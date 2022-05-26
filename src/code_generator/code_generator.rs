use std::borrow::BorrowMut;
use koopa::ir::types::{ TypeKind, Type };
use crate::optim::check_used;
use koopa::ir::values::{Binary, Return, BinaryOp, Store, Load, Branch, Jump, Call, GetElemPtr, Aggregate, GetPtr};
use lazy_static::lazy_static;
use std::sync::Mutex;
use std::cell::{Ref, RefCell};
use std::cmp::min;
use std::collections::{HashMap, HashSet, VecDeque};
use koopa::ir::entities::{Value, Program, FunctionData, ValueKind, ValueData};
use koopa::ir::Function;
use koopa::ir::ValueKind::Integer;
use crate::IntervalAnalysis;
use crate::code_generator::code_generator::StorePos::Stack;
use crate::code_generator::code_generator::StorePos::Reg;
use crate::optim::reg_alloc::RegAlloc;

pub trait GenerateAsm{
    fn generate(&self) -> String;
}
pub enum RegType{
    T(i32),
    #[warn(dead_code)]
    S(i32)
}
pub trait RegAllocator {
    fn store_type_bound(&mut self, value: Value, store_type: StoreType);
    fn get_offset_reg(&mut self, offset: i32) -> (String, i32);
    fn alloc_tmp_reg(&mut self) -> Option<i32>;
    fn free_reg(&mut self, idx: i32) -> Option<i32>;
    fn alloc_stack_space(&mut self, value: Value, size: i32);
    fn get_space(&mut self, value: Value) -> (StorePos, String);
    fn return_reg(&mut self, value: Value) -> String;
    fn borrow_reg(&mut self, value: &Value) -> (String, String);
    fn bound_stack_space(&mut self, value: &Value, offset: i32);
}
pub fn check_stmt_used(func_data: &FunctionData, value: &Value, map: &Ref<HashMap<Value,
    ValueData>>) -> bool{
    match func_data.dfg().value(value.clone()).kind(){
        ValueKind::Alloc(_) => {
            check_used(func_data, value, map)
        },
        ValueKind::Store(store) => {
            check_used(func_data, &store.dest(), map)
        }
        _ => check_used(func_data, value, map),
    }
}
pub enum StoreType{
    #[warn(dead_code)]
    Value,
    #[warn(dead_code)]
    Array,
    Point
}
pub enum StorePos{
    Reg(String),
    Stack(String)
}
struct GlobalRegAllocator {
    tmp_reg_pool: Vec<i32>,
    stack_allocation: HashMap<Value, i32>,
    reg_allocation: HashMap<Value, Option<i32>>,
    store_type: HashMap<Value, StoreType>,
    borrowed_reg: HashMap<Value, VecDeque<(RegType, i32)>>,
    have_borrowed: VecDeque<i32>,
    offset: i32,
    start_offset: i32
}
impl GlobalRegAllocator {
    fn new(bottom: i32, top: i32) -> GlobalRegAllocator {
        let mut v:Vec<i32> = Vec::new();
        for i in (bottom..top+1).rev(){
            v.push(i);
        }
        let mut queue  = VecDeque::new();
        for i in 0..12 {
            queue.push_back(i);
        }
        GlobalRegAllocator { tmp_reg_pool: v, reg_allocation: HashMap::new(), stack_allocation:
        HashMap::new(), store_type: HashMap::new() ,borrowed_reg: HashMap::new(), offset: 0 ,
            start_offset: 0, have_borrowed: queue}
    }
    fn fresh(&mut self, reg_allocation: HashMap<Value, Option<i32>>){
        // self.reg_pool is no need to fresh, because at the end of a function, all reg is free
        self.reg_allocation = reg_allocation;
        self.stack_allocation.clear();
        self.store_type.clear();
        self.offset = 0;
        self.start_offset = 0;
    }
}
impl RegAllocator for GlobalRegAllocator {
    fn store_type_bound(&mut self, value: Value, store_type: StoreType){
        self.store_type.insert(value.clone(), store_type);
    }
    // given a offset, return a string that store this offset
    // to avoid the situation offset not in (-2047, 2048)
    fn get_offset_reg(&mut self, offset: i32) -> (String, i32){
        let mut s = "".to_string();
        let reg;
        if offset >= (1 << 12){
            let div = offset / (1 << 12);
            let quo = offset % (1 << 12);
            if quo < (1 << 11) {
                let g = self.alloc_tmp_reg().unwrap();
                reg = g;
                s += &format!("\tlui t{}, {}\n", g, div);
                s += &format!("\taddi t{}, t{}, {}\n", g, g, quo);
            } else {
                let g = self.alloc_tmp_reg().unwrap();
                reg = g;
                s += &format!("\tlui t{}, {}\n", g, div + 1);
                s += &format!("\taddi t{}, t{}, {}\n", g, g, quo - (1 << 12));
            }
        } else if offset >= (1 << 11){
            let g = self.alloc_tmp_reg().unwrap();
            reg = g;
            s += &format!("\tlui t{}, {}\n", g, 1);
            s += &format!("\taddi t{}, t{}, {}\n", g, g, offset - (1 << 12));
        } else {
            let g = self.alloc_tmp_reg().unwrap();
            reg = g;
            s += &format!("\tli t{}, {}\n", g,  offset);
        }
        (s.to_string(), reg)
    }
    fn alloc_tmp_reg(&mut self) -> Option<i32> {
        if !self.tmp_reg_pool.is_empty(){
            self.tmp_reg_pool.pop()
        } else {
            None
        }
    }
    fn free_reg(&mut self, idx: i32) -> Option<i32>{
        if self.tmp_reg_pool.contains(&idx){
            unreachable!()
        }
        if idx < 0 || idx >= 7 {
            None
        } else {
            self.tmp_reg_pool.push(idx);
            Some(idx)
        }
    }
    fn alloc_stack_space(&mut self, value: Value, size: i32){
        self.stack_allocation.insert(value, self.offset);
        self.offset += size;
    }
    /// if value store in reg, return the reg name
    /// if value store in stack, before we load it to the reg
    ///     1. if temp reg not full, alloc a temp reg for it
    ///     2. else alloc a memory for any S_n reg, then move value to S_n, after borrowing,
    ///        store value back to memory, and recover S_n
    fn get_space(&mut self, value: Value) -> (StorePos, String){
        if let Some(reg) = self.reg_allocation.get(&value).unwrap(){
            (Reg(format!("s{}", *reg)), "".to_string())
        } else if let Some(offset) = self.stack_allocation.get(&value){
            let (load_string, reg_idx) = self.get_offset_reg(*offset);
            let (idx, store_string) = self.borrow_reg(&value);
            let now = store_string + &load_string + &format!("\tadd t{}, sp, t{}\n", reg_idx,
                                                             reg_idx) +
                &format!("\tlw {}, 0(t{})\n", idx, reg_idx);
            self.free_reg(reg_idx);
            (Stack(format!("{}", idx)), now)
        } else if let None = self.reg_allocation.get(&value).unwrap(){ //这是为了解决第一次存储reg spill的数据
            self.alloc_stack_space(value, 4);
            self.get_space(value) // this branch will choose Some(offset)
        } else {
            unreachable!()
        }
    }
    /// after return reg, make sure last stored reg value is wrote back to reg, return the load code
    /// if the value doesn't borrow reg, do nothing
    fn return_reg(&mut self, value: Value) -> String{
        if let Some(deque) = self.borrowed_reg.get_mut(&value){
            if let Some((RegType::T(idx), _)) = deque.pop_front(){
                let store_offset  = self.stack_allocation.get(&value).unwrap();
                let (store_before, store_idx) = self.get_offset_reg(*store_offset);
                let now = store_before + &format!("\tadd t{}, sp, t{}\n\tsw t{}, 0(t{})\n",
                                                          store_idx, store_idx, idx, store_idx);
                self.free_reg(idx);
                self.free_reg(store_idx);
                now
            } else {
                unreachable!()
            }
        } else {
            "".to_string()
        }
    }
    /// before borrow reg, make sure before value is stored correctly, return the store code, and
    /// the reg idx
    fn borrow_reg(&mut self, value: &Value) -> (String, String){
        let idx = self.alloc_tmp_reg().unwrap();
        let borrowed_reg = format!("t{}", idx);
        let now = "".to_string();
        if let Some(queue) = self.borrowed_reg.get_mut(value){
            queue.push_front((RegType::T(idx), 0));
        } else {
            let mut queue = VecDeque::new();
            queue.push_front((RegType::T(idx), 0));
            self.borrowed_reg.insert(value.clone(), queue);
        }
        (borrowed_reg, now)
    }
    fn bound_stack_space(&mut self, value: &Value, offset: i32) {
        self.stack_allocation.insert(value.clone(), offset);
    }
}
lazy_static!{
    static ref GLOBAL_REG_ALLOCATOR: Mutex<RefCell<GlobalRegAllocator >> = Mutex::new(RefCell::new
        (GlobalRegAllocator::new(0, 6)));
    static ref GLOBAL_FUNCTION_NAME: Mutex<HashMap<Function, String>> = Mutex::new(HashMap::new());
    static ref NOW_SP_SIZE: Mutex<RefCell<i32>> = Mutex::new(RefCell::new(0));
    static ref GLOBAL_FUNCTION_TYPE: Mutex<HashMap<Function, String>> = Mutex::new
    (HashMap::new());
    static ref GLOBAL_VARIABLE: Mutex<HashMap<Value, String>> = Mutex::new
    (HashMap::new());
    static ref GLOBAL_VARIABLE_TYPE: Mutex<HashMap<Value, (String, i32)>> = Mutex::new
    (HashMap::new());
}
fn gen_agg_init(agg: &Aggregate, values: HashMap<Value, ValueData>) -> String{
    let mut s = "".to_string();
    for value in agg.elems(){
        if let Integer(ii) = values.get(value).unwrap().kind(){
            if ii.value() == 0{
                s += &format!("\t.zero 4\n");
            } else {
                s += &format!("\t.word {}\n", ii.value());
            }
        } else if let ValueKind::Aggregate(agg1) = values.get(value).unwrap().kind(){
            s += &gen_agg_init(&agg1, values.clone());
        } else {
            unreachable!();
        }
    }
    s
}
impl GenerateAsm for Program{
    fn generate(&self) -> String {
        let mut s = "".to_string();
        let mut m = GLOBAL_FUNCTION_NAME.lock().unwrap();
        let mut t = GLOBAL_FUNCTION_TYPE.lock().unwrap();
        let global_values = self.borrow_values();
        let global_values_iter = global_values.iter();
        s += "\t.data\n";
        for (val,val_data) in global_values_iter {
            let mut var = GLOBAL_VARIABLE.lock().unwrap();
            let mut var_type = GLOBAL_VARIABLE_TYPE.lock().unwrap();
            if let Some(name) = val_data.name(){
                if let TypeKind::Pointer(p) = val_data.ty().kind(){
                    if let TypeKind::Array(ty, _) = p.kind(){
                        var_type.insert(val.clone(), (val_data.ty().to_string(), ty.size() as i32));
                    } else {
                        var_type.insert(val.clone(), (val_data.ty().to_string(), val_data.ty().size() as i32));
                    }
                } else {
                    var_type.insert(val.clone(), (val_data.ty().to_string(), val_data.ty().size() as i32));
                }
                var.insert(val.clone(), name.to_string());
                s += &format!("\t.global {}\n",name[1..].to_string());
                s += &format!("{}:\n",name[1..].to_string());
                if let ValueKind::GlobalAlloc(g) = val_data.kind(){
                    let init_value = global_values.get(&g.init());
                    if let Some(i) = init_value{
                        if let Integer(ii) = i.kind(){
                            if ii.value() == 0{
                                s += &format!("\t.zero 4\n");
                            } else {
                                s += &format!("\t.word {}\n", ii.value());
                            }
                        } else if let ValueKind::Aggregate(agg) = i.kind(){
                            s += &gen_agg_init(agg, global_values.clone());
                        } else if let ValueKind::ZeroInit(_) = i.kind(){
                            if let TypeKind::Array(arr_type, arr_size) = i.ty().kind(){
                                s += &format!("\t.zero {}\n", arr_type.size() * *arr_size);
                            } else {
                                s += &format!("\t.zero {}\n", i.ty().size());
                            }
                        } else {
                            unreachable!()
                        }
                    } else {
                        unreachable!()
                    }
                } else {
                    unreachable!()
                }
            }
        }
        let interval = self.get_interval();
        let mut alloc_result = self.reg_alloc(interval);
        for &func in self.func_layout(){
            m.insert(func.clone(), self.func(func).name().to_string());
            if let TypeKind::Function(_, a) = self.func(func).ty().kind(){
                if let TypeKind::Unit = a.kind(){
                    t.insert(func.clone(), "void".to_string());
                } else if let TypeKind::Int32 = a.kind(){
                    t.insert(func.clone(), "i32".to_string());
                }
            }
        }
        drop(m);
        drop(t);
        for &func in self.func_layout(){
            let tmp = &self.func(func).name().to_string()[1..];
            if is_lib(tmp){
                continue;
            }
            {
                let mut m = GLOBAL_REG_ALLOCATOR.lock().unwrap();
                let g = m.borrow_mut().get_mut();
                let alloc = alloc_result.remove(&func).unwrap();

                g.fresh(alloc);
            }
            let mut head = "\t.text\n".to_string();
            let mut func_def = "".to_string();
            head += &format!("\t.global {}\n", tmp);
            func_def += &self.func(func).generate(&global_values);
            s += &(head + &func_def);
        }
        s
    }
}
fn is_lib(true_name: &str) -> bool{
    if true_name == "getint" || true_name == "getch" || true_name == "getarray" ||
        true_name == "putint" || true_name == "putch" || true_name == "putarray" || true_name ==
        "starttime" ||
        true_name == "stoptime"{
        true
    } else {
        false
    }
}
enum Caller{
    Caller((i32, i32, HashSet<i32>)),
    Nocall((i32, i32, HashSet<i32>))
}
fn calculate_and_allocate_space(this: &FunctionData, reg_allocator: &HashMap<Value, Option<i32>>) ->
                                                                                           Caller{
    let mut bits:i32 = 0;
    let mut arg_count_max = 0;
    let mut caller: bool = false;
    let mut vec = HashSet::with_capacity(12);
    reg_allocator.iter().fold((&mut bits, &mut vec), |(sum, vec), (val, opt)|{
        if let Some(idx) = opt{
            vec.insert(*idx);
        } else {
            *sum += 4;
        }
        (sum, vec)
    });
    for (_, node) in this.layout().bbs(){
        for &inst in node.insts().keys(){
            let value_data = this.dfg().value(inst);
            let i32_type = Type::get_i32();
            if !value_data.ty().is_unit(){
                if let TypeKind::Pointer(b) = value_data.ty().kind(){
                     if *b != i32_type {
                        if let ValueKind::Alloc(_) = value_data.kind(){
                            if let TypeKind::Array(arr_type, arr_size) = b.kind(){
                                bits += (*arr_size as i32) * arr_type.size() as i32;
                            }
                        }
                    }
                } else if let ValueKind::GetElemPtr(_) = value_data.kind(){
                    bits += 4;
                }
            }
            if let ValueKind::Call(call) = value_data.kind(){
                let  arg_vec = call.args();
                if arg_vec.len() as i32 - 8 > arg_count_max{
                    arg_count_max = arg_vec.len() as i32 - 8 ;
                }
                caller = true;
            }
        }
    }
    bits += vec.len() as i32 * 4;
    if caller{
        let mut m = NOW_SP_SIZE.lock().unwrap();
        let sp = ((bits + 4 + (arg_count_max * 4) as i32 + 15) / 16) as i32 * 16;
        *m.get_mut() = sp;
        Caller::Caller((sp, arg_count_max as i32 + vec.len() as i32, vec))
    } else {
        let mut m = NOW_SP_SIZE.lock().unwrap();
        let sp = ((bits + (arg_count_max * 4) as i32 + 15) / 16) as i32 * 16;
        *m.get_mut() = sp;
        Caller::Nocall((sp, arg_count_max as i32 + vec.len() as i32, vec))
    }
}
fn save_and_recover_reg(set: &HashSet<i32>) -> (String, String){
    let mut s = ("".to_string(), "".to_string());
    let mut sp = 0;
    set.iter().fold((&mut s.0, &mut s.1), |(save, recover), idx|{
        *save += &format!("\tsw s{} ,{}(sp)\n", idx, sp);
        *recover = format!("\tlw s{}, {}(sp)\n", idx, sp) + recover;
        sp += 4;
        (save, recover)
    });
    s
}
trait GenerateAsmFunc{
    fn generate(&self, global_var: &Ref<HashMap<Value, ValueData>>) -> String;
}
impl GenerateAsmFunc for FunctionData{
    fn generate(&self, global_var: &Ref<HashMap<Value, ValueData>>) -> String{
        let mut s = "".to_string();
        s += &format!("{}:\n", &self.name().to_string()[1..]);
        let caller;
        {
            let mut k = GLOBAL_REG_ALLOCATOR.lock().unwrap();
            let m = k.get_mut();
            caller = calculate_and_allocate_space(self, &m.reg_allocation);
        }
        let sp_len;
        let save_and_recover;
        if let Caller::Caller((sp, offset, set)) = &caller{
            let mut k = GLOBAL_REG_ALLOCATOR.lock().unwrap();
            let mut m = k.get_mut();
            save_and_recover = save_and_recover_reg(set);
            sp_len = sp;
            let (ss, reg) = m.get_offset_reg(*sp);
            s += &(ss + &format!("\tsub sp, sp, t{}\n", reg));
            m.free_reg(reg);
            let (ss, reg) = m.get_offset_reg(sp - 4);
            s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg) +&format!("\tsw ra, 0(t{})\n", reg));
            m.free_reg(reg);
            m.offset = offset * 4;
            m.start_offset = offset * 4;
        } else if let Caller::Nocall((sp, offset, set)) = &caller{
            save_and_recover = save_and_recover_reg(set);
            let mut k = GLOBAL_REG_ALLOCATOR.lock().unwrap();
            let mut m = k.get_mut();
            sp_len = sp;
            let (ss, reg) = m.get_offset_reg(*sp);
            s += &(ss + &format!("\tsub sp, sp, t{}\n", reg));
            m.free_reg(reg);
            m.offset = offset * 4;
            m.start_offset = offset * 4;
        } else {
            unreachable!()
        }
        s += &save_and_recover.0;
        for (&bb, node) in self.layout().bbs(){
            if let Some(data) = self.dfg().bbs().get(&bb){
                if let Some(a) = &data.name(){
                    let k = a.to_string();
                    let len = k.len();
                    let kk = k[1..len].to_string();
                    if a == "%entry"{
                        s += ""
                    } else {
                        s += &format!("{}:\n", kk);
                    }
                }
            }
            for &inst in node.insts().keys(){
                let value_data = self.dfg().value(inst);
                match value_data.kind(){
                    ValueKind::Return(ret) => {
                        s += "# return gen\n";
                        self.return_gen(&mut s, ret);
                        s += "# return end\n\n"
                    }
                    ValueKind::Binary(bin) => {
                        s += "# bin gen\n";
                        if check_stmt_used(self, &inst, global_var){
                            self.bin_gen(&mut s, bin, inst);
                        }
                        s += "# bin gen end\n\n";
                    }
                    ValueKind::Store(store) => {
                        s += "# store gen \n";
                        if check_stmt_used(self, &inst, global_var){
                            self.store_gen(&mut s, store,  global_var);
                        }
                        s += "# store gen end\n\n";
                    }
                    ValueKind::Load(load) => {
                        s += "# load gen \n";
                        self.load_gen(&mut s, load, inst);
                        s += "# load gen end\n\n";
                    }
                    ValueKind::Alloc(_) => {
                        s += "# alloc gen\n";
                        if check_stmt_used(self, &inst, global_var){
                            self.alloc_gen(inst);
                        }
                        s += "# alloc gen end\n\n";
                    }
                    ValueKind::Branch(branch) => {
                        s += "# branch gen\n";
                        self.branch_gen(&mut s, branch);
                        s += "# branch gen end\n\n";
                    }
                    ValueKind::Jump(jump) => {
                        s += "# jump gen\n";
                        self.jump_gen(&mut s, jump);
                        s += "# jump gen\n\n";
                    }
                    ValueKind::Call(call) => {
                        s += "# call gen\n";
                        self.call_gen(&mut s, call, inst);
                        s += "# call gen end\n\n";
                    }
                    ValueKind::GetElemPtr(get_elem_ptr) => {
                        s += "# get elem ptr gen\n";
                        self.get_elem_ptr_gen(&mut s, get_elem_ptr, inst);
                        s += "# get elem ptr gen end\n\n";
                    }
                    ValueKind::GetPtr(get_ptr) => {
                        s += "# get ptr\n";
                        self.get_ptr(&mut s, get_ptr, inst);
                        s += "# get ptr end\n";
                    }
                    _ => unreachable!(),
                }
            }
            let name = self.name();
            let end_name = format!("%end_{}", name[1..].to_string());
            if let Some(data) = self.dfg().bbs().get(&bb){
                if let Some(a) = &data.name(){
                    if *a == end_name{
                        s += &save_and_recover.1;
                        if let Caller::Caller((sp, _, _)) = caller{
                            let mut k = GLOBAL_REG_ALLOCATOR.lock().unwrap();
                            let m = k.get_mut();
                            let (ss, reg) = m.get_offset_reg(sp - 4);
                            s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg) + &format!("\tlw ra, 0(t{})\n", reg));
                            m.free_reg(reg);
                        }
                        let mut k = GLOBAL_REG_ALLOCATOR.lock().unwrap();
                        let m = k.get_mut();
                        let (ss, reg) = m.get_offset_reg(*sp_len);
                        s += &(ss + &format!("\tadd sp, sp, t{}\n",reg));
                        m.free_reg(reg);
                        s += &format!("\tret\n\n");
                    }
                }
            }
        }
        s
    }
}

trait SplitGen {
    fn return_gen(&self, s: &mut String, ret: &Return);
    fn bin_gen(&self, s: &mut String, bin: &Binary, value: Value);
    fn alloc_gen(&self, value: Value);
    fn load_gen(&self, s: &mut String, alloc: &Load, value: Value);
    fn store_gen(&self, s: &mut String, alloc: &Store, global_variable_ref:
    &Ref<HashMap<Value, ValueData>>);
    fn branch_gen(&self, s: &mut String, branch: &Branch);
    fn jump_gen(&self, s: &mut String, jump: &Jump);
    fn call_gen(&self, s: &mut String, call: &Call, value: Value);
    fn get_elem_ptr_gen(&self, s: &mut String, get_elem_ptr: &GetElemPtr, value: Value);
    fn get_ptr(&self, s: &mut String, get_ptr: &GetPtr, value: Value);
}
impl SplitGen for FunctionData {
    fn return_gen(&self, s: &mut String, ret: &Return) {
        if let Some(val) = ret.value() {
            let a = self.dfg().value(val);
            let b = a.kind();
            match b {
                Integer(i) =>
                    *s += &format!("\tli a0, {}\n", i.value()),
                _ =>{
                    let mut g = GLOBAL_REG_ALLOCATOR.lock().unwrap();
                    let r = g.borrow_mut().get_mut();
                    let (idx, before) = r.get_space(val);
                    let mut recover_idx = false;
                    if let Stack(reg_name) = idx{
                        *s += &before;
                        *s += &(format!("\tmv a0, {}\n", reg_name));
                        recover_idx = true;
                    } else if let Reg(reg_name) = idx{
                        *s += &(before + &(format!("\tmv a0, {}\n", reg_name)) + &r.return_reg
                        (val));
                    }
                    if recover_idx{
                        *s += &r.return_reg(val);
                    }
                }
            }
        }
    }
    fn bin_gen(&self, s: &mut String, bin: &Binary, value: Value) {
        let r_value = bin.rhs();
        let l_value = bin.lhs();
        let r_s:String;
        let l_s:String;
        let op = bin.op();
        let bin_operation:String;
        let idx;
        let mut g = GLOBAL_REG_ALLOCATOR.lock().unwrap();
        let r = g.borrow_mut().get_mut();
        r.store_type_bound(value, StoreType::Value);
        let mut tmp_r:i32 = 0;
        let mut tmp_l:i32 = 0;
        let mut r_is_integer = false;
        let mut l_is_integer = false;
        let mut recover_r = false;
        let mut recover_l = false;
        let mut recover_i = false;
        if let Integer(i) = self.dfg().value(r_value).kind(){
            if i.value() == 0 {
                r_s = format!("x0");
            } else {
                tmp_r = r.alloc_tmp_reg().unwrap();
                *s += &format!("\tli t{}, {}\n", tmp_r,i.value());
                r_s = format!("t{}", tmp_r);
                r_is_integer = true;
            }
        } else {
            let (idx, before) = r.get_space(r_value);
            if let Reg(reg_name) = idx{
                r_s = reg_name;
            } else if let Stack(reg_name) = idx{
                recover_r = true;
                *s += &before;
                r_s = reg_name;
            } else {
                unreachable!()
            }
        }
        if let Integer(i) = self.dfg().value(l_value).kind(){
            if i.value() == 0{
                l_s = format!("x0");
            } else {
                tmp_l = r.alloc_tmp_reg().unwrap();
                *s += &format!("\tli t{}, {}\n", tmp_l, i.value());
                l_s = format!("t{}", tmp_l);
                l_is_integer = true;
            }
        } else {
            let (idx, before) = r.get_space(l_value);
            if let Reg(reg_name) = idx{
                l_s = reg_name;
            } else if let Stack(reg_name) = idx{
                recover_l = true;
                *s += &before;
                l_s = reg_name;
            } else {
                unreachable!()
            }
        }
        let (reg, before) = r.get_space(value);
        if let Reg(reg_name) = reg{
            idx = reg_name;
        } else if let Stack(reg_name) = reg{
            recover_i = true;
            idx = reg_name;
            *s += &before;
        } else {
            unreachable!()
        }
        match op{
            BinaryOp::Add => {
                bin_operation = "add".to_string();
                *s += &format!("\t{} {}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Sub => {
                bin_operation = "sub".to_string();
                *s += &format!("\t{} {}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Mul => {
                bin_operation = "mul".to_string();
                *s += &format!("\t{} {}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Div => {
                bin_operation = "div".to_string();
                *s += &format!("\t{} {}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Mod => {
                bin_operation = "rem".to_string();
                *s += &format!("\t{} {}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Eq => {
                let tmp = r.alloc_tmp_reg().unwrap();
                *s += &format!("\txor t{}, {}, {}\n", tmp, l_s, r_s);
                *s += &format!("\tseqz {}, t{}\n", idx, tmp);
                r.free_reg(tmp);
            },
            BinaryOp::And => {
                bin_operation = "and".to_string();
                *s += &format!("\t{} {}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Or => {
                bin_operation = "or".to_string();
                *s += &format!("\t{} {}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::NotEq => {
                let tmp = r.alloc_tmp_reg().unwrap();
                *s += &format!("\txor t{}, {}, {}\n", tmp, l_s, r_s);
                *s += &format!("\tsnez {}, t{}\n", idx, tmp);
                r.free_reg(tmp);
            },
            BinaryOp::Le => {
                bin_operation = "slt".to_string();
                let tmp = r.alloc_tmp_reg().unwrap();
                let tmp1 = r.alloc_tmp_reg().unwrap();
                *s += &format!("\txor t{}, {}, {}\n", tmp, l_s, r_s);
                *s += &format!("\tseqz {}, t{}\n", idx, tmp);
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, tmp1, l_s, r_s);
                *s += &format!("\tor {}, {}, t{}\n", idx, idx, tmp1);
                r.free_reg(tmp);
                r.free_reg(tmp1);
            },
            BinaryOp::Lt => {
                bin_operation = "slt".to_string();
                *s += &format!("\t{} {}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Gt => {
                bin_operation = "slt".to_string();
                *s += &format!("\t{} {}, {}, {}\n", bin_operation, idx, r_s, l_s);
            },
            BinaryOp::Ge =>{
                bin_operation = "slt".to_string();
                let tmp = r.alloc_tmp_reg().unwrap();
                let tmp1 = r.alloc_tmp_reg().unwrap();
                *s += &format!("\txor t{}, {}, {}\n", tmp, l_s, r_s);
                *s += &format!("\tseqz {}, t{}\n", idx, tmp);
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, tmp1, r_s, l_s);
                *s += &format!("\tor {}, {}, t{}\n", idx, idx, tmp1);
                r.free_reg(tmp);
                r.free_reg(tmp1);
            }
            _ => bin_operation = "".to_string()
        }
        if recover_i{
            *s += &r.return_reg(value);
        }
        if recover_l{
            *s += &r.return_reg(l_value);
        }
        if recover_r{
            *s += &r.return_reg(r_value);
        }

        if l_is_integer{
            r.free_reg(tmp_l);
        }
        if r_is_integer{
            r.free_reg(tmp_r);
        }
    }
    fn alloc_gen(&self, value: Value) {
        let mut m = GLOBAL_REG_ALLOCATOR.lock().unwrap();
        let g = m.get_mut();
        let size ;
        if let TypeKind::Pointer(type_id)= self.dfg().value(value).ty().kind(){
            let i32_type = Type::get_i32();
            if i32_type == *type_id{
                size = 4;
                g.store_type_bound(value, StoreType::Value);
            } else {
                if let TypeKind::Array(arr_type, arr_size) = type_id.kind(){
                    size = *arr_size as i32 * arr_type.size() as i32;
                    g.store_type_bound(value, StoreType::Value);
                } else if let TypeKind::Pointer(_) = type_id.kind(){
                    size = type_id.size() as i32;
                    g.store_type_bound(value, StoreType::Value);
                } else {
                    unreachable!();
                }
            }
            // if value is array or i32 or ptr which reg spill we should bound a value to it
            let tmp = g.reg_allocation.get(&value);
            if let None = tmp{
                g.alloc_stack_space(value, size);
            }
        } else {
            unreachable!();
        }
    }
    fn load_gen(&self, s: &mut String, load: &Load, value: Value) {
        let src_value = load.src();
        let var = GLOBAL_VARIABLE.lock().unwrap();
        let reg_idx;
        let src_reg_idx;
        let mut m = GLOBAL_REG_ALLOCATOR.lock().unwrap();
        let g = m.get_mut();
        let mut recover_i = false;
        let mut recover_s = false;
        if !self.dfg().value(value).used_by().is_empty(){
            let (reg, before) = g.get_space(value);
            if let Reg(reg_name) = reg{
                reg_idx = reg_name;
            } else if let Stack(reg_name) = reg{
                recover_i = true;
                *s += &before;
                reg_idx = reg_name;
            } else {
                unreachable!()
            }
        } else {
            return;
        }
        if let Some(name) = var.get(&src_value){
            let tmp_reg = g.alloc_tmp_reg().unwrap();
            *s += &format!("\tla t{}, {}\n\tlw {}, 0(t{})\n",tmp_reg, name[1..].to_string(),
                           reg_idx, tmp_reg);
            g.free_reg(tmp_reg);
        } else {
            let (src_reg, src_before) = g.get_space(src_value);
            if let Reg(reg_name) = src_reg{
                src_reg_idx = reg_name;
            } else if let Stack(reg_name) = src_reg{
                recover_s = true;
                *s += &src_before;
                src_reg_idx = reg_name;
            } else {
                unreachable!()
            }
            if let ValueKind::GetPtr(_) = self.dfg().value(src_value).kind(){
                *s += &format!("\tlw {}, 0({})\n", reg_idx, src_reg_idx);
            } else if let ValueKind::GetElemPtr(_) = self.dfg().value(src_value).kind(){
                *s += &format!("\tlw {}, 0({})\n", reg_idx, src_reg_idx);
            } else {
                *s += &format!("\tmv {}, {}\n", reg_idx, src_reg_idx);
            }
        }
        if recover_i{
            *s += &g.return_reg(value);
        }
        if recover_s{
            *s += &g.return_reg(load.src());
        }
    }
    fn store_gen(&self, s: &mut String, store: &Store, global_variable_ref:
    &Ref<HashMap<Value, ValueData>>) {
        let value = store.value();
        let dest = store.dest();
        let var = GLOBAL_VARIABLE.lock().unwrap();
        let mut m = GLOBAL_REG_ALLOCATOR.lock().unwrap();
        let g = m.get_mut();
        let value_reg;
        let dest_reg;
        let mut recover_value = false;
        let mut recover_dest = false;
        if let Some(name) = var.get(&dest){
            if let Integer(i) = self.dfg().value(value).kind(){
                let tmp_reg = g.alloc_tmp_reg().unwrap();
                let reg_idx = g.alloc_tmp_reg().unwrap();
                *s += &(format!("\tli t{}, {}\n",reg_idx, i.value()) + &format!("\tla t{}, \
                {}\n\tsw t{}, 0(t{})\n", tmp_reg, name[1..].to_string(), reg_idx, tmp_reg));
                g.free_reg(tmp_reg);
                g.free_reg(reg_idx);
            } else {
                let (src_reg_pos, src_begin) = g.get_space(value);
                if let Reg(reg_name) = src_reg_pos{
                    value_reg = reg_name;
                } else if let Stack(reg_name) = src_reg_pos{
                    value_reg = reg_name;
                    *s += &src_begin;
                    recover_value = true;
                } else {
                    unreachable!()
                }
                let tmp = g.alloc_tmp_reg().unwrap();
                *s += &format!("\tla t{}, {}\n",tmp, name[1..].to_string());
                *s += &format!("\tsw {}, 0(t{})\n",value_reg, tmp);
                g.free_reg(tmp);
            }
        } else if check_used(self, &dest, global_variable_ref){
            if let (dest_reg_pos, dest_before) = g.get_space(dest){
                if let Stack(reg_name) = dest_reg_pos{
                    dest_reg = reg_name;
                    *s += &dest_before;
                    recover_dest = true;
                } else if let Reg(reg_name) = dest_reg_pos{
                    dest_reg = reg_name;
                } else {
                    unreachable!()
                }
                if let Integer(i) = self.dfg().value(value).kind(){
                    let tmp = g.alloc_tmp_reg().unwrap();
                    if let ValueKind::GetElemPtr(_) = self.dfg().value(dest).kind(){
                        *s += &format!("\tli t{}, {}\n\tsw t{}, 0({})\n", tmp, i.value(), tmp,
                                       dest_reg);
                    } else if let ValueKind::GetPtr(_) = self.dfg().value(dest).kind(){
                        *s += &format!("\tli t{}, {}\n\tsw t{}, 0({})\n", tmp, i.value(), tmp,
                                       dest_reg);
                    } else {
                        *s += &format!("\tli t{}, {}\n\tmv {}, t{}\n", tmp, i.value(), dest_reg, tmp);
                    }
                    g.free_reg(tmp);
                } else {
                    if let ValueKind::FuncArgRef(func_arg_ref) = self.dfg().value(value).kind() {
                        if func_arg_ref.index() < 8 {
                            *s += &(format!("\tmv {}, a{}\n", dest_reg, func_arg_ref.index()));
                        } else {
                            let mut k = NOW_SP_SIZE.lock().unwrap();
                            let sp_size = k.get_mut();
                            let src_offset = *sp_size + 4 * (func_arg_ref.index() as i32 - 8);
                            let (src_ss, src_reg) = g.get_offset_reg(src_offset);
                            *s += &(src_ss + &format!("\tadd t{}, sp, t{}\n", src_reg, src_reg) +
                                &format!("\tlw {}, 0(t{})\n", dest_reg, src_reg));
                            g.free_reg(src_reg);
                        }
                    } else if let (src_reg_pos, src_begin) = g.get_space(value){
                        if let Reg(reg_name) = src_reg_pos{
                            value_reg = reg_name;
                        } else if let Stack(reg_name) = src_reg_pos{
                            value_reg = reg_name;
                            *s += &src_begin;
                            recover_value = true;
                        } else {
                            unreachable!()
                        }
                        if let ValueKind::GetElemPtr(_) = self.dfg().value(dest).kind(){
                            *s += &format!("\tsw {}, 0({})\n",value_reg, dest_reg);
                        } else if let ValueKind::GetPtr(_) = self.dfg().value(dest).kind(){
                            *s += &format!("\tsw {}, 0({})\n",value_reg, dest_reg);
                        } else {
                            *s += &format!("\tmv {}, {}\n",dest_reg, value_reg);
                        }
                    }
                }
            }
        }
        if recover_value{
            *s += &g.return_reg(value);
        }
        if recover_dest{
            *s += &g.return_reg(dest);
        }
    }
    fn branch_gen(&self, s: &mut String, branch: &Branch) {
        let cond = branch.cond();
        let then_branch = branch.true_bb();
        let else_branch = branch.false_bb();
        let mut k = GLOBAL_REG_ALLOCATOR.lock().unwrap();
        let g = k.get_mut();
        let reg_idx ;
        let mut recover_cond = false;
        if let Integer(i) = self.dfg().value(cond).kind(){
            let reg_idx_i32 = g.borrow_mut().alloc_tmp_reg().unwrap();
            reg_idx = format!("t{}", reg_idx_i32);
            *s += &format!("\tli {}, {}\n", reg_idx, i.value());
            g.borrow_mut().free_reg(reg_idx_i32);
        } else if let (reg, before) = g.get_space(cond){
            if let Stack(reg_name) = reg{
                reg_idx = reg_name;
                recover_cond = true;
                *s += &before;
            } else if let Reg(reg_name) = reg{
                reg_idx = reg_name;
            } else {
                unreachable!()
            }
        } else {
            unreachable!()
        }
        if let Some(then_data) = self.dfg().bbs().get(&then_branch){
            if let Some(then_name) = then_data.name(){
                let kk = then_name.to_string()[1..then_name.len()].to_string();
                *s += &format!("\tbnez {}, {}\n", reg_idx, kk);
            }
        } else {
            unreachable!()
        }
        if let Some(else_data) = self.dfg().bbs().get(&else_branch){
            if let Some(else_name) = else_data.name(){
                let kk = else_name.to_string()[1..else_name.len()].to_string();
                *s += &format!("\tj {}\n\n", kk);
            }
        } else {
            unreachable!()
        }
        if recover_cond{
            *s += &g.return_reg(cond);
        }
    }
    fn jump_gen(&self, s: &mut String, jump: &Jump) {
        let target = jump.target();
        if let Some(bd) = self.dfg().bbs().get(&target){
            if let Some(name) = bd.name(){
                let kk = name.to_string()[1..name.len()].to_string();
                *s += &format!("\tj {}\n\n", kk);
            }
        }
    }
    fn call_gen(&self, s: &mut String, call: &Call, value: Value) {
        let arg_vec = call.args();
        let mut len = arg_vec.len() as i32;
        let mut m = GLOBAL_REG_ALLOCATOR.lock().unwrap();
        let g = m.get_mut();
        for i   in 0..min(len, 8){
            let idx = i as usize;
            if let Integer(int) = self.dfg().value(arg_vec[idx]).kind(){
                *s += &format!("\tli a{}, {}\n", i, int.value());
            } else {
                let (arg_pos, beign_arg) = g.get_space(arg_vec[idx]);
                let mut recover_arg = false;
                let reg_idx;
                if let Reg(reg_name) = arg_pos{
                    reg_idx = reg_name;
                } else if let Stack(reg_name) = arg_pos{
                    reg_idx = reg_name;
                    *s += &beign_arg;
                    recover_arg = true;
                } else{
                    unreachable!()
                }
                *s += &(format!("\tmv a{}, {}\n", i, reg_idx));
                if recover_arg{
                    *s += &g.return_reg(arg_vec[idx]);
                }
            }
        }
        let mut idx = 8;
        while len - 8 > 0{
            let value = arg_vec[idx];
            if let Integer(i) = self.dfg().value(value).kind(){
                let tmp = g.alloc_tmp_reg().unwrap();
                let offset = ((idx - 8) * 4) as i32;
                let (ss, reg) = g.get_offset_reg(offset);
                *s += &(ss +&format!("\tadd t{}, sp, t{}\n",reg, reg)+ &(format!("\tli t{}, {}\n",tmp , i.value()) +  &format!("\tsw t{}, 0(t{})\
                \n", tmp,  reg)));
                g.free_reg(reg);
                g.free_reg(tmp);
            } else {
                let (arg_pos, begin_pos) = g.get_space(value);
                let reg_idx;
                let mut recover_arg = false;
                if let Stack(reg_name) = arg_pos{
                    reg_idx = reg_name;
                    *s += &begin_pos;
                    recover_arg = true;
                } else if let Reg(reg_name) = arg_pos{
                    reg_idx = reg_name;
                } else {
                    unreachable!()
                }
                let offset = ((idx - 8) * 4) as i32;
                let (ss, reg) = g.get_offset_reg(offset);
                *s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tsw {}, 0(t{})\n", reg_idx, reg));
                if recover_arg{
                    *s += &g.return_reg(value);
                }
                g.free_reg(reg);
            }
            len = len - 1;
            idx = idx + 1;
        }
        let m = GLOBAL_FUNCTION_NAME.lock().unwrap();
        *s += &format!("\tcall {}\n", m.get(&call.callee()).unwrap()[1..].to_string());
        let t = GLOBAL_FUNCTION_TYPE.lock().unwrap();
        let a = t.get(&call.callee()).unwrap();
        if a == "i32" && !self.dfg().value(value).used_by().is_empty(){
            let (rst_idx, rst_begin) = g.get_space(value);
            let reg;
            let mut recover_rst = false;
            if let Stack(reg_name) = rst_idx{
                reg = reg_name;
                *s += &rst_begin;
                recover_rst = true;
            } else if let Reg(reg_name) = rst_idx{
                reg = reg_name;
            } else {
                unreachable!()
            }
            g.store_type_bound(value, StoreType::Value);
            *s += &(format!("\tmv {}, a0\n", reg));
            if recover_rst{
                *s += &g.return_reg(value);
            }
        }
    }
    fn get_elem_ptr_gen(&self, s: &mut String, get_elem_ptr: &GetElemPtr, value: Value){
        let src = get_elem_ptr.src();
        let idx = get_elem_ptr.index();
        let idx_reg;
        let src_reg;
        let mut tmp_src_reg = -1;
        let mut tmp_idx_reg = -1;
        let mut m = GLOBAL_REG_ALLOCATOR.lock().unwrap();
        let global_var = GLOBAL_VARIABLE.lock().unwrap();
        let g = m.get_mut();
        let mut ty_size = 0;
        let mut recover_src = false;
        g.store_type_bound(value, StoreType::Point);
        let var_type = GLOBAL_VARIABLE_TYPE.lock().unwrap();
        if let Some((global_var, size)) = var_type.get(&src){
            if  global_var.as_bytes()[0] == b'*'{
                ty_size = *size;
            }
        } else {
            if let TypeKind::Pointer(p) = self.dfg().value(src).ty().kind(){
                if let TypeKind::Array(ty, _) = p.kind(){
                    ty_size = ty.size() as i32;
                }
            }
        }
        let mut recover_idx = false;
        if let Integer(i) =  self.dfg().value(idx).kind(){
            tmp_idx_reg = g.alloc_tmp_reg().unwrap();
            idx_reg = format!("t{}", tmp_idx_reg);
            *s += &format!("\tli {}, {}\n",idx_reg, i.value());
        } else{
            let (idx_pos, begin_idx) = g.get_space(idx);
            if let Reg(reg_name) = idx_pos{
                idx_reg = reg_name;
            } else if let Stack(reg_name) = idx_pos{
                idx_reg = reg_name;
                recover_idx = true;
                *s += &begin_idx;
            } else {
                unreachable!()
            }
        }
        let mut reg_out = -1;
        if let Some(k) = global_var.get(&src){
            tmp_src_reg = g.alloc_tmp_reg().unwrap();
            src_reg = format!("t{}", tmp_src_reg);
            *s += &format!("\tla {}, {}\n",src_reg, k[1..].to_string());
        }else if let ValueKind::GetElemPtr(_) = &self.dfg().value(src).kind() {
            let (src_pos, begin_src) = g.get_space(src.clone());
            if let Reg(reg_name) = src_pos {
                src_reg = reg_name;
            } else if let Stack(reg_name) = src_pos {
                src_reg = reg_name;
                recover_src = true;
                *s += &begin_src;
            } else {
                unreachable!()
            }
        }else if let ValueKind::GetPtr(_) = &self.dfg().value(src).kind() {
            let (src_pos, begin_src) = g.get_space(src.clone());
            if let Reg(reg_name) = src_pos {
                src_reg = reg_name;
            } else if let Stack(reg_name) = src_pos {
                src_reg = reg_name;
                recover_src = true;
                *s += &begin_src;
            } else {
                unreachable!()
            }
        } else if let Some(offset) =  g.stack_allocation.get(&src){
            let (ss, reg) = g.get_offset_reg(*offset);
            reg_out = reg;
            src_reg = format!("t{}", reg);
            *s += &(ss + &format!("\tadd {}, sp, {}\n",src_reg, src_reg));
        } else {
            unreachable!()
        }
        let type_size_reg = g.alloc_tmp_reg().unwrap();
        *s += &format!("\tli t{}, {}\n", type_size_reg, ty_size);
        *s += &format!("\tmul {}, {}, t{}\n",idx_reg, idx_reg, type_size_reg);
        g.free_reg(type_size_reg);
        let (ptr_pos, begin_ptr) = g.get_space(value);
        let mut recover_ptr = false;
        let ptr_reg;
        if let Stack(reg_name) = ptr_pos{
            *s += &begin_ptr;
            recover_ptr = true;
            ptr_reg = reg_name;
        } else if let Reg(reg_name) = ptr_pos{
            ptr_reg = reg_name;
        } else {
            unreachable!()
        }
        *s += &format!("\tadd {}, {}, {}\n",ptr_reg, src_reg, idx_reg);
        if reg_out != -1{
            g.free_reg(reg_out);
        }
        if recover_idx{
            *s += &g.return_reg(idx);
        }
        if recover_ptr{
            *s += &g.return_reg(value);
        }
        if recover_src{
            *s += &g.return_reg(src);
        }
        if tmp_src_reg != -1{
            g.free_reg(tmp_src_reg);
        }
        if tmp_idx_reg != -1{
            g.free_reg(tmp_idx_reg);
        }
    }
    fn get_ptr(&self, s: &mut String, get_ptr: &GetPtr, value: Value){
        let src = get_ptr.src();
        let idx = get_ptr.index();
        let mut m = GLOBAL_REG_ALLOCATOR.lock().unwrap();
        let g = m.get_mut();
        let ty_size;
        let src_reg;
        let idx_reg;
        let ptr_reg;
        let mut tmp_src_reg = -1;
        let mut tmp_idx_reg = -1;
        let mut recover_src = false;
        let mut recover_idx = false;
        let mut recover_ptr = false;
        let (src_reg_pos, src_begin) = g.get_space(src);
        let (ptr_reg_pos, ptr_begin) = g.get_space(value);
        if let Stack(reg_name) = src_reg_pos{
            src_reg = reg_name;
            *s += &src_begin;
            recover_src = true;
        } else if let Reg(reg_name) = src_reg_pos{
            src_reg = reg_name;
        } else {
            let mut m = GLOBAL_VARIABLE.lock().unwrap();
            let k = m.get_mut(&src).unwrap();
            tmp_src_reg = g.alloc_tmp_reg().unwrap();
            src_reg = format!("t{}", tmp_src_reg);
            *s += &format!("\tla {}, {}\n",src_reg, k[1..].to_string());
        }
        if let Stack(reg_name) = ptr_reg_pos{
            ptr_reg = reg_name;
            *s += &ptr_begin;
            recover_ptr = true;
        } else if let Reg(reg_name) = ptr_reg_pos{
            ptr_reg = reg_name;
        } else {
            unreachable!()
        }
        let var_type = GLOBAL_VARIABLE_TYPE.lock().unwrap();
        if let Some((global_var, size)) = var_type.get(&src){
            if  global_var.as_bytes()[0] == b'*'{
                ty_size = *size;
            } else {
                unreachable!()
            }
        } else {
            if let TypeKind::Pointer(p) = self.dfg().value(src).ty().kind(){
                if let TypeKind::Array(ty, size) = p.kind(){
                    ty_size = ty.size() as i32 * (*size as i32);
                } else {
                    ty_size = 4;
                }
            } else {
                unreachable!()
            }
        }
        if let Integer(i) =  self.dfg().value(idx).kind(){
            tmp_idx_reg = g.alloc_tmp_reg().unwrap();
            idx_reg = format!("t{}", tmp_idx_reg);
            *s += &format!("\tli {}, {}\n",idx_reg, i.value());
        } else{
            let (idx_pos, begin_idx) = g.get_space(idx);
            if let Stack(reg_name) = idx_pos{
                idx_reg = reg_name;
                recover_idx = true;
                *s += &begin_idx;
            } else if let Reg(reg_name) = idx_pos{
                idx_reg = reg_name;
            } else {
                unreachable!()
            }
        }
        let type_size_reg = g.alloc_tmp_reg().unwrap();
        *s += &format!("\tli t{}, {}\n", type_size_reg, ty_size);
        *s += &format!("\tmul {}, {}, t{}\n",idx_reg, idx_reg, type_size_reg);
        g.free_reg(type_size_reg);
        *s += &format!("\tadd {}, {}, {}\n",ptr_reg, src_reg, idx_reg);
        g.store_type_bound(value, StoreType::Point);
        if recover_src{
            *s += &g.return_reg(src);
        }
        if recover_ptr{
            *s += &g.return_reg(value);
        }
        if recover_idx{
            *s += &g.return_reg(idx);
        }
        if tmp_src_reg != -1{
            g.free_reg(tmp_src_reg);
        }
        if tmp_idx_reg != -1{
            g.free_reg(tmp_idx_reg);
        }
    }
}
