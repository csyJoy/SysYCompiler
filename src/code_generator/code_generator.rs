use std::borrow::BorrowMut;
// use koopa::ir::{BinaryOp, FunctionData, Program, Value, ValueKind};
use koopa::ir::types::{ TypeKind, Type };
use koopa::ir::values::{Binary, Return, BinaryOp, Alloc, Store, Load, Branch, Jump, Call, GetElemPtr, Aggregate, GetPtr};
use lazy_static::lazy_static;
use std::sync::Mutex;
use std::cell::RefCell;
use std::cmp::min;
use std::collections::{HashMap, VecDeque};
use koopa::ir::entities::{Value, Program, FunctionData, ValueKind, ValueData};
use koopa::ir::Function;
use koopa::ir::ValueKind::Integer;
use rand::Rng;
use crate::code_generator::code_generator::StorePos::Stack;

pub trait GenerateAsm{
    fn generate(&self) -> String;
}
// todo 这里的allocator不是allocator，他只是一个item，之后可以在外面套一个真正的global allocator
pub trait RegAlloctor{
    fn store_type_bound(&mut self, value: Value, store_type: StoreType);
    fn get_offset_reg(&mut self, offset: i32) -> (String, i32);
    fn alloc_tmp_reg(&mut self) -> Option<i32>;
    fn free_reg(&mut self, idx: i32) -> Option<i32>;
    fn bound_space(&mut self, value: Value, size: i32);
    fn get_space(&self, value: Value, size: i32) -> Option<i32>;
    fn return_reg(&mut self, value: Value) -> String;
    fn borrow_reg(&mut self, value: &Value, size: i32) -> (i32, String);
}
pub enum StoreType{
    Value, // single value or one dimension array
    Array,
    Point //the dimension of array
}
pub enum StorePos{
    Reg(String),
    Stack(String)
}
struct GlobalRegAlloctor{
    tmp_reg_pool: Vec<i32>,
    stack_allocation: HashMap<Value, i32>,
    reg_allocation: HashMap<Value, i32>,
    store_type: HashMap<Value, StoreType>,
    borrowed_reg: HashMap<Value, VecDeque<(i32, i32)>>,
    offset: i32
}
impl GlobalRegAlloctor{
    fn new(bottom: i32, top: i32) -> GlobalRegAlloctor{
        let mut v:Vec<i32> = Vec::new();
        for i in (bottom..top+1).rev(){
            v.push(i);
        }
        GlobalRegAlloctor{ tmp_reg_pool: v, reg_allocation: HashMap::new(), stack_allocation:
        HashMap::new(), store_type: HashMap::new() ,borrowed_reg: HashMap::new(), offset: 0 }
    }
    fn fresh(&mut self, reg_allocation: HashMap<Value, i32>){
        // self.reg_pool is no need to fresh, because at the end of a function, all reg is free
        self.reg_allocation = reg_allocation;
        self.stack_allocation.clear();
        self.store_type.clear();
        self.offset = 0;
    }
}
impl RegAlloctor for GlobalRegAlloctor{
    fn store_type_bound(&mut self, value: Value, store_type: StoreType){
        self.store_type.insert(value.clone(), store_type);
    }
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
        for i in &self.tmp_reg_pool {
            if idx == *i{
                unreachable!();
            }
        }
        if idx < 0 || idx >= 7 {
            None
        } else {
            self.tmp_reg_pool.push(idx);
            Some(idx)
        }
    }
    // fn bound_reg(&mut self, value: Value, idx: i32) -> Option<i32> {
    //     self.map.insert(value, StorePos::Reg(idx));
    //     Some(idx)
    // }
    // fn get_reg(&self, value: Value) -> Option<i32> {
    //     Some(*self.map.get(&value).unwrap())
    // }
    fn bound_space(&mut self, value: Value, size: i32){
        self.stack_allocation.insert(value, self.offset);
        self.offset += size;
    }
    /// if value store in reg, return the reg name
    /// if value store in stack, before we load it to the reg
    ///     1. if temp reg not full, alloc a temp reg for it
    ///     2. else alloc a memory for any S_n reg, then move value to S_n, after borrowing,
    ///        store value back to memory, and recover S_n
    fn get_space(&mut self, value: Value, size: i32) -> (StorePos, String){
        if let Some(reg) = self.reg_allocation.get(&value){
            (StorePos::Reg(format!("s{}", *reg)), "".to_string())
        } else if let Some(offset) = self.stack_allocation.get(&value){
            let (idx, store_string) = self.borrowed_reg(value, size);
            let (load_string, reg_idx) = self.get_offset_reg(*offset);
            let now = store_string + load_string + &format!("sub t{}, sp, t{}", reg_idx, reg_idx) +
                &format!("lw \
            s{}, 0(t{})", idx, reg_idx);
            self.free_reg(reg_idx);
            (StorePos::Stack(format!("s{}", reg_idx)), now)
        }
    }
    /// before borrow reg, make sure before value is stored correctly, return the store code, and
    /// the reg idx
    fn borrow_reg(&mut self, value: &Value, size: i32) -> (i32, String){
        let borrowed_reg = rand::thread_rng().gen_range(0, 12);
        self.bound_space(value.clone(), size);
        let Some(offset) = self.stack_allocation.get(value);
        if let Some(queue) = self.borrowed_reg.get_mut(value){
            queue.push_front((borrowed_reg, *offset));
        } else {
            let mut queue = VecDeque::new();
            queue.push_front((borrowed_reg, *offset));
            self.borrowed_reg.insert(value.clone(), queue);
        }
        let (before, reg_idx) = self.get_offset_reg(*offset);
        let now = before + &format!("sub, t{}, sp, t{}", reg_idx, reg_idx) + &format!("sw s{}, 0\
        (t{})", borrowed_reg, reg_idx);
        self.free_reg(reg_idx);
        (borrowed_reg, now)
    }
    /// after return reg, make sure last stored reg value is wrote back to reg, return the load code
    fn return_reg(&mut self, value: Value) -> String{
        let Some((reg, offset)) = self.borrowed_reg.get(&value).unwrap().front();
        let (before, reg_idx) = self.get_offset_reg(*offset);
        let now = before + &format!("sub, t{}, sp, t{}", reg_idx, reg_idx) + &format!("lw s{}, 0\
        (t{})", reg, reg_idx);
        self.free_reg(reg_idx);
        now
    }
}
lazy_static!{
    static ref global_reg_allocator: Mutex<RefCell<GlobalRegAlloctor>> = Mutex::new(RefCell::new
        (GlobalRegAlloctor::new(0, 6)));
    static ref global_function_name: Mutex<HashMap<Function, String>> = Mutex::new(HashMap::new());
    static ref now_sp_size: Mutex<RefCell<i32>> = Mutex::new(RefCell::new(0));
    static ref global_function_type: Mutex<HashMap<Function, String>> = Mutex::new
    (HashMap::new());
    static ref global_varable: Mutex<HashMap<Value, String>> = Mutex::new
    (HashMap::new());
    static ref global_variable_type: Mutex<HashMap<Value, (String, i32)>> = Mutex::new
    (HashMap::new());
}
fn gen_agg_init(agg: &Aggregate, values: HashMap<Value, ValueData>) -> String{
    let mut s = "".to_string();
    for value in agg.elems(){
        if let ValueKind::Integer(ii) = values.get(value).unwrap().kind(){
            if ii.value() == 0{
                s += &format!("\t.zero 4\n");
            } else {
                s += &format!("\t.word {}\n", ii.value());
            }
        } else if let ValueKind::Aggregate(agg1) = values.get(value).unwrap().kind(){
            s += &gen_agg_init(&agg1, values.clone());
        } else {
            println!("{}", values.get(value).unwrap().ty());
            unreachable!();
        }
    }
    s
}
impl GenerateAsm for Program{
    fn generate(&self) -> String {
        let mut s = "".to_string();
        let mut m = global_function_name.lock().unwrap();
        let mut t = global_function_type.lock().unwrap();
        //todo: global var的初始化的值表示了左值的下表，不是一个真值
        let values = self.borrow_values();
        let vvalue = values.iter();
        s += "\t.data\n";
        for (val,val_data) in vvalue{
            let mut var = global_varable.lock().unwrap();
            let mut var_type = global_variable_type.lock().unwrap();
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
                    let init_value = values.get(&g.init());
                    if let Some(i) = init_value{
                        if let ValueKind::Integer(ii) = i.kind(){
                            if ii.value() == 0{
                                s += &format!("\t.zero 4\n");
                            } else {
                                s += &format!("\t.word {}\n", ii.value());
                            }
                        } else if let ValueKind::Aggregate(agg) = i.kind(){
                            s += &gen_agg_init(agg, values.clone());
                        } else if let ValueKind::ZeroInit(_) = i.kind(){
                            if let TypeKind::Array(arr_type, arr_size) = i.ty().kind(){
                                s += &format!("\t.zero {}\n", arr_type.size() * *arr_size);
                            } else {
                                s += &format!("\t.zero {}\n", i.ty().size());
                            }
                        } else {
                            eprintln!("{:#?}", i.kind());
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
        std::mem::drop(m);
        std::mem::drop(t);
        for &func in self.func_layout(){
            let mut head = "\t.text\n".to_string();
            let mut func_def = "".to_string();
            let tmp = &self.func(func).name().to_string()[1..];
            if is_lib(tmp){
                continue;
            }
            head += &format!("\t.global {}\n", tmp);
            func_def += &self.func(func).generate();
            let mut m = global_reg_allocator.lock().unwrap();
            let g = m.borrow_mut().get_mut();
            g.fresh();
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
    Caller((i32, i32)),
    Nocall((i32, i32))
}
fn calculate_and_allocate_space(this: &FunctionData) -> Caller{
    let mut bits:i32 = 0;
    let mut arg_count_max = 0;
    let mut caller: bool = false;
    for (_, node) in this.layout().bbs(){
        for &inst in node.insts().keys(){
            let value_data = this.dfg().value(inst);
            let i32_type = Type::get_i32();
            if !value_data.ty().is_unit(){
                if let TypeKind::Pointer(b) = value_data.ty().kind(){
                    if *b == i32_type{
                        if let ValueKind::Alloc(_) = value_data.kind(){
                            bits += 4;
                        } else {
                            bits += value_data.ty().size() as i32;
                        }
                    } else {
                        if let ValueKind::Alloc(_) = value_data.kind(){
                            if let TypeKind::Array(arr_type, arr_size) = b.kind(){
                                bits += (*arr_size as i32) * arr_type.size() as i32;
                            } else {
                                bits += value_data.ty().size() as i32;
                            }
                        } else {
                            bits += value_data.ty().size() as i32;
                        }
                    }
                } else {
                    if value_data.ty().is_i32(){
                        bits += 4;
                    } else {
                        bits += value_data.ty().size() as i32;
                    }
                }
            }
            if let ValueKind::Call(call) = value_data.kind(){
                let  vec = call.args();
                if vec.len() as i32 - 8 > arg_count_max{
                    arg_count_max = vec.len() as i32 - 8 ;
                }
                caller = true;
            }
        }
    }
    if caller{
        let mut m = now_sp_size.lock().unwrap();
        let sp = ((bits + 4 + (arg_count_max * 4) as i32 + 15) / 16) as i32 * 16;
        *m.get_mut() = sp;
        Caller::Caller((sp, arg_count_max as i32))
    } else {
        let mut m = now_sp_size.lock().unwrap();
        let sp = ((bits   + (arg_count_max * 4) as i32 + 15) / 16) as i32 * 16;
        *m.get_mut() = sp;
        Caller::Nocall((sp, arg_count_max as i32))
    }
}

impl GenerateAsm for FunctionData{
    fn generate(&self) -> String {
        let mut s = "".to_string();
        s += &format!("{}:\n", &self.name().to_string()[1..]);
        let caller = calculate_and_allocate_space(self);
        let sp_len;
        if let Caller::Caller((sp, offset)) = caller{
            let mut k = global_reg_allocator.lock().unwrap();
            let mut m = k.get_mut();
            sp_len = sp;
            let (ss, reg) = m.get_offset_reg(sp);
            s += &(ss + &format!("\tsub sp, sp, t{}\n", reg));
            m.free_reg(reg);
            let (ss, reg) = m.get_offset_reg(sp - 4);
            s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg) +&format!("\tsw ra, 0(t{})\n", reg));
            m.free_reg(reg);
            m.offset = offset * 4;
            // m.free_reg(mid_reg);
        } else if let Caller::Nocall((sp, offset)) = caller{
            let mut k = global_reg_allocator.lock().unwrap();
            let mut m = k.get_mut();
            sp_len = sp;
            let (ss, reg) = m.get_offset_reg(sp);
            s += &(ss + &format!("\tsub sp, sp, t{}\n", reg));
            m.free_reg(reg);
            m.offset = offset * 4;
        } else {
            unreachable!()
        }
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
                        // println!("{:#?}", ret);
                        // println!("{:#?}", self.dfg().value(ret.value().unwrap()));
                        // println!("=============================================");
                        s += "# return gen\n";
                        self.return_gen(&mut s, ret);
                        s += "# return end\n\n"
                    }
                    ValueKind::Binary(bin) => {
                        // println!("{:#?}", bin);
                        // println!("{:#?}, {:#?}", self.dfg().value(bin.rhs()), self.dfg().value
                        // (bin.lhs()));
                        // println!("=============================================");
                        // let l = bin.lhs();
                        // let r = bin.rhs();
                        // self.dfg().value(l).kind()
                        s += "# bin gen\n";
                        self.bin_gen(&mut s, bin, inst);
                        s += "# bin gen end\n\n";
                    }
                    ValueKind::Store(store) => {
                        s += "# store gen \n";
                        self.store_gen(&mut s, store, inst);
                        s += "# store gen end\n\n";
                    }
                    ValueKind::Load(load) => {
                        s += "# load gen \n";
                        self.load_gen(&mut s, load, inst);
                        s += "# load gen end\n\n";
                    }
                    ValueKind::Alloc(alloc) => {
                        s += "# alloc gen\n";
                        self.alloc_gen(&mut s, alloc, inst);
                        s += "# alloc gen end\n\n";
                    }
                    ValueKind::Branch(branch) => {
                        s += "# branch gen\n";
                        self.branch_gen(&mut s, branch, inst);
                        s += "# branch gen end\n\n";
                    }
                    ValueKind::Jump(jump) => {
                        s += "# jump gen\n";
                        self.jump_gen(&mut s, jump, inst);
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
                    // println!("{}",a);
                    if *a == end_name{
                        if let Caller::Caller((sp, _)) = caller{
                            let mut k = global_reg_allocator.lock().unwrap();
                            let m = k.get_mut();
                            let (ss, reg) = m.get_offset_reg(sp - 4);
                            s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg) + &format!("\tlw ra, 0(t{})\n", reg));
                            m.free_reg(reg);
                        }
                        let mut k = global_reg_allocator.lock().unwrap();
                        let m = k.get_mut();
                        let (ss, reg) = m.get_offset_reg(sp_len);
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
    fn alloc_gen(&self, s: &mut String, alloc: &Alloc, value: Value);
    fn load_gen(&self, s: &mut String, alloc: &Load, value: Value);
    fn store_gen(&self, s: &mut String, alloc: &Store, value: Value);
    fn branch_gen(&self, s: &mut String, branch: &Branch, value: Value);
    fn jump_gen(&self, s: &mut String, jump: &Jump, value: Value);
    fn call_gen(&self, s: &mut String, call: &Call, value: Value);
    fn get_elem_ptr_gen(&self, s: &mut String, get_elem_ptr: &GetElemPtr, value: Value);
    fn get_ptr(&self, s: &mut String, get_ptr: &GetPtr, value: Value);
}
impl SplitGen for FunctionData {
    fn get_ptr(&self, s: &mut String, get_ptr: &GetPtr, value: Value){
        let src = get_ptr.src();
        let idx = get_ptr.index();
        let mut m = global_reg_allocator.lock().unwrap();
        let g = m.get_mut();
        let mut idx_reg = 0;
        let mut ty_size = 0;
        g.store_type_bound(value, StoreType::Point);
        let var_type = global_variable_type.lock().unwrap();
        if let Some((global_var, size)) = var_type.get(&src){
            if  global_var.as_bytes()[0] == b'*'{
                println!("this is a global point of array:{}, size is {}", global_var, size);
                ty_size = *size;
            }
        } else {
            if let TypeKind::Pointer(p) = self.dfg().value(src).ty().kind(){
                if let TypeKind::Array(ty, size) = p.kind(){
                    println!("this is a point of array:{}, the size is {}, inner type is {}", self.dfg().value(src).ty().to_string(), size, ty.size());
                    ty_size = ty.size() as i32 * (*size as i32);
                } else {
                    ty_size = 4;
                }
            }
        }
        if let ValueKind::Integer(i) =  self.dfg().value(idx).kind(){
            idx_reg = g.alloc_tmp_reg().unwrap();
            *s += &format!("\tli t{}, {}\n",idx_reg, i.value());
        } else{
            let mut offset = 0;
            offset = g.get_space(idx).unwrap();
            let (ss, reg) = g.get_offset_reg(offset);
            idx_reg = reg;
            *s += &(ss + &format!("\tadd t{}, sp, t{}\n",idx_reg, idx_reg)+ &format!("\tlw t{}, 0(t{})\n", idx_reg, idx_reg));
        }
        let mut src_reg = 0;
        if let Some(offset) = g.get_space(src){
            let (ss, reg) = g.get_offset_reg(offset);
            src_reg = reg;
            if let StoreType::Point = g.store_type.get(&src).unwrap(){
                *s += &(ss + &format!("\tadd t{}, sp, t{}\n",src_reg, src_reg)+ &format!("\tlw t{}, 0(t{})\n", src_reg, src_reg));
            } else {
                *s += &(ss + &format!("\tadd t{}, sp, t{}\n",src_reg, src_reg) + &format!("\tlw t{}, 0(t{})\n", src_reg, src_reg));
            }
        } else {
            let mut m = global_varable.lock().unwrap();
            let k = m.get_mut(&src).unwrap();
            src_reg = g.alloc_tmp_reg().unwrap();
            *s += &format!("\tla t{}, {}\n",src_reg, k[1..].to_string());
        }
        let type_size_reg = g.alloc_tmp_reg().unwrap();
        *s += &format!("\tli t{}, {}\n", type_size_reg, ty_size);
        *s += &format!("\tmul t{}, t{}, t{}\n",idx_reg, idx_reg, type_size_reg);
        g.free_reg(type_size_reg);
        let rst_reg = g.alloc_tmp_reg().unwrap();
        *s += &format!("\tadd t{}, t{}, t{}\n",rst_reg, src_reg, idx_reg);
        g.free_reg(src_reg);
        g.free_reg(idx_reg);
        g.bound_space(value, self.dfg().value(value).ty().size() as i32);
        g.store_type_bound(value, StoreType::Point);
        let offset = g.get_space(value).unwrap();
        let (ss, reg) = g.get_offset_reg(offset);
        *s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tsw t{}, 0(t{})\n", rst_reg,  reg));
        g.free_reg(reg);
        // g.free_reg(s0);
        g.free_reg(rst_reg);
    }
    fn get_elem_ptr_gen(&self, s: &mut String, get_elem_ptr: &GetElemPtr, value: Value){
        let src = get_elem_ptr.src();
        let idx = get_elem_ptr.index();
        let mut idx_reg = 0;
        let mut src_reg = 0;
        let mut m = global_reg_allocator.lock().unwrap();
        let g = m.get_mut();
        let mut ty_size = 0;
        g.store_type_bound(value, StoreType::Point);
        let var_type = global_variable_type.lock().unwrap();
        if let Some((global_var, size)) = var_type.get(&src){
            if  global_var.as_bytes()[0] == b'*'{
                println!("this is a global point of array:{}, size is {}", global_var, size);
                ty_size = *size;
            }
        } else {
            if let TypeKind::Pointer(p) = self.dfg().value(src).ty().kind(){
                if let TypeKind::Array(ty, size) = p.kind(){
                    println!("this is a point of array, the size is {}, inner type is {}", size, ty.size());
                    ty_size = ty.size() as i32;
                }
            }
        }
        if let ValueKind::Integer(i) =  self.dfg().value(idx).kind(){
            idx_reg = g.alloc_tmp_reg().unwrap();
            *s += &format!("\tli t{}, {}\n",idx_reg, i.value());
        } else{
            let offset = g.get_space(idx).unwrap();
            let (ss, reg) = g.get_offset_reg(offset);
            idx_reg = reg;
            *s += &(ss + &format!("\tadd t{}, sp, t{}\n",idx_reg, idx_reg)+ &format!("\tlw t{}, 0(t{})\n", idx_reg, idx_reg));
            // *s += &format!("\tlw t{}, {}(sp)\n",idx_reg, g.get_space(idx).unwrap());
        }
        if let Some(offset) = g.get_space(src){
            // let offset = g.get_space(value).unwrap();
            let (ss, reg) = g.get_offset_reg(offset);
            src_reg = reg;
            if let StoreType::Point = g.store_type.get(&src).unwrap(){
                *s += &(ss + &format!("\tadd t{}, sp, t{}\n",src_reg, src_reg)+ &format!("\tlw t{}, 0(t{})\n", src_reg, src_reg));
            } else {
                *s += &(ss + &format!("\tadd t{}, sp, t{}\n",src_reg, src_reg));
            }
            // *s += &format!("\tlw t{}, {}(sp)\n",src_reg, offset);
        } else {
            let mut m = global_varable.lock().unwrap();
            let k = m.get_mut(&src).unwrap();
            src_reg = g.alloc_tmp_reg().unwrap();
            *s += &format!("\tla t{}, {}\n",src_reg, k[1..].to_string());
        }
        //todo: 没有添加对大的type_size的特殊处理
        let type_size_reg = g.alloc_tmp_reg().unwrap();
        *s += &format!("\tli t{}, {}\n", type_size_reg, ty_size); //todo:对不同维度有不同的值，需要判断
        *s += &format!("\tmul t{}, t{}, t{}\n",idx_reg, idx_reg, type_size_reg);
        g.free_reg(type_size_reg);
        *s += &format!("\tadd t{}, t{}, t{}\n",src_reg, src_reg, idx_reg);
        g.bound_space(value, self.dfg().value(value).ty().size() as i32);
        g.free_reg(idx_reg);
        let offset = g.get_space(value).unwrap();
        let (ss, reg) = g.get_offset_reg(offset);
        *s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tsw t{}, 0(t{})\n", src_reg, reg));
        g.free_reg(reg);
        g.free_reg(src_reg);
    }
    fn call_gen(&self, s: &mut String, call: &Call, value: Value) {
        let arg_vec = call.args();
        let mut len = arg_vec.len() as i32;
        let mut m = global_reg_allocator.lock().unwrap();
        let g = m.get_mut();
        for i   in 0..min(len, 8){
            let idx = i as usize;
            if let ValueKind::Integer(int) = self.dfg().value(arg_vec[idx]).kind(){
                *s += &format!("\tli a{}, {}\n", i, int.value());
            } else {
                let src_offset = g.get_space(arg_vec[idx]).unwrap();
                let reg_idx = g.alloc_tmp_reg().unwrap();
                let (ss, reg) = g.get_offset_reg(src_offset);
                *s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tlw t{}, 0(t{})\n\tmv a{}, t{}\n", reg_idx, reg, i,
                               reg_idx));
                g.free_reg(reg_idx);
                g.free_reg(reg);
            }
        }
        let mut idx = 8;
        while len - 8 > 0{
            let value = arg_vec[idx];
            if let ValueKind::Integer(i) = self.dfg().value(value).kind(){
                let tmp = g.alloc_tmp_reg().unwrap();
                let offset = ((idx - 8) * 4) as i32;
                let (ss, reg) = g.get_offset_reg(offset);
                *s += &(ss +&format!("\tadd t{}, sp, t{}\n",reg, reg)+ &(format!("\tli t{}, {}\n",tmp , i.value()) +  &format!("\tsw t{}, 0(t{})\
                \n", tmp,  reg)));
                g.free_reg(reg);
                g.free_reg(tmp);
            } else {
                let src_offset = g.get_space(value).unwrap();
                let reg_idx = g.alloc_tmp_reg().unwrap();
                let (src_ss, src_reg) = g.get_offset_reg(src_offset);
                let offset = ((idx - 8) * 4) as i32;
                let (ss, reg) = g.get_offset_reg(offset);
                *s += &(src_ss + &format!("\tadd t{}, sp, t{}\n",src_reg, src_reg)+ &format!("\tlw t{}, 0(t{})\n", reg_idx,  src_reg)+ &ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tsw t{}, 0\
                (t{})\n",
                                                                           reg_idx, reg));

                g.free_reg(src_reg);
                g.free_reg(reg);
                g.free_reg(reg_idx);
            }
            len = len - 1;
            idx = idx + 1;
        }
        let m = global_function_name.lock().unwrap();
        *s += &format!("\tcall {}\n", m.get(&call.callee()).unwrap()[1..].to_string());
        let t = global_function_type.lock().unwrap();
        let a = t.get(&call.callee()).unwrap();
        if a == "i32"{
            g.bound_space(value, 4);
            g.store_type_bound(value, StoreType::Value);
            let offset = g.get_space(value).unwrap();
            let (ss, reg) = g.get_offset_reg(offset);
            *s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tsw a0, 0(t{})\n", reg));
            g.free_reg(reg);
        }
    }
    fn return_gen(&self, s: &mut String, ret: &Return) {
        if let Some(val) = ret.value() {
            let a = self.dfg().value(val);
            let b = a.kind();
            match b {
                ValueKind::Integer(i) =>
                    *s += &format!("\tli a0, {}\n", i.value()),
                _ =>{
                    let mut g = global_reg_allocator.lock().unwrap();
                    let r = g.borrow_mut().get_mut();
                    let offset = r.get_space(val).unwrap();
                    let (ss, reg) = r.get_offset_reg(offset);
                    *s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tlw a0, 0(t{})\n", reg));
                    r.free_reg(reg);
                }
            }
        }
    }
    fn bin_gen(&self, s: &mut String, bin: &Binary, value: Value) {
        let r_value = bin.rhs();
        let l_value = bin.lhs();
        let mut r_s:String;
        let mut l_s:String;
        let op = bin.op();
        let mut bin_operation:String;
        let mut idx = 0;
        let mut g = global_reg_allocator.lock().unwrap();
        let r = g.borrow_mut().get_mut();
        let size = self.dfg().value(value).ty().size() as i32;
        r.bound_space(value, size);
        r.store_type_bound(value, StoreType::Value);
        let mut tmp_r:i32 = 0;
        let mut tmp_l:i32 = 0;
        let mut r_use_x0 = false;
        let mut l_use_x0 = false;
        if let ValueKind::Integer(i) = self.dfg().value(r_value).kind(){
            if i.value() == 0 {
                r_s = format!("x0");
                r_use_x0 = true;
            } else {
                tmp_r = r.alloc_tmp_reg().unwrap();
                *s += &format!("\tli t{}, {}\n", tmp_r,i.value());
                r_s = format!("t{}", tmp_r);
            }
        } else {
            tmp_r = r.alloc_tmp_reg().unwrap();
            let offset = r.get_space(r_value).unwrap();
            let (ss, reg) = r.get_offset_reg(offset);
            *s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tlw t{}, 0(t{})\n", tmp_r, reg));
            r_s = format!("t{}", tmp_r);
            r.free_reg(reg);
        }
        if let ValueKind::Integer(i) = self.dfg().value(l_value).kind(){
            if i.value() == 0{
                l_s = format!("x0");
                l_use_x0 = true;
            } else {
                tmp_l = r.alloc_tmp_reg().unwrap();
                *s += &format!("\tli t{}, {}\n", tmp_l, i.value());
                l_s = format!("t{}", tmp_l);
            }
        } else {
            tmp_l = r.alloc_tmp_reg().unwrap();
            let offset = r.get_space(l_value).unwrap();
            let (ss, reg) = r.get_offset_reg(offset);
            *s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tlw t{}, 0(t{})\n", tmp_l, reg));
            l_s = format!("t{}", tmp_l);
            r.free_reg(reg);
            // r.free_reg(tmp_l);
        }
        idx = r.alloc_tmp_reg().unwrap();
        match op{
            BinaryOp::Add => {
                bin_operation = "add".to_string();
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Sub => {
                bin_operation = "sub".to_string();
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Mul => {
                bin_operation = "mul".to_string();
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Div => {
                bin_operation = "div".to_string();
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Mod => {
                bin_operation = "rem".to_string();
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Eq => {
                let tmp = r.alloc_tmp_reg().unwrap();
                *s += &format!("\txor t{}, {}, {}\n", tmp, l_s, r_s);
                *s += &format!("\tseqz t{}, t{}\n", idx, tmp);
                r.free_reg(tmp);
            },
            BinaryOp::And => {
                bin_operation = "and".to_string();
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Or => {
                bin_operation = "or".to_string();
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::NotEq => {
                let tmp = r.alloc_tmp_reg().unwrap();
                *s += &format!("\txor t{}, {}, {}\n", tmp, l_s, r_s);
                *s += &format!("\tsnez t{}, t{}\n", idx, tmp);
                r.free_reg(tmp);
            },
            BinaryOp::Le => {
                bin_operation = "slt".to_string();
                let tmp = r.alloc_tmp_reg().unwrap();
                let tmp1 = r.alloc_tmp_reg().unwrap();
                *s += &format!("\txor t{}, {}, {}\n", tmp, l_s, r_s);
                *s += &format!("\tseqz t{}, t{}\n", idx, tmp);
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, tmp1, l_s, r_s);
                *s += &format!("\tor t{}, t{}, t{}\n", idx, idx, tmp1);
                r.free_reg(tmp);
                r.free_reg(tmp1);
            },
            BinaryOp::Lt => {
                bin_operation = "slt".to_string();
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Gt => {
                bin_operation = "slt".to_string();
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, idx, r_s, l_s);
            },
            BinaryOp::Ge =>{
                bin_operation = "slt".to_string();
                let tmp = r.alloc_tmp_reg().unwrap();
                let tmp1 = r.alloc_tmp_reg().unwrap();
                *s += &format!("\txor t{}, {}, {}\n", tmp, l_s, r_s);
                *s += &format!("\tseqz t{}, t{}\n", idx, tmp);
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, tmp1, r_s, l_s);
                *s += &format!("\tor t{}, t{}, t{}\n", idx, idx, tmp1);
                r.free_reg(tmp);
                r.free_reg(tmp1);
            }
            _ => bin_operation = "".to_string()
        }
        if !l_use_x0{
            r.free_reg(tmp_l);
        }
        if !r_use_x0{
            r.free_reg(tmp_r);
        }
        let mut offset = 0;
        offset = r.get_space(value).unwrap();
        let (ss, reg) = r.get_offset_reg(offset);
        *s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tsw t{}, 0(t{})\n", idx, reg));
        r.free_reg(idx);
        r.free_reg(reg);
    }
    fn load_gen(&self, s: &mut String, load: &Load, value: Value) {
        let src_value = load.src();
        let var = global_varable.lock().unwrap();
        let mut offset = 0;
        let reg_idx = 0;
        let size = self.dfg().value(value).ty().size() as i32;
        let mut m = global_reg_allocator.lock().unwrap();
        let g = m.get_mut();
        g.bound_space(value, size);
        g.store_type_bound(value, StoreType::Value);
        offset = g.get_space(value).unwrap();
        if let Some(src_offset) = g.get_space(src_value){
            let (src_ss, src_reg) = g.get_offset_reg(src_offset);
            let (ss, reg) = g.get_offset_reg(offset);
            if let StoreType::Point = g.store_type.get(&src_value).unwrap(){
                *s += &(src_ss + &format!("\tadd t{}, sp, t{}\n",src_reg, src_reg) + &(format!("\tlw t{}, 0(t{})\n",src_reg, src_reg) +&format!("\tlw t{}, 0(t{})\n", src_reg, src_reg) + &ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tsw t{}, 0(t{})\n",
                                                                                                                                                                                                          src_reg, reg)));
            } else {
                *s += &(src_ss + &format!("\tadd t{}, sp, t{}\n",src_reg, src_reg)+ &(format!("\tlw t{}, 0(t{})\n",src_reg, src_reg)  + &ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tsw t{}, 0(t{})\n",
                                                                                                    src_reg, reg)));
            }
            g.free_reg(reg);
            g.free_reg(src_reg);
        } else if let Some(name) = var.get(&src_value){
            let tmp_reg = g.alloc_tmp_reg().unwrap();
            let (ss, reg) = g.get_offset_reg(offset);
            *s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tla t{}, {}\n\tlw t{}, 0(t{})\n\tsw t{}, 0(t{})\n",tmp_reg, name[1..] .to_string(), tmp_reg, tmp_reg,tmp_reg,reg));
            g.free_reg(tmp_reg);
            g.free_reg(reg);
        }
        // g.free_reg(reg_idx);
    }
    fn store_gen(&self, s: &mut String, store: &Store, value: Value) {
        let value = store.value();
        let dest = store.dest();
        let var = global_varable.lock().unwrap();
        let mut m = global_reg_allocator.lock().unwrap();
        let g = m.get_mut();
        let reg_idx = g.alloc_tmp_reg().unwrap();
        if let Some(offset) = g.get_space(dest){
            if let ValueKind::Integer(i) = self.dfg().value(value).kind(){
                let (ss, reg)  = g.get_offset_reg(offset);
                if let StoreType::Point = g.store_type.get(&dest).unwrap(){
                    let tmp = g.alloc_tmp_reg().unwrap();
                    *s += &(format!("\tli t{}, {}\n",reg_idx, i.value()) + &ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tlw t{}, 0(t{})\
                \n", tmp, reg) + &format!("\tsw t{}, 0(t{})\n", reg_idx, tmp));
                    //+&format!("\tadd t{}, sp, t{}\n", tmp, tmp)
                    g.free_reg(tmp);
                } else {
                    *s += &(format!("\tli t{}, {}\n",reg_idx, i.value()) + &ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tsw t{}, 0(t{})\
                \n", reg_idx, reg));
                }
                g.free_reg(reg);
            } else {
                //todo 传参数
                let ty = self.dfg().value(value).kind();
                match ty{
                    ValueKind::FuncArgRef(func_arg_ref) => {
                        if func_arg_ref.index() < 8{
                            let (ss, reg) = g.get_offset_reg(offset);
                            *s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg) +  &format!("\tsw a{}, 0(t{})\n", func_arg_ref.index(), reg));
                            g.free_reg(reg);
                        } else {
                            let mut k = now_sp_size.lock().unwrap();
                            let sp_size = k.get_mut();
                            let src_offset = *sp_size + 4 * (func_arg_ref.index() as i32 - 8);
                            let (src_ss, src_reg) = g.get_offset_reg(src_offset);
                            let (ss, reg) = g.get_offset_reg(offset);
                            *s += &(src_ss + &ss  + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tadd t{}, sp, t{}\n",src_reg, src_reg)+&format!("\tlw t{}, 0(t{})\n\tsw t{}, 0(t{})\n",reg_idx, src_reg, reg_idx, reg));
                            g.free_reg(reg);
                            g.free_reg(src_reg);
                        }
                    }
                    _ => {
                        let src_offset = g.get_space(value).unwrap();
                        let (ss, reg) = g.get_offset_reg(offset);
                        let (src_ss, src_reg) = g.get_offset_reg(src_offset);
                        if let StoreType::Point = g.store_type.get(&dest).unwrap() {
                            *s += &(src_ss + &format!("\tadd t{}, sp, t{}\n",src_reg, src_reg)+ &format!("\tlw t{}, 0(t{})\n", src_reg, src_reg) + &ss  + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tlw t{}, 0(t{})\n", reg, reg) + &format!("\tsw t{}, 0(t{})\n", src_reg, reg));
                        } else {
                            *s += &(src_ss + &format!("\tadd t{}, sp, t{}\n",src_reg, src_reg)+ &format!("\tlw t{}, 0(t{})\n", src_reg, src_reg) + &ss  + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tsw t{}, 0(t{})\n", src_reg, reg));
                        }
                        g.free_reg(reg);
                        g.free_reg(src_reg);
                    }
                }
            }
        } else if let Some(name) = var.get(&dest){
            if let ValueKind::Integer(i) = self.dfg().value(value).kind(){
                let tmp_reg = g.alloc_tmp_reg().unwrap();
                *s += &(format!("\tli t{}, {}\n",reg_idx, i.value()) + &format!("\tla t{}, \
                {}\n\tsw t{}, 0(t{})\n", tmp_reg, name[1..].to_string(), reg_idx, tmp_reg));
                g.free_reg(tmp_reg);
            } else {
                //todo 传参数
                let ty = self.dfg().value(value).kind();
                match ty{
                    ValueKind::FuncArgRef(func_arg_ref) => {
                        if func_arg_ref.index() < 8{
                            let tmp = g.alloc_tmp_reg().unwrap();
                            *s += &format!("\tla t{}, {}\n\tsw a{}, 0(t{})\n",tmp, name[1..].to_string() , func_arg_ref.index(), tmp);
                            g.free_reg(tmp);
                        } else {
                            let tmp = g.alloc_tmp_reg().unwrap();
                            let mut k = now_sp_size.lock().unwrap();
                            let sp_size = k.get_mut();
                            let offset = *sp_size + 4 * (func_arg_ref.index() as i32 - 8);
                            let (ss, reg) = g.get_offset_reg(offset);
                            *s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg) + &format!("\tlw t{}, 0(t{})\n\tla t{}, {}\n\tsw t{}, 0(t{})\n", reg, reg,  tmp, name[1..].to_string(),reg, tmp));
                            g.free_reg(tmp);
                            g.free_reg(reg);
                        }
                    }
                    _ => {
                        let src_offset = g.get_space(value).unwrap();
                        let tmp = g.alloc_tmp_reg().unwrap();
                        let (ss, reg) = g.get_offset_reg(src_offset);
                        *s += &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tlw t{}, 0(t{})\n\tla t{}, {}\n",reg, reg,
                                        tmp, name[1..].to_string()) + &format!("\tsw t{}, 0(t{})\n", reg, tmp));
                        g.free_reg(tmp);
                        g.free_reg(reg);
                    }
                }
            }
        }
        g.free_reg(reg_idx);
    }
    fn alloc_gen(&self, s: &mut String, alloc: &Alloc, value: Value) {
        //todo: 对指针的处理
        let mut m = global_reg_allocator.lock().unwrap();
        let g = m.get_mut();
        let mut size = 0;
        if let TypeKind::Pointer(type_id)= self.dfg().value(value).ty().kind(){
            let i32_type = Type::get_i32();
            if i32_type == *type_id{
                size = 4;
                g.store_type_bound(value, StoreType::Value);
            } else {
                if let TypeKind::Array(arr_type, arr_size) = type_id.kind(){
                    size = *arr_size as i32 * arr_type.size() as i32;
                    g.store_type_bound(value, StoreType::Value);
                } else if let TypeKind::Pointer(inner_type) = type_id.kind(){
                    size = type_id.size() as i32;
                    g.store_type_bound(value, StoreType::Value); //todo: change point into value
                } else {
                    unreachable!();
                }
            }
            g.bound_space(value, size);
        } else {
            unreachable!();
        }
        // if self.dfg().value(value).ty().is_i32(){
        //     size = 4;
        // } else {
        //     size = self.dfg().value(value).ty().size() as i32;
        // }
    }
    fn branch_gen(&self, s: &mut String, branch: &Branch, value: Value) {
        let cond = branch.cond();
        let then_branch = branch.true_bb();
        let else_branch = branch.false_bb();
        let mut k = global_reg_allocator.lock().unwrap();
        let g = k.get_mut();
        let reg_idx = g.borrow_mut().alloc_tmp_reg().unwrap();
        if let Some(offset) = g.borrow_mut().get_space(cond){
            let (ss, reg) = g.get_offset_reg(offset);
            *s +=  &(ss + &format!("\tadd t{}, sp, t{}\n",reg, reg)+ &format!("\tlw t{}, 0(t{})\n",reg_idx, reg));
            g.free_reg(reg);
        } else if let Integer(i) = self.dfg().value(cond).kind(){
            *s += &format!("\tli t{}, {}\n", reg_idx, i.value());
        } else {
            unreachable!();
        }
        if let Some(then_data) = self.dfg().bbs().get(&then_branch){
            if let Some(then_name) = then_data.name(){
                let kk = then_name.to_string()[1..then_name.len()].to_string();
                *s += &format!("\tbnez t{}, {}\n", reg_idx, kk);
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
        g.borrow_mut().free_reg(reg_idx);
    }
    fn jump_gen(&self, s: &mut String, jump: &Jump, value: Value) {
        let target = jump.target();
        if let Some(bd) = self.dfg().bbs().get(&target){
            if let Some(name) = bd.name(){
                let kk = name.to_string()[1..name.len()].to_string();
                *s += &format!("\tj {}\n\n", kk);
            }
        }
    }
}
