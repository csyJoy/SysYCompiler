use std::any::Any;
use std::borrow::BorrowMut;
//use koopa::ir::{BinaryOp, FunctionData, Program, Value, ValueKind};
use koopa::ir::values::{Binary, Return, BinaryOp, Alloc, Store, Load, Branch, Jump, Call};
use lazy_static::lazy_static;
use std::sync::Mutex;
use std::cell::{Ref, RefCell};
use std::collections::HashMap;
use koopa::ir::entities::{Value, Program, FunctionData, ValueKind, ValueData};
use koopa::ir::{Function, Type, TypeKind};
use koopa::ir::ValueKind::Integer;
use crate::codeGenerator::code_generator::Caller::Nocall;
use crate::frontEnd::GlobalSymbolTableAllocator;
use std::sync::Arc;

pub trait GenerateAsm{
    fn generate(&self) -> String;
}
// todo 这里的allocator不是allocator，他只是一个item，之后可以在外面套一个真正的global allocator
pub trait RegAlloctor{
    fn alloc_reg(&mut self) -> Option<i32>;
    fn free_reg(&mut self, idx: i32) -> Option<i32>;
    #[deprecated]
    fn bound_reg(&mut self, value: Value, idx: i32) -> Option<i32>;
    #[deprecated]
    fn get_reg(&self, value: Value) -> Option<i32>;

    fn bound_space(&mut self, value: Value, size: i32);
    fn get_space(&self, value: Value) -> Option<i32>;
}
struct GlobalRegAlloctor{
    reg_pool: Vec<i32>,
    map: HashMap<Value, i32>,
    offset: i32
}
impl GlobalRegAlloctor{
    fn new(bottom: i32, top: i32) -> GlobalRegAlloctor{
        let mut v:Vec<i32> = Vec::new();
        for i in (bottom..top+1).rev(){
            v.push(i);
        }
        GlobalRegAlloctor{ reg_pool: v, map: HashMap::new(), offset: 0 }
    }
    fn fresh(&mut self){
        // self.reg_pool is no need to fresh, because at the end of a function, all reg is free
        self.map.clear();
        self.offset = 0;
    }
}
impl RegAlloctor for GlobalRegAlloctor{
    fn free_reg(&mut self, idx: i32) -> Option<i32>{
        if(idx == 0) {
            None
        } else {
            self.reg_pool.push(idx);
            Some(idx)
        }
    }
    fn alloc_reg(&mut self) -> Option<i32> {
        if !self.reg_pool.is_empty(){
            self.reg_pool.pop()
        } else {
            None
        }
    }
    fn get_reg(&self, value: Value) -> Option<i32> {
        Some(*self.map.get(&value).unwrap())
    }
    fn bound_reg(&mut self, value: Value, idx: i32) -> Option<i32> {
        self.map.insert(value, idx);
        Some(idx)
    }
    fn bound_space(&mut self, value: Value, size: i32){
        self.map.insert(value, self.offset);
        self.offset += size;
    }
    fn get_space(&self, value: Value) -> Option<i32> {
        if let Some(offset) = self.map.get(&value){
            Some(*offset)
        } else {
            None
        }
    }

}
lazy_static!{
    static ref global_reg_allocator: Mutex<RefCell<GlobalRegAlloctor>> = Mutex::new(RefCell::new
        (GlobalRegAlloctor::new(1, 7)));
    static ref global_function_name: Mutex<HashMap<Function, String>> = Mutex::new(HashMap::new());
}


impl GenerateAsm for Program{
    fn generate(&self) -> String {
        let mut s = "".to_string();
        let mut m = global_function_name.lock().unwrap();
        //todo: global var的初始化的值表示了左值的下表，不是一个真值
        let mut values = self.borrow_values();
        let mut vvalue = values.iter();
        s += "\t.data\n";
        for (val,val_data) in vvalue{
            if let Some(name) = val_data.name(){
                s += &format!("\t.global {}\n",name);
                s += &format!("{}:\n",name);
                if let ValueKind::GlobalAlloc(g) = val_data.kind(){
                    let init_value = values.get(&g.init());
                    if let Some(i) = init_value{
                        if let ValueKind::Integer(ii) = i.kind(){
                            if ii.value() == 0{
                                s += &format!("\t.zero 4\n");
                            } else {
                                s += &format!("\t.word {}\n", ii.value());
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
        for &func in self.func_layout(){
            m.insert(func.clone(), self.func(func).name().to_string());
        }
        std::mem::drop(m);
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
            let mut g = m.borrow_mut().get_mut();
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
    for (&bb, node) in this.layout().bbs(){
        for &inst in node.insts().keys(){
            let value_data = this.dfg().value(inst);
            if !value_data.ty().is_unit(){
                bits += 4;
                if let ValueKind::Call(call) = value_data.kind(){
                    let  vec = call.args();
                    if vec.len() as i32 - 8 > arg_count_max{
                        arg_count_max = vec.len() as i32 - 8 ;
                    }
                    caller = true;
                }
            }
        }
    }
    if caller{
        Caller::Caller((((bits + (arg_count_max * 4) as i32 + 15) / 16) as i32 * 16, arg_count_max
            as i32))
    } else {
        Caller::Nocall((((bits + (arg_count_max * 4) as i32 + 15) / 16) as i32 * 16, arg_count_max as i32))
    }
}

impl GenerateAsm for FunctionData{
    fn generate(&self) -> String {
        let mut s = "".to_string();
        s += &format!("{}:\n", &self.name().to_string()[1..]);
        let caller = calculate_and_allocate_space(self);
        let mut sp_len = 0;
        if let Caller::Caller((sp, offset)) = caller{
            sp_len = sp;
            s += &format!("\taddi sp, sp, -{}\n",sp);
            s += &format!("\tsw ra, {}(sp)\n", sp - 4);
            let mut k = global_reg_allocator.lock().unwrap();
            let mut m = k.get_mut();
            m.offset = offset * 4;
        } else if let Caller::Nocall((sp, offset)) = caller{
            sp_len = sp;
            s += &format!("\taddi sp, sp, -{}\n",sp);
            let mut k = global_reg_allocator.lock().unwrap();
            let mut m = k.get_mut();
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
                        self.return_gen(&mut s, ret, inst);
                    }
                    ValueKind::Binary(bin) => {
                        // println!("{:#?}", bin);
                        // println!("{:#?}, {:#?}", self.dfg().value(bin.rhs()), self.dfg().value
                        // (bin.lhs()));
                        // println!("=============================================");
                        // let l = bin.lhs();
                        // let r = bin.rhs();
                        // self.dfg().value(l).kind()
                        self.bin_gen(&mut s, bin, inst);
                    }
                    ValueKind::Store(store) => {
                        self.store_gen(&mut s, store, inst);
                    }
                    ValueKind::Load(load) => {
                        self.load_gen(&mut s, load, inst);
                    }
                    ValueKind::Alloc(alloc) => {
                        self.alloc_gen(&mut s, alloc, inst);
                    }
                    ValueKind::Branch(branch) => {
                        self.branch_gen(&mut s, branch, inst);
                    }
                    ValueKind::Jump(jump) => {
                        self.jump_gen(&mut s, jump, inst);
                    }
                    ValueKind::Call(call) => {
                        self.call_gen(&mut s, call, inst);
                    }
                    _ => unreachable!(),
                }
            }
            if let Caller::Caller((sp, offeset)) = caller{
                s += &format!("\tlw ra, {}(sp)\n", sp - 4);
            }
            let name = self.name();
            let end_name = format!("%end_{}", name[1..].to_string());
            if let Some(data) = self.dfg().bbs().get(&bb){
                if let Some(a) = &data.name(){
                    println!("{}",a);
                    if *a == end_name{
                        s += &format!("\taddi sp, sp, {}\n",sp_len);
                        s += &format!("\tret\n\n");
                    }
                }
            }
        }

        s
    }
}

trait splitGen{
    fn return_gen(&self, s: &mut String, ret: &Return, value: Value);
    fn bin_gen(&self, s: &mut String, bin: &Binary, value: Value);
    fn alloc_gen(&self, s: &mut String, alloc: &Alloc, value: Value);
    fn load_gen(&self, s: &mut String, alloc: &Load, value: Value);
    fn store_gen(&self, s: &mut String, alloc: &Store, value: Value);
    fn branch_gen(&self, s: &mut String, branch: &Branch, value: Value);
    fn jump_gen(&self, s: &mut String, jump: &Jump, value: Value);
    fn call_gen(&self, s: &mut String, call: &Call, value: Value);
}
impl splitGen for FunctionData {
    fn call_gen(&self, s: &mut String, call: &Call, value: Value) {
        let arg_vec = call.args();
        let mut len = arg_vec.len() as i32;
        while len - 8 > 0{
            let mut idx = 8;
            let value = arg_vec[idx];
            if let ValueKind::Integer(i) = self.dfg().value(value).kind(){
                *s += &format!("sw {}, {}(to_string)",i.value(), (idx - 8) * 4);
            } else {
                let mut m = global_reg_allocator.lock().unwrap();
                let mut g = m.get_mut();
                let src_offset = g.get_space(value).unwrap();
                let reg_idx = g.alloc_reg().unwrap();
                *s += &(format!("\tlw t{}, {}(sp)\n", reg_idx, src_offset)+&format!("\tsw t{}, {}\
                (sp)\n",
                                                                           reg_idx, (idx - 8) * 4));
                g.free_reg(reg_idx);
            }
            len = len - 1;
            idx = idx + 1;
        }
        let m = global_function_name.lock().unwrap();
        *s += &format!("\tcall {}\n", m.get(&call.callee()).unwrap()[1..].to_string());
        let mut m = global_reg_allocator.lock().unwrap();
        m.get_mut().bound_space(value, 4);
        *s += &format!("\tsw a0, {}(sp)\n", m.get_mut().get_space(value).unwrap());
    }
    fn return_gen(&self, s: &mut String, ret: &Return, value: Value) {
        if let Some(val) = ret.value() {
            let a = self.dfg().value(val);
            let b = a.kind();
            let mut g = global_reg_allocator.lock().unwrap();
            let mut r = g.borrow_mut().get_mut();
            match b {
                ValueKind::Integer(i) =>
                    *s += &format!("\tli a0, {}\n", i.value()),
                _ => *s += &format!("\tlw a0, {}(sp)\n", r.get_space(val).unwrap()),
            }
        }
    }
    fn bin_gen(&self, s: &mut String, bin: &Binary, value: Value) {
        let r_value = bin.rhs();
        let l_value = bin.lhs();
        let mut r_s = "".to_string();
        let mut l_s = "".to_string();
        let op = bin.op();
        let mut bin_operation = "".to_string();
        let mut g = global_reg_allocator.lock().unwrap();
        let mut r = g.borrow_mut().get_mut();
        let idx = r.alloc_reg().unwrap();
        let size = self.dfg().value(value).ty().size() as i32;
        r.bound_space(value, size);
        let mut tmp_r:i32 = 0;
        let mut tmp_l:i32 = 0;
        if let ValueKind::Integer(i) = self.dfg().value(r_value).kind(){
            if(i.value() == 0) {
                r_s = format!("x0");
            } else {
                tmp_r = r.alloc_reg().unwrap();
                *s += &format!("\tli t{}, {}\n", tmp_r,i.value());
                r_s = format!("t{}", tmp_r);
            }
        } else {
            tmp_r = r.alloc_reg().unwrap();
            *s += &format!("\tlw t{}, {}(sp)\n", tmp_r, r.get_space(r_value).unwrap());
            r_s = format!("t{}", tmp_r);
        }
        if let ValueKind::Integer(i) = self.dfg().value(l_value).kind(){
            if(i.value() == 0){
                l_s = format!("x0");
            } else {
                tmp_l = r.alloc_reg().unwrap();
                *s += &format!("\tli t{}, {}\n", tmp_l, i.value());
                l_s = format!("t{}", tmp_l);
            }
        } else {
            tmp_l = r.alloc_reg().unwrap();
            *s += &format!("\tlw t{}, {}(sp)\n", tmp_l, r.get_space(l_value).unwrap());
            l_s = format!("t{}", tmp_l);
        }
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
                let tmp = r.alloc_reg().unwrap();
                *s += &format!("\txor t{}, t{}, t{}\n", tmp, tmp_l, tmp_r);
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
                let tmp = r.alloc_reg().unwrap();
                *s += &format!("\txor t{}, t{}, t{}\n", tmp, tmp_l, tmp_r);
                *s += &format!("\tsnez t{}, t{}\n", idx, tmp);
                r.free_reg(tmp);
            },
            BinaryOp::Le => {
                bin_operation = "slt".to_string();
                let tmp = r.alloc_reg().unwrap();
                let tmp1 = r.alloc_reg().unwrap();
                *s += &format!("\txor t{}, t{}, t{}\n", tmp, tmp_l, tmp_r);
                *s += &format!("\tseqz t{}, t{}\n", idx, tmp);
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, tmp1, l_s, r_s);
                *s += &format!("\tor t{}, t{}, t{}\n", idx, tmp, tmp1);
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
                let tmp = r.alloc_reg().unwrap();
                let tmp1 = r.alloc_reg().unwrap();
                *s += &format!("\txor t{}, t{}, t{}\n", tmp, tmp_l, tmp_r);
                *s += &format!("\tseqz t{}, t{}\n", idx, tmp);
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, tmp1, r_s, l_s);
                *s += &format!("\tor t{}, t{}, t{}\n", idx, tmp, tmp1);
                r.free_reg(tmp);
                r.free_reg(tmp1);
            }
            _ => bin_operation = "".to_string()
        }
        *s += &format!("\tsw t{}, {}(sp)\n", idx, r.get_space(value).unwrap());
        r.free_reg(tmp_l);
        r.free_reg(tmp_r);
        r.free_reg(idx);
    }
    fn load_gen(&self, s: &mut String, load: &Load, value: Value) {
        let src_value = load.src();
        let mut m = global_reg_allocator.lock().unwrap();
        let mut g = m.get_mut();
        let reg_idx = g.alloc_reg().unwrap();
        let size = self.dfg().value(value).ty().size() as i32;
        g.bound_space(value, size);
        let offset = g.get_space(value).unwrap();
        let src_offset = g.get_space(src_value).unwrap();
        *s += &(format!("\tlw t{}, {}(sp)\n",reg_idx, src_offset) + &format!("\tsw t{}, {}(sp)\n",
                                                                         reg_idx, offset));
        g.free_reg(reg_idx);
    }
    fn store_gen(&self, s: &mut String, store: &Store, value: Value) {
        let value = store.value();
        let dest = store.dest();
        let mut m = global_reg_allocator.lock().unwrap();
        let mut g = m.get_mut();
        let reg_idx = g.alloc_reg().unwrap();
        let offset = g.get_space(dest).unwrap();
        if let ValueKind::Integer(i) = self.dfg().value(value).kind(){
            *s += &(format!("\tli t{}, {}\n",reg_idx, i.value()) + &format!("\tsw t{}, {}(sp)\n",
                                                                             reg_idx, offset));
        } else {
            //todo 传参数
            let ty = self.dfg().value(value).kind();
            match ty{
                ValueKind::FuncArgRef(func_arg_ref) => {
                    *s += &format!("\tsw a{}, {}(sp)\n", func_arg_ref.index(), offset);
                }
                _ => {
                    let src_offset = g.get_space(value).unwrap();
                    *s += &(format!("\tlw t{}, {}(sp)\n",reg_idx, src_offset) + &format!("\tsw t{}, {}\
                        (sp)\n", reg_idx, offset));
                }
            }
        }
        g.free_reg(reg_idx);
    }
    fn alloc_gen(&self, s: &mut String, alloc: &Alloc, value: Value) {
        let size = 4;
        global_reg_allocator.lock().unwrap().get_mut().bound_space(value, size);
    }
    fn branch_gen(&self, s: &mut String, branch: &Branch, value: Value) {
        let cond = branch.cond();
        let then_branch = branch.true_bb();
        let else_branch = branch.false_bb();

        let mut k = global_reg_allocator.lock().unwrap();
        let mut g = k.get_mut();
        let reg_idx = g.borrow_mut().alloc_reg().unwrap();
        if let Some(offset) = g.borrow_mut().get_space(cond){
            *s +=  &format!("\tlw t{}, {}(sp)\n",reg_idx, offset);
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
