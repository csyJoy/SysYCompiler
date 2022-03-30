use koopa::ir::{BinaryOp, FunctionData, Program, Value, ValueKind};
use koopa::ir::values::{Binary, Return};
use lazy_static::lazy_static;
use std::sync::Mutex;
use std::cell::RefCell;
use std::collections::HashMap;

pub trait GenerateAsm{
    fn generate(&self) -> String;
}
pub trait RegAlloctor{
    fn alloc_reg(&mut self) -> Option<i32>;
    fn free_reg(&mut self, idx: i32) -> Option<i32>;
    fn bound_reg(&mut self, value: Value, idx: i32) -> Option<i32>;
    fn get_reg(&self, value: Value) -> Option<i32>;
}
struct GlobalRegAlloctor{
    reg_pool: Vec<i32>,
    map: HashMap<Value, i32>
}
impl GlobalRegAlloctor{
    fn new(bottom: i32, top: i32) -> GlobalRegAlloctor{
        let mut v:Vec<i32> = Vec::new();
        for i in (bottom..top+1).rev(){
            v.push(i);
        }
        GlobalRegAlloctor{ reg_pool: v, map: HashMap::new() }
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
}
lazy_static!{
    static ref global_reg_allocator: Mutex<RefCell<GlobalRegAlloctor>> = Mutex::new(RefCell::new
        (GlobalRegAlloctor::new(1, 7)));
}

impl GenerateAsm for Program{
    fn generate(&self) -> String {
        let mut head = "\t.text\n".to_string();
        let mut func_def = "".to_string();
        for &func in self.func_layout(){
            let tmp = &self.func(func).name().to_string()[1..];
            head += &format!("\t.global {}\n", tmp);
            func_def += &self.func(func).generate()
        }
        head + &func_def
    }
}

impl GenerateAsm for FunctionData{
    fn generate(&self) -> String {
        let mut s = "".to_string();
        s += &format!("{}:\n", &self.name().to_string()[1..]);
        for (&bb, node) in self.layout().bbs(){
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
                    _ => unreachable!(),
                }
            }
        }
        s
    }
}

trait splitGen{
    fn return_gen(&self, s: &mut String, ret: &Return, value: Value);
    fn bin_gen(&self, s: &mut String, bin: &Binary, value: Value);
}
impl splitGen for FunctionData {
    fn return_gen(&self, s: &mut String, ret: &Return, value: Value) {
        if let Some(val) = ret.value() {
            let a = self.dfg().value(val);
            let b = a.kind();
            let g = global_reg_allocator.lock().unwrap();
            let r = g.borrow_mut();
            match b {
                ValueKind::Integer(i) =>
                    *s += &format!("\tli a0, {}\n", i.value()),
                ValueKind::Binary(bin) => {
                    *s += &format!("\tli a0, t{}\n", r.get_reg(val).unwrap());
                }
                _ => unreachable!(),
            }
        }
        *s += &format!("\tret\n");
    }
    fn bin_gen(&self, s: &mut String, bin: &Binary, value: Value) {
        let r_value = bin.rhs();
        let l_value = bin.lhs();
        let mut r_s = "".to_string();
        let mut l_s = "".to_string();
        let op = bin.op();
        let mut bin_operation = "".to_string();
        let g = global_reg_allocator.lock().unwrap();
        let mut r = g.borrow_mut();
        let idx = r.alloc_reg().unwrap();
        r.bound_reg(value, idx);
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
            r_s = format!("t{}", r.get_reg(r_value).unwrap());
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
            l_s = format!("t{}", r.get_reg(l_value).unwrap());
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
                *s += &format!("\txor t{}, {}, {}\n", tmp, tmp_l, tmp_r);
                *s += &format!("\tseqz t{}, {}\n", idx, tmp);
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
                *s += &format!("\txor t{}, {}, {}\n", tmp, tmp_l, tmp_r);
                *s += &format!("\tsnez t{}, {}\n", idx, tmp);
                r.free_reg(tmp);
            },
            BinaryOp::Le => {
                bin_operation = "slt".to_string();
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, idx, l_s, r_s);
            },
            BinaryOp::Lt => {
                bin_operation = "slt".to_string();
                let tmp = r.alloc_reg().unwrap();
                let tmp1 = r.alloc_reg().unwrap();
                *s += &format!("\txor t{}, {}, {}\n", tmp, tmp_l, tmp_r);
                *s += &format!("\tseqz t{}, {}\n", idx, tmp);
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, tmp1, l_s, r_s);
                *s += &format!("\tor t{}, t{}, t{}\n", idx, tmp, tmp1);
                r.free_reg(tmp);
                r.free_reg(tmp1);
            },
            BinaryOp::Gt => {
                bin_operation = "slt".to_string();
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, idx, r_s, l_s);
            },
            BinaryOp::Ge =>{
                bin_operation = "slt".to_string();
                let tmp = r.alloc_reg().unwrap();
                let tmp1 = r.alloc_reg().unwrap();
                *s += &format!("\txor t{}, {}, {}\n", tmp, tmp_l, tmp_r);
                *s += &format!("\tseqz t{}, {}\n", idx, tmp);
                *s += &format!("\t{} t{}, {}, {}\n", bin_operation, tmp1, r_s, l_s);
                *s += &format!("\tor t{}, t{}, t{}\n", idx, tmp, tmp1);
                r.free_reg(tmp);
                r.free_reg(tmp1);
            }
            _ => bin_operation = "".to_string()
        }
        r.free_reg(tmp_l);
        r.free_reg(tmp_r);
    }
}
