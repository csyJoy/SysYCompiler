//use koopa::ir::{BinaryOp, FunctionData, Program, Value, ValueKind};
use koopa::ir::values::{Binary, Return, BinaryOp, Alloc, Store, Load, Branch, Jump};
use lazy_static::lazy_static;
use std::sync::Mutex;
use std::cell::RefCell;
use std::collections::HashMap;
use koopa::ir::entities::{Value, Program, FunctionData, ValueKind, ValueData};
use crate::frontEnd::GlobalSymbolTableAllocator;

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

    fn bound_space(&mut self, value: Value);
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
    fn bound_space(&mut self, value: Value){
        self.map.insert(value, self.offset);
        self.offset += 4;
    }
    fn get_space(&self, value: Value) -> Option<i32> {
        Some(*self.map.get(&value).unwrap())
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

fn calculate_and_allocate_space(this: &FunctionData) -> i32{
    let mut bits:i32 = 0;
    for (&bb, node) in this.layout().bbs(){
        for &inst in node.insts().keys(){
            let value_data = this.dfg().value(inst);
            if !value_data.ty().is_unit(){
                bits = bits + 4;
            }
        }
    }
    bits
}

impl GenerateAsm for FunctionData{
    fn generate(&self) -> String {
        let mut s = "".to_string();
        s += &format!("{}:\n", &self.name().to_string()[1..]);
        let sp = calculate_and_allocate_space(self);
        s += &format!("\taddi sp, sp, -{}\n",sp);
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
                    _ => unreachable!(),
                }
            }
            if let Some(data) = self.dfg().bbs().get(&bb){
                if let Some(a) = &data.name(){
                    if a == "%end"{
                        s += &format!("\taddi sp, sp, {}\n",sp);
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
}
impl splitGen for FunctionData {
    fn return_gen(&self, s: &mut String, ret: &Return, value: Value) {
        if let Some(val) = ret.value() {
            let a = self.dfg().value(val);
            let b = a.kind();
            let mut g = global_reg_allocator.lock().unwrap();
            let mut r = g.borrow_mut();
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
        let g = global_reg_allocator.lock().unwrap();
        let mut r = g.borrow_mut();
        let idx = r.alloc_reg().unwrap();
        r.bound_space(value);
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
        g.bound_space(value);
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
        g.bound_space(dest);
        let offset = g.get_space(dest).unwrap();
        if let ValueKind::Integer(i) = self.dfg().value(value).kind(){
            *s += &(format!("\tli t{}, {}\n",reg_idx, i.value()) + &format!("\tsw t{}, {}(sp)\n",
                                                                             reg_idx, offset));
        } else {
            let src_offset = g.get_space(value).unwrap();
            *s += &(format!("\tlw t{}, {}(sp)\n",reg_idx, src_offset) + &format!("\tsw t{}, {}\
            (sp)\n",
                                                                             reg_idx, offset));
        }
        g.free_reg(reg_idx);
    }
    fn alloc_gen(&self, s: &mut String, alloc: &Alloc, value: Value) {
        global_reg_allocator.lock().unwrap().get_mut().bound_space(value);
    }
    fn branch_gen(&self, s: &mut String, branch: &Branch, value: Value) {
        let cond = branch.cond();
        let then_branch = branch.true_bb();
        let else_branch = branch.false_bb();
        let g = global_reg_allocator.lock().unwrap();
        let offset = g.borrow_mut().get_space(cond).unwrap();
        let reg_idx = g.borrow_mut().alloc_reg().unwrap();
        *s +=  &format!("\tlw t{}, {}(sp)\n",reg_idx, offset);
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
