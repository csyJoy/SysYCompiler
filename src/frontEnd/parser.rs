use std::borrow::BorrowMut;
use crate::frontEnd::{ast, symbol_table};
use crate::frontEnd::ast::{AddExp, AddOperator, Block, BlockItem, CompUnit, ConstDecl, ConstDef, ConstExp, ConstInitVal, Decl, EqExp, EqOperation, Exp, FuncDef, FuncType, InitVal, LAndExp, LOrExp, MulExp, MulOperator, PrimaryExp, RelExp, RelOperation, Stmt, StmtType, UnaryExp, UnaryOp, UnaryOperator, VarDecl, VarDef};
use lazy_static::lazy_static;
use std::cell::{Ref, RefCell};
use std::ops::{Add, Mul};
use std::sync::Mutex;
use symbol_table::GlobalSymbolTableAllocator;
use crate::frontEnd::symbol_table::Value;

lazy_static!{
    pub static ref REG_INDEX: Mutex<RefCell<i32>> = Mutex::new(RefCell::new(0));
    pub static ref GLOBAL_SYMBOL_TABLE_ALLOCATOR: Mutex<RefCell<GlobalSymbolTableAllocator>> = Mutex::new
    (RefCell::new(GlobalSymbolTableAllocator{ now_symbol: None }));
}
pub fn add_reg_idx() -> i32{
    let mut a = REG_INDEX.lock().unwrap();
    let mut b = a.get_mut();
    *b = *b + 1;
    *b
}

pub fn get_reg_idx(name: &String) -> i32{
    let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
    let mut g = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
    if let Some(i) = g.get_var_reg(name){
        i
    } else {
        let a = REG_INDEX.lock().unwrap();
        let b = a.borrow();
        *b
    }
}

fn test(a_string: String, c_string: String, a_reg_idx: i32, c_reg_idx: i32,reg_idx: i32,
        operation: String) -> String{
    let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
    let mut g = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
    if let Ok(d) = c_string.parse::<i32>(){
        if let Ok(e) = a_string.parse::<i32>(){
            format!("\t%{} = {} {}, {}\n", reg_idx, operation,e, d)
        } else {
            if g.exist_var_symbol(&a_string){
                format!("\t%{} = {} %{}, {}\n",reg_idx, operation,
                        a_reg_idx,d)
            } else {
                a_string + &format!("\t%{} = {} %{}, {}\n",reg_idx, operation,
                                    a_reg_idx,d)
            }
        }
    } else {
        if let Ok(f) = a_string.parse::<i32>(){
            if g.exist_var_symbol(&c_string){
                format!("\t%{} = {} {}, %{}\n", reg_idx, operation, f, c_reg_idx)
            } else {
                c_string + &format!("\t%{} = {} {}, %{}\n", reg_idx, operation, f, c_reg_idx)
            }
        } else {
            let tmp = format!("\t%{} = {} %{}, %{}\n",reg_idx, operation, a_reg_idx,
                              c_reg_idx);
            let mut tmp1 = "".to_string();
            if g.exist_var_symbol(&a_string) {
                if g.exist_var_symbol(&c_string){
                    tmp1 = "".to_string();
                } else {
                    tmp1 = c_string;
                }
            } else {
                if g.exist_var_symbol(&c_string){
                    tmp1 = a_string;
                } else {
                    tmp1 = a_string + &c_string;
                }
            }
            tmp1 + &tmp
        }
    }
}

pub trait GetKoopa{
    fn get_koopa(&self) -> String;
}
pub trait EvalConst{
    fn eval_const(&self) -> Option<Value>;
}
pub trait GetName{
    fn get_name(&self) -> String;
}

impl GetKoopa for CompUnit{
    fn get_koopa(&self) -> String {
        self.func_def.get_koopa()
    }
}

impl GetKoopa for FuncDef{
    fn get_koopa(&self) -> String {
        let typ: &str;
        match self.func_type{
            FuncType::Int => {
                typ = "i32";
            }
        }
        format!("fun @{}(): {} ", &self.id, typ).to_string() + &self.block.get_koopa()
    }
}

impl GetKoopa for Block {
    fn get_koopa(&self) -> String {
        {
            let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
            let mut g = m.borrow_mut().get_mut();
            g.allocate_symbol_table();
        }
        let s = format!("{{\n").to_string() + &format!("%entry:\n") + &self.block_item.get_koopa() +
            &format!("}}\n");
        return s;
    }
}

impl GetKoopa for Vec<BlockItem>{
    fn get_koopa(&self) -> String {
        let mut s = "".to_string();
        for v in self{
            s += &v.get_koopa();
        }
        s
    }
}

impl GetKoopa for BlockItem{
    fn get_koopa(&self) -> String {
        if let Some(decl) = &self.decl{
            decl.get_koopa()
        } else if let Some(stmt) = &self.stmt{
            stmt.get_koopa()
        } else {
            "".to_string()
        }
    }
}


impl GetKoopa for Stmt{
    fn get_koopa(&self) -> String {
        match &self.stmt_type{
            StmtType::Return(exp) => {
                let a = exp.eval_const();
                if let Some(Value::Int(i)) = a{
                    return format!("\tret {}\n", i);
                } else {
                    let exp_string = exp.get_koopa();
                    let exp_reg_idx = get_reg_idx(&exp_string);
                    if let Ok(c) = exp_string.parse::<i32>(){
                        return format!("\tret {}\n", c);
                    } else {
                        exp_string + &format!("\tret %{}\n", exp_reg_idx)
                    }
                }
            }
            StmtType::Assign((ident, exp)) => {
                let s1 = format!("\t%{} = load @{}\n", add_reg_idx(), ident.ident);
                let s2 = exp.get_koopa();
                let s3 = format!("\tstore %{}, @{}\n",get_reg_idx(&s2), ident.ident);
                s1 + &s2 + &s3
            }
            _ => "ParserError".to_string()
        }
    }
}

impl GetKoopa for Exp{
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.exp{
            a.get_koopa()
        } else {
            "".to_string()
        }
    }
}
impl EvalConst for Exp{
    fn eval_const(&self) -> Option<Value> {
        self.exp.as_ref().unwrap().eval_const()
    }
}

impl GetKoopa for UnaryExp{
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.primary_exp{
            a.get_koopa()
        }  else {
            let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
            let mut go = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
            if let Some((a,b))  = &self.unary_exp{
                let g = &a.unary_op;
                match g{
                    UnaryOperator::Add => {
                        let mut s = b.get_koopa();
                        if let Ok(c) = s.parse::<i32>(){
                            let reg_idx = add_reg_idx();
                            format!("\t%{} = add 0, {}\n",reg_idx, c)
                        } else {
                            let reg_idxx = get_reg_idx(&s);
                            if go.exist_var_symbol(&s){
                                let reg_idx = add_reg_idx();
                                format!("\t%{} = add 0, %{}\n",reg_idx, reg_idxx)
                            } else {
                                let reg_idx = add_reg_idx();
                                s + &format!("\t%{} = add 0, %{}\n", reg_idx, reg_idxx)
                            }
                        }
                    }
                    UnaryOperator::Sub => {
                        let mut s = b.get_koopa();
                        if let Ok(c) = s.parse::<i32>(){
                            let reg_idx = add_reg_idx();
                            format!("\t%{} = sub 0, {}\n",reg_idx, c)
                        } else {
                            let reg_idxx = get_reg_idx(&s);
                            if go.exist_var_symbol(&s){
                                let reg_idx = add_reg_idx();
                                s + &format!("\t%{} = sub 0, %{}\n", reg_idx, reg_idxx)
                            } else {
                                let reg_idx = add_reg_idx();
                                s + &format!("\t%{} = sub 0, %{}\n", reg_idx, reg_idxx)
                            }
                        }
                    }
                    UnaryOperator::False => {
                        let mut s = b.get_koopa();
                        if let Ok(c) = s.parse::<i32>(){
                            let reg_idx = add_reg_idx();
                            format!("\t%{} = eq {}, 0\n",reg_idx, c)
                        } else {
                            let reg_idxx = get_reg_idx(&s);
                            if go.exist_var_symbol(&s){
                                let reg_idx = add_reg_idx();
                                format!("\t%{} = eq %{}, 0\n", reg_idx, reg_idxx)
                            } else {
                                let reg_idx = add_reg_idx();
                                s + &format!("\t%{} = eq %{}, 0\n", reg_idx, reg_idxx)
                            }
                        }
                    }
                    _ => "".to_string()
                }
            } else {
                "".to_string()
            }
        }
    }
}

impl PrimaryExp{
    fn is_num(&self) -> bool{
        if let Some(_) = self.exp{
            false
        } else {
            true
        }
    }
}

impl GetKoopa for PrimaryExp{
    fn get_koopa(&self) -> String {
       if let Some(a) = &self.exp{
            a.get_koopa()
       }  else {
           if let Some(a) = self.num{
                format!("{}", a)
           } else if let Some(a) = &self.lval{
               let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
               let mut g  = m.borrow_mut().get_mut();
               if g.now_symbol.as_ref().unwrap().lock().unwrap().exist_const_symbol(&a.ident){
                    format!("{}", g.now_symbol.as_ref().unwrap().lock().unwrap().get_const_value(&a
                        .ident))
               } else {
                   "".to_string()
               }
           } else {
               "".to_string()
           }
       }
    }
}

impl GetKoopa for MulExp{
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.unary_exp{
            a.get_koopa()
        } else {
            if let Some((a,b,c)) = &self.mul_operate{
                let mut operation = "".to_string();
                match b{
                    MulOperator::Divide => operation = "div".to_string(),
                    MulOperator::Times => operation = "mul".to_string(),
                    MulOperator::Quote => operation = "mod".to_string(),
                    _ => operation = "".to_string()
                }
                let a_string = a.get_koopa();
                let a_reg_idx = get_reg_idx(&a_string);
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx(&a_string);
                let e = add_reg_idx();
                test(a_string, c_string, a_reg_idx, c_reg_idx, e, operation)
            } else {
                "ParserError".to_string()
            }
        }
    }
}

impl GetKoopa for AddExp{
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.mul_exp{
            a.get_koopa()
        } else {
            if let Some((a, b ,c)) = &self.add_operate{
                let mut operation = "".to_string();
                match b{
                    AddOperator::Add => operation = "add".to_string(),
                    AddOperator::Sub => operation = "sub".to_string(),
                    _ => operation = "".to_string(),
                }
                let a_string = a.get_koopa();
                let a_reg_idx = get_reg_idx(&a_string);
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx(&c_string);
                let reg_idx = add_reg_idx();
                test(a_string, c_string, a_reg_idx, c_reg_idx, reg_idx, operation)
            } else {
                "ParserError".to_string()
            }
        }
    }
}

impl GetKoopa for RelExp {
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.add_exp{
            a.get_koopa()
        } else {
            if let Some((a, b ,c)) = &self.rel_operate{
                let mut operation = "".to_string();
                match b{
                    RelOperation::Less => operation = "lt".to_string(),
                    RelOperation::LessEq => operation = "le".to_string(),
                    RelOperation::Greater => operation = "gt".to_string(),
                    RelOperation::GreaterEq => operation = "ge".to_string(),
                    _ => operation = "".to_string(),
                }
                let a_string = a.get_koopa();
                let a_reg_idx = get_reg_idx(&a_string);
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx(&c_string);
                let reg_idx = add_reg_idx();
                test(a_string, c_string, a_reg_idx, c_reg_idx, reg_idx, operation)
            } else {
                "ParserError".to_string()
            }
        }
    }
}

impl GetKoopa for EqExp {
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.rel_exp{
            a.get_koopa()
        } else {
            if let Some((a, b ,c)) = &self.eq_operate{
                let mut operation = "".to_string();
                match b{
                    EqOperation::Eq => operation = "eq".to_string(),
                    EqOperation::NEq => operation = "ne".to_string(),
                    _ => operation = "".to_string(),
                }
                let a_string = a.get_koopa();
                let a_reg_idx = get_reg_idx(&a_string);
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx(&c_string);
                let reg_idx = add_reg_idx();
                test(a_string, c_string, a_reg_idx, c_reg_idx, reg_idx, operation)
            } else {
                "ParserError".to_string()
            }
        }
    }
}

impl GetKoopa for LAndExp{
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.eq_exp{
            a.get_koopa()
        } else {
            if let Some((a, c )) = &self.land_operate{
                let mut operation = "and".to_string();
                let a_string = a.get_koopa();
                let a_reg_idx = get_reg_idx(&a_string);
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx(&c_string);
                let e_reg = add_reg_idx();
                let d_reg = add_reg_idx();
                let reg_idx = add_reg_idx();
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
                if let Ok(d) = c_string.parse::<i32>(){
                    if let Ok(e) = a_string.parse::<i32>(){
                        let s1 = format!("\t%{} = ne 0, {}\n",e_reg, e);
                        let s2 = format!("\t%{} = ne 0, {}\n",d_reg, d);
                        s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx, operation,e_reg, d_reg) }
                    else {
                        let s1 = format!("\t%{} = ne 0, %{}\n",e_reg, a_reg_idx);
                        let s2 = format!("\t%{} = ne 0, {}\n",d_reg, d);
                        if g.exist_var_symbol(&a_string){
                            s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                        } else {
                            a_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                        }
                    }
                } else {
                    if let Ok(e) = a_string.parse::<i32>(){
                        let s1 = format!("\t%{} = ne 0, {}\n",e_reg, e);
                        let s2 = format!("\t%{} = ne 0, %{}\n",d_reg, c_reg_idx);
                        if g.exist_var_symbol(&c_string){
                            s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                        } else {
                            c_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                        }
                    } else {
                        let s1 = format!("\t%{} = ne 0, %{}\n",e_reg, a_reg_idx);
                        let s2 = format!("\t%{} = ne 0, %{}\n",d_reg, c_reg_idx);
                        if g.exist_var_symbol(&c_string){
                            if g.exist_var_symbol(&a_string){
                                s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                                                     e_reg, d_reg)
                            } else {
                                a_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                                                                e_reg, d_reg)
                            }
                        } else {
                            if g.exist_var_symbol(&a_string){
                                c_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                                                                 e_reg, d_reg)
                            } else {
                                a_string + &c_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                                                                            e_reg, d_reg)
                            }
                        }
                    }
                }
            } else {
                "ParserError".to_string()
            }
        }
    }
}

impl GetKoopa for LOrExp{
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.land_exp{
            a.get_koopa()
        } else {
            if let Some((a, c )) = &self.lor_operate{
                let mut operation = "or".to_string();
                let a_string = a.get_koopa();
                let a_reg_idx = get_reg_idx(&a_string);
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx(&c_string);
                let e_reg = add_reg_idx();
                let d_reg = add_reg_idx();
                let reg_idx = add_reg_idx();
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
                if let Ok(d) = c_string.parse::<i32>(){
                    if let Ok(e) = a_string.parse::<i32>(){
                        let s1 = format!("\t%{} = ne 0, {}\n",e_reg, e);
                        let s2 = format!("\t%{} = ne 0, {}\n",d_reg, d);
                        s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx, operation,e_reg, d_reg)
                    } else {
                        let s1 = format!("\t%{} = ne 0, %{}\n",e_reg, a_reg_idx);
                        let s2 = format!("\t%{} = ne 0, {}\n",d_reg, d);
                        if g.exist_var_symbol(&a_string){
                            s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                        } else {
                            a_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                        }
                    }
                } else {
                    if let Ok(e) = a_string.parse::<i32>(){
                        let s1 = format!("\t%{} = ne 0, {}\n",e_reg, e);
                        let s2 = format!("\t%{} = ne 0, %{}\n",d_reg, c_reg_idx);
                        if g.exist_var_symbol(&c_string){
                            s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                        } else {
                            c_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                        }
                    } else {
                        let s1 = format!("\t%{} = ne 0, %{}\n",e_reg, a_reg_idx);
                        let s2 = format!("\t%{} = ne 0, %{}\n",d_reg, c_reg_idx);
                        if g.exist_var_symbol(&c_string){
                            if g.exist_var_symbol(&a_string){
                                s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                                                    e_reg, d_reg)
                            } else {
                                a_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                                                                e_reg, d_reg)
                            }
                        } else {
                            if g.exist_var_symbol(&a_string){
                                c_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                                                                e_reg, d_reg)
                            } else {
                                a_string + &c_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                                                                            e_reg, d_reg)
                            }
                        }
                    }
                }
            } else {
                "ParserError".to_string()
            }
        }
    }
}
impl GetKoopa for Decl{
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.const_decl{
            a.get_koopa()
        } else if let Some(b) = &self.var_decl{
            b.get_koopa()
        } else {
            "".to_string()
        }
    }
}

impl GetKoopa for VarDecl{
    fn get_koopa(&self) -> String {
        let mut s = "".to_string();
        s += &self.var_def.get_koopa();
        for var in &self.var_def_vec{
            s += &var.get_koopa();
        }
        s
    }
}

impl GetKoopa for VarDef{
    fn get_koopa(&self) -> String {
        let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
        let mut g = m.borrow_mut().get_mut();
        let s = self.get_name();
        if let Some(i) = &self.initval{
            let mut k = i.get_koopa();
            if let Ok(l)= k.parse::<i32>(){
                g.now_symbol.as_mut().unwrap().lock().unwrap().insert_var_symbol(s, Some(l));
                format!("\t@{} = alloc {}\n",self.get_name(), "i32")
                    + &format!("\tstore {}, @{}\n",l, self.get_name())
            } else {
                g.now_symbol.as_mut().unwrap().lock().unwrap().insert_var_symbol((&s).to_string(),
                                                                                  None);
                (&s).to_string() + &format!("\t@{} = alloc {}\n",self.get_name(), "i32")
                    + &format!("\tstore %{}, @{}\n",get_reg_idx(&s), self.get_name())
            }
        } else {
            g.now_symbol.as_mut().unwrap().lock().unwrap().insert_var_symbol(s, None);
            format!("\t@{} = alloc {}\n",self.get_name(), "i32")
        }
    }
}

impl GetName for VarDef{
    fn get_name(&self) -> String {
        (&self.ident).to_string()
    }
}

impl GetKoopa for InitVal{
    fn get_koopa(&self) -> String {
        let a = self.exp.eval_const().unwrap();
        if let Value::Int(i) = a {

            format!("{}", i)
        } else {
            self.exp.get_koopa()
        }
    }
}

impl GetKoopa for ConstDecl{
    fn get_koopa(&self) -> String {
        let a = self.const_def.eval_const().unwrap();
        let Value::Int(i) = a;
        let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
        let mut g = m.borrow_mut().get_mut();
        let s = self.const_def.get_name();
        g.now_symbol.as_mut().unwrap().lock().unwrap().insert_const_symbol(s, i);
        "".to_string()
    }
}

impl EvalConst for ConstDef{
    fn eval_const(&self) -> Option<Value> {
        let a = self.const_init_val.const_exp.exp.exp.as_ref().unwrap();
        a.eval_const()
    }
}
impl GetName for ConstDef{
    fn get_name(&self) -> String {
        (&self.ident).to_string()
    }
}
impl EvalConst for LOrExp{
    fn eval_const(&self) -> Option<Value> {
        if let a = self.land_exp.as_ref().unwrap().eval_const(){
            a
        } else if let Some((lor, land)) = &self.lor_operate{
            let lor_val = lor.eval_const();
            if let Some(v1) = lor_val{
                if let Some(v2) = land.eval_const(){
                    let Value::Int(i1) = v1;
                    let Value::Int(i2) = v2;
                    return Some(Value::Int(if i1 != 0 || i2 != 0 {1} else {0}));
                } else {
                    return None;
                }
            } else {
                return None;
            }
        } else {
            return None;
        }
    }
}

impl EvalConst for LAndExp{
    fn eval_const(&self) -> Option<Value> {
        if let a = self.eq_exp.as_ref().unwrap().eval_const(){
            a
        } else if let Some((land, eq)) = &self.land_operate{
            let land_val = land.eval_const();
            if let Some(v1) = land_val{
                if let Some(v2) = eq.eval_const(){
                    let Value::Int(i1) = v1;
                    let Value::Int(i2) = v2;
                    return Some(Value::Int(if i1 != 0 && i2 != 0{1} else {0}));
                } else {
                    return None;
                }
            } else {
                return None;
            }
        } else {
            return None;
        }
    }
}

impl EvalConst for EqExp{
    fn eval_const(&self) -> Option<Value> {
        if let a = self.rel_exp.as_ref().unwrap().eval_const(){
            a
        } else if let Some((eq, op, rel)) = &self.eq_operate{
            let eq_val = eq.eval_const();
            if let Some(v1) = eq_val{
                if let Some(v2) = rel.eval_const(){
                    let Value::Int(i1) = v1;
                    let Value::Int(i2) = v2;
                    match op{
                        EqOperation::Eq => return Some(Value::Int(if i1 == i2 {1} else {0})),
                        EqOperation::NEq => return Some(Value::Int(if i1 != i2 {1} else {0})),
                        _ => return None,
                    }
                } else {
                    return None;
                }
            } else {
                return None;
            }
        } else {
            return None;
        }
    }
}

impl EvalConst for RelExp{
    fn eval_const(&self) -> Option<Value> {
        if let a = self.add_exp.as_ref().unwrap().eval_const(){
            a
        } else if let Some((rel, op, add)) = &self.rel_operate{
            let rel_val = rel.eval_const();
            if let Some(v1) = rel_val{
                if let Some(v2) = add.eval_const(){
                    let Value::Int(i1) = v1;
                    let Value::Int(i2) = v2;
                    match op{
                        RelOperation::Greater => return Some(Value::Int(if i1 > i2 {1} else {0})),
                        RelOperation::Less => return Some(Value::Int(if i1 < i2 {1} else {0})),
                        RelOperation::LessEq => return Some(Value::Int(if i1 <= i2 {1} else {0})),
                        RelOperation::GreaterEq => return Some(Value::Int(if i1 >= i2 {1} else
                        {0})),
                        _ => return None,
                    }
                } else {
                    return None;
                }
            } else {
                return None;
            }
        } else {
            return None;
        }
    }
}

impl EvalConst for AddExp{
    fn eval_const(&self) -> Option<Value> {
        if let a = self.mul_exp.as_ref().unwrap().eval_const(){
            a
        } else if let Some((add_exp, op, mul_exp)) = &self.add_operate{
            let add_val = add_exp.eval_const();
            if let Some(v1) = add_val{
                if let Some(v2) = mul_exp.eval_const(){
                    let Value::Int(i1) = v1;
                    let Value::Int(i2) = v2;
                    match op{
                        AddOperator::Add => return Some(Value::Int(i1 + i2)),
                        AddOperator::Sub => return Some(Value::Int(i1 - i2)),
                        _ => return None,
                    }
                } else {
                    return None;
                }
            } else {
                return None;
            }
        } else {
            return None;
        }
    }
}

impl EvalConst for MulExp{
    fn eval_const(&self) -> Option<Value> {
        if let Some(exp) = &self.unary_exp{
            exp.eval_const()
        } else if let Some((mul, op, un)) = &self.mul_operate{
            let mul_val = mul.eval_const();
            if let Some(v1) = mul_val{
                if let Some(v2) = un.eval_const(){
                    let Value::Int(i1) = v1;
                    let Value::Int(i2) = v2;
                    match op{
                        MulOperator::Times => return Some(Value::Int(i1 * i2)),
                        MulOperator::Divide => return Some(Value::Int(i1 / i2)),
                        MulOperator::Quote => return Some(Value::Int(i1 % i2)),
                        _ => return None,
                    }
                } else {
                    return None;
                }
            } else {
                return None;
            }
        } else {
            return None;
        }
    }
}

impl EvalConst for UnaryExp{
    fn eval_const(&self) -> Option<Value> {
        if let Some(exp) = &self.primary_exp{
            exp.eval_const()
        } else if let Some((op, exp))  = &self.unary_exp{
            let mut tmp:Option<Value>;
            match op.unary_op{
                UnaryOperator::Add => tmp = exp.eval_const(),
                UnaryOperator::False => {
                    if let Some(v) = exp.eval_const(){
                        match v{
                            Value::Int(i) => {
                                if i == 0{
                                    tmp = Some(Value::Int(0));
                                } else {
                                    tmp = Some(Value::Int(1));
                                }
                            },
                            _ => tmp = None
                        }
                    } else {
                        tmp = None;
                    }
                } ,
                UnaryOperator::Sub => {
                    if let Some(v) = exp.eval_const(){
                        match v{
                            Value::Int(i) => tmp = Some(Value::Int(-i)),
                            _ => tmp = None,
                        }
                    } else {
                        tmp = None;
                    }
                },
                _ => tmp = None,
            }
            return tmp;
        } else {
            return None;
        }
    }
}

impl EvalConst for PrimaryExp{
    fn eval_const(&self) -> Option<Value> {
        if let Some(n) = self.num{
            Some(Value::Int(n))
        } else {
            if let Some(tmp) = &self.lval{
                let mut g = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let i = g.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap()
                    .get_const_value(&tmp.ident);
                return Some(Value::Int(i))
            } else {
                None
            }
        }
    }
}