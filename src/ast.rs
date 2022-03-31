use std::cell::RefCell;
use lazy_static::lazy_static;
use std::sync::Mutex;
use crate::ast::AddOperator::Add;

pub type int = i32;
pub trait GetKoopa{
    fn get_koopa(&self) -> String;
}
lazy_static!{
    static ref REG_INDEX: Mutex<RefCell<i32>> = Mutex::new(RefCell::new(0));
}
pub fn add_reg_idx() -> i32{
    let a = REG_INDEX.lock().unwrap();
    let mut b = a.borrow_mut();
    *b = *b + 1;
    *b
}
pub fn get_reg_idx() -> i32{
    let a = REG_INDEX.lock().unwrap();
    let b = a.borrow();
    *b
}

#[derive(Debug)]
pub struct CompUnit{
    pub func_def: FuncDef,
}
impl GetKoopa for CompUnit{
    fn get_koopa(&self) -> String {
        self.func_def.get_koopa()
    }
}

#[derive(Debug)]
pub struct FuncDef {
    pub func_type: FuncType,
    pub id: String,
    pub block: Block,
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


#[derive(Debug)]
pub enum  FuncType{
    Int,
}

#[derive(Debug)]
pub struct Block{
    pub stmt: Stmt,
}

impl GetKoopa for Block {
    fn get_koopa(&self) -> String {
        format!("{{\n").to_string() + &format!("%entry:\n") + &self.stmt.get_koopa() + &format!
        ("}}\n")
    }
}
#[derive(Debug)]
pub enum StmtType{
    Return(Exp),
}
#[derive(Debug)]
pub struct Stmt{
    pub stmt_type: StmtType,
}
impl GetKoopa for Stmt{
    fn get_koopa(&self) -> String {
        match &self.stmt_type{
            StmtType::Return(exp) => {
                let exp_string = exp.get_koopa();
                let exp_reg_idx = get_reg_idx();
                if let Ok(c) = exp_string.parse::<i32>(){
                    format!("\tret {}\n", c)
                } else {
                    exp_string + &format!("\tret %{}\n", exp_reg_idx)
                }
            }
            _ => "ParserError".to_string()
        }
    }
}

#[derive(Debug)]
pub struct Exp{
    pub exp: Option<Box<LOrExp>>
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

#[derive(Debug)]
pub struct UnaryExp{
    pub primary_exp: Option<Box<PrimaryExp>>,
    pub unary_exp: Option<(UnaryOp, Box<UnaryExp>)>
}
impl GetKoopa for UnaryExp{
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.primary_exp{
            a.get_koopa()
        }  else {
            if let Some((a,b))  = &self.unary_exp{
                let g = &a.unary_op;
                match g{
                    UnaryOperator::Add => {
                        let mut s = b.get_koopa();
                        if let Ok(c) = s.parse::<i32>(){
                            let reg_idx = get_reg_idx();
                            format!("\t%{} = add 0, {}\n",reg_idx, c)
                        } else {
                            let reg_idx = add_reg_idx();
                            s + &format!("\t%{} = add 0, %{}\n", reg_idx, reg_idx - 1)
                        }
                    }
                    UnaryOperator::Sub => {
                        let mut s = b.get_koopa();
                        if let Ok(c) = s.parse::<i32>(){
                            let reg_idx = add_reg_idx();
                            format!("\t%{} = sub 0, {}\n",reg_idx, c)
                        } else {
                            let reg_idx = add_reg_idx();
                            s + &format!("\t%{} = sub 0, %{}\n", reg_idx, reg_idx - 1)
                        }
                    }
                    UnaryOperator::False => {
                        let mut s = b.get_koopa();
                        if let Ok(c) = s.parse::<i32>(){
                            let reg_idx = get_reg_idx();
                            format!("\t%{} = eq {}, 0\n",reg_idx, c)
                        } else {
                            let reg_idx = add_reg_idx();
                            s + &format!("\t%{} = eq %{}, 0\n", reg_idx, reg_idx - 1)
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

#[derive(Debug)]
pub struct PrimaryExp{
    pub exp: Option<Box<Exp>>,
    pub num: Option<int>
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
           } else {
               "".to_string()
           }
       }
    }
}
#[derive(Debug)]
pub enum UnaryOperator{
    Add,
    Sub,
    False,
}
#[derive(Debug)]
pub struct UnaryOp{
    pub unary_op: UnaryOperator
}

#[derive(Debug)]
pub enum MulOperator{
    Times,
    Divide,
    Quote
}

#[derive(Debug)]
pub struct MulExp{
    pub unary_exp: Option<Box<UnaryExp>>,
    pub mul_operate: Option<(Box<MulExp>,MulOperator,Box<UnaryExp>)>,
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
                let a_reg_idx = get_reg_idx();
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx();
                let e = add_reg_idx();
                if let Ok(d) = c_string.parse::<i32>(){
                    if let Ok(f) = a_string.parse::<i32>(){
                        format!("\t%{} = {} {}, {}\n", e, operation, f, d)
                    } else {
                        a_string + &format!("\t%{} = {} %{}, {}\n",e, operation,
                                                        a_reg_idx,d)
                    }
                } else {
                    if let Ok(f) = a_string.parse::<i32>(){
                        c_string + &format!("\t%{} = {} {}, %{}\n", e, operation, f, c_reg_idx)
                    } else {
                        a_string + &c_string + &format!("\t%{} = {} %{}, %{}\n",e, operation,
                                                        a_reg_idx,c_reg_idx)
                    }
                }
            } else {
                "ParserError".to_string()
            }
        }
    }
}

#[derive(Debug)]
pub enum AddOperator{
    Add,
    Sub
}
#[derive(Debug)]
pub struct AddExp{
    pub mul_exp: Option<Box<MulExp>>,
    pub add_operate: Option<(Box<AddExp>, AddOperator, Box<MulExp>)>
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
                let a_reg_idx = get_reg_idx();
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx();
                let reg_idx = add_reg_idx();
                if let Ok(d) = c_string.parse::<i32>(){
                    if let Ok(e) = a_string.parse::<i32>(){
                        format!("\t%{} = {} {}, {}\n", reg_idx, operation,e, d)
                    } else {
                        a_string + &format!("\t%{} = {} %{}, {}\n", reg_idx,operation, a_reg_idx, d)
                    }
                } else {
                    if let Ok(e) = a_string.parse::<i32>(){
                        c_string + &format!("\t%{} = {} {}, %{}\n", reg_idx,operation, e, c_reg_idx)
                    } else {
                        a_string + &c_string + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                                                        a_reg_idx, c_reg_idx)
                    }
                }
            } else {
                "ParserError".to_string()
            }
        }
    }
}

#[derive(Debug)]
pub enum RelOperation{
    Less,
    Greater,
    LessEq,
    GreaterEq
}

#[derive(Debug)]
pub struct RelExp{
    pub add_exp: Option<Box<AddExp>>,
    pub rel_operate: Option<(Box<RelExp>, RelOperation, Box<AddExp>)>
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
                let a_reg_idx = get_reg_idx();
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx();
                let reg_idx = add_reg_idx();
                if let Ok(d) = c_string.parse::<i32>(){
                    if let Ok(e) = a_string.parse::<i32>(){
                        format!("\t%{} = {} {}, {}\n", reg_idx, operation,e, d)
                    } else {
                        a_string + &format!("\t%{} = {} %{}, {}\n", reg_idx,operation, a_reg_idx, d)
                    }
                } else {
                    if let Ok(e) = a_string.parse::<i32>(){
                        c_string + &format!("\t%{} = {} {}, %{}\n", reg_idx,operation, e, c_reg_idx)
                    } else {
                        a_string + &c_string + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                                                        a_reg_idx, c_reg_idx)
                    }
                }
            } else {
                "ParserError".to_string()
            }
        }
    } 
}

#[derive(Debug)]
pub enum EqOperation{
    Eq,
    NEq
}

#[derive(Debug)]
pub struct EqExp{
    pub rel_exp: Option<Box<RelExp>>,
    pub eq_operate: Option<(Box<EqExp>, EqOperation, Box<RelExp>)>
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
                let a_reg_idx = get_reg_idx();
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx();
                let reg_idx = add_reg_idx();
                if let Ok(d) = c_string.parse::<i32>(){
                    if let Ok(e) = a_string.parse::<i32>(){
                        format!("\t%{} = {} {}, {}\n", reg_idx, operation,e, d)
                    } else {
                        a_string + &format!("\t%{} = {} %{}, {}\n", reg_idx,operation, a_reg_idx, d)
                    }
                } else {
                    if let Ok(e) = a_string.parse::<i32>(){
                        c_string + &format!("\t%{} = {} {}, %{}\n", reg_idx,operation, e, c_reg_idx)
                    } else {
                        a_string + &c_string + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                                                        a_reg_idx, c_reg_idx)
                    }
                }
            } else {
                "ParserError".to_string()
            }
        }
    }
}

#[derive(Debug)]
pub struct LAndExp{
    pub eq_exp: Option<Box<EqExp>>,
    pub land_operate:  Option<(Box<LAndExp>, Box<EqExp>)>
}
impl GetKoopa for LAndExp{
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.eq_exp{
            a.get_koopa()
        } else {
            if let Some((a, c )) = &self.land_operate{
                let mut operation = "and".to_string();
                let a_string = a.get_koopa();
                let a_reg_idx = get_reg_idx();
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx();
                let e_reg = add_reg_idx();
                let d_reg = add_reg_idx();
                let reg_idx = add_reg_idx();
                if let Ok(d) = c_string.parse::<i32>(){
                    if let Ok(e) = a_string.parse::<i32>(){
                        let s1 = format!("\t%{} = ne 0, {}\n",e_reg, e);
                        let s2 = format!("\t%{} = ne 0, {}\n",d_reg, d);
                        s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx, operation,e_reg, d_reg) }
                    else {
                        let s1 = format!("\t%{} = ne 0, %{}\n",e_reg, a_reg_idx);
                        let s2 = format!("\t%{} = ne 0, {}\n",d_reg, d);
                        a_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                    }
                } else {
                    if let Ok(e) = a_string.parse::<i32>(){
                        let s1 = format!("\t%{} = ne 0, {}\n",e_reg, e);
                        let s2 = format!("\t%{} = ne 0, %{}\n",d_reg, c_reg_idx);
                        c_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                    } else {
                        let s1 = format!("\t%{} = ne 0, %{}\n",e_reg, a_reg_idx);
                        let s2 = format!("\t%{} = ne 0, %{}\n",d_reg, c_reg_idx);
                        a_string + &c_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                                                        e_reg, d_reg)
                    }
                }
            } else {
                "ParserError".to_string()
            }
        }
    }
}

#[derive(Debug)]
pub struct LOrExp{
    pub land_exp: Option<Box<LAndExp>>,
    pub lor_operate: Option<(Box<LOrExp>, Box<LAndExp>)>
}

impl GetKoopa for LOrExp{
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.land_exp{
            a.get_koopa()
        } else {
            if let Some((a, c )) = &self.lor_operate{
                let mut operation = "or".to_string();
                let a_string = a.get_koopa();
                let a_reg_idx = get_reg_idx();
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx();
                let e_reg = add_reg_idx();
                let d_reg = add_reg_idx();
                let reg_idx = add_reg_idx();
                if let Ok(d) = c_string.parse::<i32>(){
                    if let Ok(e) = a_string.parse::<i32>(){
                        let s1 = format!("\t%{} = ne 0, {}\n",e_reg, e);
                        let s2 = format!("\t%{} = ne 0, {}\n",d_reg, d);
                        s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx, operation,e_reg, d_reg)
                    } else {
                        let s1 = format!("\t%{} = ne 0, %{}\n",e_reg, a_reg_idx);
                        let s2 = format!("\t%{} = ne 0, {}\n",d_reg, d);
                        a_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                    }
                } else {
                    if let Ok(e) = a_string.parse::<i32>(){
                        let s1 = format!("\t%{} = ne 0, {}\n",e_reg, e);
                        let s2 = format!("\t%{} = ne 0, %{}\n",d_reg, c_reg_idx);
                        c_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                    } else {
                        let s1 = format!("\t%{} = ne 0, %{}\n",e_reg, a_reg_idx);
                        let s2 = format!("\t%{} = ne 0, %{}\n",d_reg, c_reg_idx);
                        a_string + &c_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                                                                    e_reg, d_reg)
                    }
                }
            } else {
                "ParserError".to_string()
            }
        }
    }
}
