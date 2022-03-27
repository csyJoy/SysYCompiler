use std::cell::RefCell;
use lazy_static::lazy_static;
use std::sync::Mutex;

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
pub struct Stmt{
    pub exp: Exp,
}
impl GetKoopa for Stmt{
    fn get_koopa(&self) -> String {
        self.exp.get_koopa()
    }
}

#[derive(Debug)]
pub struct Exp{
    pub exp: Option<Box<UnaryExp>>
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
                            let reg_idx = get_reg_idx();
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