use std::cell::RefCell;
use lazy_static::lazy_static;
use std::sync::{Mutex, WaitTimeoutResult};
use crate::frontEnd::ast::AddOperator::Add;
use crate::frontEnd::SymbolTable;
use crate::frontEnd::SymbolType;

pub type int = i32;
pub type Ident = String;


#[derive(Debug)]
pub struct CompUnit{
    pub func_def: FuncDef,
}

#[derive(Debug)]
pub struct FuncDef {
    pub func_type: FuncType,
    pub id: String,
    pub block: Block,
}


#[derive(Debug)]
pub enum  FuncType{
    Int,
}

#[derive(Debug)]
pub struct Block{
    pub block_item: Vec<BlockItem>,
}

#[derive(Debug)]
pub struct BlockItem{
    pub decl: Option<Decl>,
    pub stmt: Option<Stmt>
}

#[derive(Debug)]
pub enum StmtType{
    Return(Exp),
    Assign((Lval, Exp))
}
#[derive(Debug)]
pub struct Stmt{
    pub stmt_type: StmtType,
}

#[derive(Debug)]
pub struct Exp{
    pub exp: Option<Box<LOrExp>>
}

#[derive(Debug)]
pub struct UnaryExp{
    pub primary_exp: Option<Box<PrimaryExp>>,
    pub unary_exp: Option<(UnaryOp, Box<UnaryExp>)>
}

#[derive(Debug)]
pub struct PrimaryExp{
    pub exp: Option<Box<Exp>>,
    pub lval: Option<Lval>,
    pub num: Option<int>
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

#[derive(Debug)]
pub struct LAndExp{
    pub eq_exp: Option<Box<EqExp>>,
    pub land_operate:  Option<(Box<LAndExp>, Box<EqExp>)>
}

#[derive(Debug)]
pub struct LOrExp{
    pub land_exp: Option<Box<LAndExp>>,
    pub lor_operate: Option<(Box<LOrExp>, Box<LAndExp>)>
}

#[derive(Debug)]
pub struct Decl{
    pub const_decl: Option<Box<ConstDecl>>,
    pub var_decl: Option<Box<VarDecl>>
}

#[derive(Debug)]
pub struct ConstDecl{
    pub b_type: BType,
    pub const_def: ConstDef,
    pub const_def_vec: Option<Vec<ConstDef>>
}

#[derive(Debug)]
pub enum BType{
    Int
}

#[derive(Debug)]
pub struct Lval{
    pub ident: Ident
}

#[derive(Debug)]
pub struct ConstDef{
    pub ident: Ident,
    pub const_init_val: ConstInitVal
}

#[derive(Debug)]
pub struct ConstInitVal{
    pub const_exp: ConstExp,
}

#[derive(Debug)]
pub struct ConstExp{
    pub exp: Exp
}

#[derive(Debug)]
pub struct VarDecl{
    pub b_type: BType,
    pub var_def: VarDef,
    pub var_def_vec: Vec<VarDef>
}

#[derive(Debug)]
pub struct VarDef{
    pub ident: Ident,
    pub initval: Option<InitVal>
}

#[derive(Debug)]
pub struct InitVal{
    pub exp: Exp
}
