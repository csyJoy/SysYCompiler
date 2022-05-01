pub type int = i32;
pub type Ident = String;


#[derive(Debug, Clone)]
pub struct CompUnit{
    pub items: Vec<GlobalItem>,
}

#[derive(Debug, Clone)]
pub enum GlobalItem{
    Decl(Decl),
    FuncDef(FuncDef),
}

#[derive(Debug, Clone)]
pub struct FuncDef {
    pub func_type: FuncType,
    pub id: String,
    pub params: Option<FuncParams>,
    pub block: Block,
}


#[derive(Debug, Clone)]
pub enum  FuncType{
    Int,
    Void
}
#[derive(Debug, Clone)]
pub struct FuncParams{
    pub param: FuncParam,
    pub params: Vec<FuncParam>,
}
#[derive(Debug, Clone)]
pub struct ArrayIdx{
    pub const_exp: Vec<ConstExp>
}

#[derive(Debug, Clone)]
pub struct FuncParam{
    pub btype: BType,
    pub ident: Ident,
    pub array_idx: Option<ArrayIdx>
}

#[derive(Debug, Clone)]
pub struct Block{
    pub block_item: Vec<BlockItem>,
}

#[derive(Debug, Clone)]
pub struct BlockItem{
    pub decl: Option<Decl>,
    pub stmt: Option<Stmt>
}

#[derive(Debug, Clone)]
pub enum BranchType{
    Matched(Box<(Exp, Stmt, Stmt)>),
    UnMatched(Box<(Exp, Stmt, Option<Stmt>)>)
}
#[derive(Debug, Clone)]
pub enum StmtType{
    Return(Option<Exp>),
    Assign((Lval, Exp)),
    StmtBlock(Block),
    Exp(Option<Exp>),
    Branch(BranchType),
    While(Box<(Exp, Stmt)>),
    Break,
    Continue
}
#[derive(Debug, Clone)]
pub struct Stmt{
    pub stmt_type: StmtType,
}

#[derive(Debug, Clone)]
pub struct Exp{
    pub exp: Option<Box<LOrExp>>
}

#[derive(Debug, Clone)]
pub struct UnaryExp{
    pub primary_exp: Option<Box<PrimaryExp>>,
    pub unary_exp: Option<(UnaryOp, Box<UnaryExp>)>,
    pub func_call: Option<(Ident,Option<FuncRParams>)>
}

#[derive(Debug, Clone)]
pub struct FuncRParams{
    pub exp: Exp,
    pub exp_vec: Vec<Exp>
}

#[derive(Debug, Clone)]
pub struct PrimaryExp{
    pub exp: Option<Box<Exp>>,
    pub lval: Option<Lval>,
    pub num: Option<int>
}

#[derive(Debug, Clone)]
pub enum UnaryOperator{
    Add,
    Sub,
    False,
}
#[derive(Debug, Clone)]
pub struct UnaryOp{
    pub unary_op: UnaryOperator
}

#[derive(Debug, Clone)]
pub enum MulOperator{
    Times,
    Divide,
    Quote
}

#[derive(Debug, Clone)]
pub struct MulExp{
    pub unary_exp: Option<Box<UnaryExp>>,
    pub mul_operate: Option<(Box<MulExp>,MulOperator,Box<UnaryExp>)>,
}

#[derive(Debug, Clone)]
pub enum AddOperator{
    Add,
    Sub
}
#[derive(Debug, Clone)]
pub struct AddExp{
    pub mul_exp: Option<Box<MulExp>>,
    pub add_operate: Option<(Box<AddExp>, AddOperator, Box<MulExp>)>
}

#[derive(Debug, Clone)]
pub enum RelOperation{
    Less,
    Greater,
    LessEq,
    GreaterEq
}

#[derive(Debug, Clone)]
pub struct RelExp{
    pub add_exp: Option<Box<AddExp>>,
    pub rel_operate: Option<(Box<RelExp>, RelOperation, Box<AddExp>)>
}

#[derive(Debug, Clone)]
pub enum EqOperation{
    Eq,
    NEq
}

#[derive(Debug, Clone)]
pub struct EqExp{
    pub rel_exp: Option<Box<RelExp>>,
    pub eq_operate: Option<(Box<EqExp>, EqOperation, Box<RelExp>)>
}

#[derive(Debug, Clone)]
pub struct LAndExp{
    pub eq_exp: Option<Box<EqExp>>,
    pub land_operate:  Option<(Box<LAndExp>, Box<EqExp>)>
}

#[derive(Debug, Clone)]
pub struct LOrExp{
    pub land_exp: Option<Box<LAndExp>>,
    pub lor_operate: Option<(Box<LOrExp>, Box<LAndExp>)>
}

#[derive(Debug, Clone)]
pub struct Decl{
    pub const_decl: Option<Box<ConstDecl>>,
    pub var_decl: Option<Box<VarDecl>>
}

#[derive(Debug, Clone)]
pub struct ConstDecl{
    pub b_type: BType,
    pub const_def: ConstDef,
    pub const_def_vec: Option<Vec<ConstDef>>
}

#[derive(Debug, Clone)]
pub enum BType{
    Int
}

#[derive(Debug, Clone)]
pub struct Lval{
    pub ident: Ident,
    pub array_idx: Vec<Exp>,
}

#[derive(Debug, Clone)]
pub struct ConstDef{
    pub ident: Ident,
    pub array_idx: Vec<ConstExp>,
    pub const_init_val: Option<ConstInitVal>
}

#[derive(Debug, Clone)]
pub struct ConstInitVal{
    pub const_exp: Option<ConstExp>,
    pub array_init_vec: Option<Box<ConstArrayInit>>
}

#[derive(Debug, Clone)]
pub struct ConstArrayInit{
    pub array_init: ConstInitVal,
    pub array_init_vec: Vec<ConstInitVal>
}

#[derive(Debug, Clone)]
pub struct ConstExp{
    pub exp: Exp
}

#[derive(Debug, Clone)]
pub struct VarDecl{
    pub b_type: BType,
    pub var_def: VarDef,
    pub var_def_vec: Vec<VarDef>
}

#[derive(Debug, Clone)]
pub struct VarDef{
    pub ident: Ident,
    pub array_init: Vec<ConstExp>,
    pub initval: Option<InitVal>
}

#[derive(Debug, Clone)]
pub struct InitVal{
    pub exp: Option<Exp>,
    pub array_init_vec: Option<Box<VarArrayInit>>,
}

#[derive(Debug, Clone)]
pub struct  VarArrayInit{
    pub array_init: InitVal,
    pub array_init_vec: Vec<InitVal>
}