use std::sync::Arc;
use std::sync::Weak;

struct CFG{
    enter: CFGInner,
    exit: CFGInner,
    all_inner: Vec<CFGInner>
}

struct CFGInner{
    before: Vec<Weak<CFGInner>>,
    after: Vec<Arc<CFGInner>>,
    code: String,
}