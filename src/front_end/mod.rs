pub mod symbol_table;
pub mod ast;
pub mod parser;
pub mod ir_marco;
mod eval_const;

pub use symbol_table::{SymbolTable, SymbolType};
use lazy_static::lazy_static;
use std::sync::Mutex;
use std::cell::RefCell;
pub use symbol_table::GlobalSymbolTableAllocator;

lazy_static!{
    pub static ref REG_INDEX: Mutex<RefCell<i32>> = Mutex::new(RefCell::new(0));
    pub static ref GLOBAL_SYMBOL_TABLE_ALLOCATOR: Mutex<RefCell<GlobalSymbolTableAllocator>> = Mutex::new
    (RefCell::new(GlobalSymbolTableAllocator{ now_symbol: None ,symbol_table_vec: Vec::new(),
     now_id: 0, global_symbol_table: None}));
}
