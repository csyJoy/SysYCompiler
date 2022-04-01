use std::collections::HashMap;
use std::hash;
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::sync::Weak;

#[derive(Debug)]
pub struct SymbolTable{
    last_scpoe: Option<Arc<Mutex<SymbolTable>>>,
    table: HashMap<String, SymbolInner>,
}
impl SymbolTable{
    pub fn insert_const_symbol(&mut self, name: String, value: i32){
        self.table.insert(name,
                          SymbolInner{symbol_type: SymbolType::Const,
                                         value: Some(Value::Int(value)),
                                         reg: None});
    }
    pub fn insert_var_symbol(&mut self, name: String, value: Option<i32>){
        if let Some(i) = value{
            self.table.insert(name,
                              SymbolInner{symbol_type: SymbolType::Var,
                                  value: Some(Value::Int(i)),
                                  reg: None});
        } else {
            self.table.insert(name,
                              SymbolInner{symbol_type: SymbolType::Var,
                                  value: None,
                                  reg: None});
        }
    }
    pub fn exist_const_symbol(&self, name: &String)-> bool{

        let a  = match &self.table.get(name).unwrap().symbol_type{
            SymbolType::Const => true,
            SymbolType::Var => false
        };
        self.table.contains_key(name) &&  a
    }
    pub fn exist_var_symbol(&self, name: &String)-> bool{
        let a  = match &self.table.get(name).unwrap().symbol_type{
            SymbolType::Const => false,
            SymbolType::Var => true
        };
        self.table.contains_key(name) &&  a
    }
    pub fn get_const_value(&self, name: &String) -> i32{
        let a = self.table.get(name).unwrap().value.as_ref().unwrap();
        match a{
            Value::Int(b) => *b,
            _ => 0
        }
    }
    pub fn set_var_reg(&mut self, name: &String, reg_idx: i32){
        let a = self.table.get_mut(name).unwrap();
        a.reg = Some(reg_idx);
    }
    pub fn get_var_reg(&self, name: &String) -> Option<i32>{
        self.table.get(name).unwrap().reg
    }
}
#[derive(Debug)]
pub enum SymbolType{
    Const,
    Var
}
#[derive(Debug)]
pub enum Value{
    Int(i32),
}
#[derive(Debug)]
struct SymbolInner{
    symbol_type: SymbolType,
    value: Option<Value>,
    reg: Option<i32>
}

pub struct GlobalSymbolTableAllocator{
    pub now_symbol: Option<Arc<Mutex<SymbolTable>>>
}
impl GlobalSymbolTableAllocator{
    pub(crate) fn allocate_symbol_table(&mut self) -> Arc<Mutex<SymbolTable>>{
        if let Some(a) = &self.now_symbol{
            let tmp = Arc::new(Mutex::new(SymbolTable{last_scpoe: Some(a.clone()),
                table: HashMap::new()}));
            self.now_symbol = Some(tmp.clone());
            return tmp;
        } else {
            let tmp = Arc::new(Mutex::new(SymbolTable{last_scpoe: None,
                table:HashMap::new()}));
            self.now_symbol = Some(tmp.clone());
            return tmp;
        }
    }
    pub(crate) fn deallocate_symbol_table(&mut self){
        let mut tmp: Option<Arc<Mutex<SymbolTable>>> = None;
        if let Some(a) = &self.now_symbol{
            if let Some(b) = &a.lock().unwrap().last_scpoe{
                tmp = Some(b.clone());
            } else {
                tmp = None;
            }
        }
        self.now_symbol = tmp;
    }
}
