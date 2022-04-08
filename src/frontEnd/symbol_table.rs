use std::collections::HashMap;
use std::hash;
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::sync::Weak;
use crate::frontEnd::ast::PrimaryExp;
use crate::frontEnd::GLOBAL_SYMBOL_TABLE_ALLOCATOR;

#[derive(Debug)]
pub struct SymbolTable{
    pub symbol_id: i32,
    last_scpoe: Option<Arc<Mutex<SymbolTable>>>,
    table: HashMap<String, SymbolInner>,
}
impl SymbolTable{
    pub fn insert_function_symbol(&mut self, name: String){
        let s = format!("{}_function", name);
        self.table.insert(s,
                          SymbolInner{symbol_type: SymbolType::Function,
                              value: None,
                              reg: None});
    }
    pub fn exist_function_symbol(&mut self, name: &String) -> bool{
        let s = format!("{}_function", name);
        if let Some(_) = self.table.get(&s){
            true
        } else {
            false
        }
    }
    pub fn exist_global_inited_symbol(&mut self, name: &String) -> bool{
        //todo: 是否是global symbol的检测
        if let Some(v) = self.table.get(name){
            if let Some(_) = v.value{
                true
            }else {
                false
            }
        }else{
            false
        }
    }
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
    pub fn exist_const_symbol(&self, name: &String) -> bool{
        if let Some(a) = self.table.get(name){
            let c  = match a.symbol_type{
                SymbolType::Const => true,
                _ => false,
            };
            self.table.contains_key(name) && c
        } else {
            if let Some(b) = &self.last_scpoe{
                let d = b.lock().unwrap();
                d.exist_const_symbol(name)
            } else {
                false
            }
       }
    }
    pub fn exist_var_symbol(&self, name: &String)-> Option<i32>{
        if let Some(a) = self.table.get(name){
            let c  = match a.symbol_type{
                SymbolType::Var => true,
                _ => false
            };
            if self.table.contains_key(name) && c{
                Some(self.symbol_id)
            } else {
                None
            }
        } else {
            if let Some(b) = &self.last_scpoe{
                let d = b.lock().unwrap();
                d.exist_var_symbol(name)
            } else {
                None
            }
        }
    }
    pub fn get_value(&self, name: &String) -> i32{
        if let Some(b) = self.table.get(name) {
            if let Some(a) = &b.value{
                match a{
                    Value::Int(i) => *i,
                    _ => 0
                }
            } else {
                0
            }
        } else {
            if let Some(d) = &self.last_scpoe{
                let e = d.lock().unwrap();
                e.get_value(name)
            } else {
                0
            }
        }
    }
    pub fn set_var_reg(&mut self, name: &String, reg_idx: i32){
        if let Some(a) = self.table.get_mut(name){
            a.reg = Some(reg_idx);
        } else {
            if let Some(b) = &self.last_scpoe{
                let mut d = b.lock().unwrap();
                d.set_var_reg(name, reg_idx);
            }
        }
    }
    pub fn get_var_reg(&self, name: &String) -> Option<i32>{
        if let Some(a) = self.table.get(name){
            a.reg
        } else {
            if let Some(c) = &self.last_scpoe{
                let mut d = c.lock().unwrap();
                d.get_var_reg(name)
            } else {
                None
            }
        }
    }
}
#[derive(Debug)]
pub enum SymbolType{
    Function,
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
    pub now_symbol: Option<Arc<Mutex<SymbolTable>>>,
    pub symbol_table_vec: Vec<Arc<Mutex<SymbolTable>>>,
    pub now_id: i32,
    pub global_symbol_table: Option<Arc<Mutex<SymbolTable>>>
}
impl GlobalSymbolTableAllocator{
    pub(crate) fn allocate_symbol_table(&mut self) -> Arc<Mutex<SymbolTable>>{
        if let Some(a) = &self.now_symbol{
            self.now_id = self.now_id + 1;
            let tmp = Arc::new(Mutex::new(SymbolTable{last_scpoe: Some(a.clone()),
                table: HashMap::new(), symbol_id: self.now_id}));
            self.now_symbol = Some(tmp.clone());
            self.symbol_table_vec.push(tmp.clone());
            return tmp;
        } else {
            self.now_id = self.now_id + 1;
            let tmp = Arc::new(Mutex::new(SymbolTable{last_scpoe: None,
                table:HashMap::new(),symbol_id: self.now_id}));
            self.now_symbol = Some(tmp.clone());
            self.symbol_table_vec.push(tmp.clone());
            return tmp;
        }
    }
    pub(crate) fn deallocate_symbol_table(&mut self){
        //todo: 没有对vec中的arc做处理，所以说symbol_table是不会消失的
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
