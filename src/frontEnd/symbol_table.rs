use std::borrow::BorrowMut;
use std::collections::HashMap;
use std::hash;
use std::path::Prefix::Disk;
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::sync::Weak;
use crate::frontEnd::ast::{FuncType, PrimaryExp};
use crate::frontEnd::GLOBAL_SYMBOL_TABLE_ALLOCATOR;

#[derive(Debug)]
pub struct SymbolTable{
    pub symbol_id: i32,
    last_scpoe: Option<Arc<Mutex<SymbolTable>>>,
    table: HashMap<String, SymbolInner>,
}
impl SymbolTable{
    pub fn insert_function_symbol(&mut self, name: String, func_type: FuncType){
        let s = format!("{}_function", name);
        self.table.insert(s,
                          SymbolInner{symbol_type: SymbolType::Function(func_type),
                              value: None,
                              reg: None});
    }
    pub fn init_lib_fun(&mut self) -> String{
        let mut s = "".to_string();
        self.insert_function_symbol("getint".to_string(), FuncType::Int);
        s += "decl @getint(): i32\n";
        self.insert_function_symbol("getch".to_string(), FuncType::Int);
        s += "decl @getch(): i32\n";
        self.insert_function_symbol("getarray".to_string(), FuncType::Int);
        s += "decl @getarray(*i32): i32\n";
        self.insert_function_symbol("putint".to_string(), FuncType::Void);
        s += "decl @putint(i32)\n";
        self.insert_function_symbol("putch".to_string(), FuncType::Void);
        s += "decl @putch(i32)\n";
        self.insert_function_symbol("putarray".to_string(), FuncType::Void);
        s += "decl @putarray(i32, *i32)\n";
        self.insert_function_symbol("starttime".to_string(), FuncType::Void);
        s += "decl @starttime()\n";
        self.insert_function_symbol("stoptime".to_string(), FuncType::Void);
        s += "decl @stoptime()\n";
        s
    }
    pub fn function_type(&mut self, name: &String) -> Option<FuncType>{
        let s = format!("{}_function", name);
        if let Some(f) = self.table.get(&s){
            if let SymbolType::Function(FuncType::Int) = &f.symbol_type{
                Some(FuncType::Int)
            } else if let SymbolType::Function(FuncType::Void) = &f.symbol_type{
                Some(FuncType::Void)
            } else {
                unreachable!()
            }
        } else {
            None
        }
    }
    pub fn exist_function_symbol(&mut self, name: &String) -> bool{
        let s = format!("{}_function", name);
        if let Some(_) = self.table.get(&s){
            true
        } else {
            false
        }
    }
    pub fn get_dimension(&self, name: &String) -> Option<Vec<i32>>{
        if let Some(a) = self.table.get(name){
            let c  = match &a.symbol_type{
                SymbolType::RawPoint(a) => Some(a.size.clone()),
                SymbolType::ConstPoint(a) => Some(a.size.clone()),
                SymbolType::VarPoint(a) => Some(a.size.clone()),
                _ => None,
            };
            c
        } else {
            if let Some(b) = &self.last_scpoe{
                let d = b.lock().unwrap();
                d.get_dimension(name)
            } else {
                None
            }
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
    pub fn insert_var_point_symbol(&mut self, name: String, dim: &Vec<i32>){
        self.table.insert(name,
                          SymbolInner{symbol_type: SymbolType::VarPoint(Dimension::from(dim.clone
                          ())),
                              value: None,
                              reg: None});
    }

    pub fn insert_raw_point_symbol(&mut self, name: String, dim: &Vec<i32>){
        self.table.insert(name,
                          SymbolInner{symbol_type: SymbolType::RawPoint(Dimension::from(dim.clone())),
                              value: None,
                              reg: None});
    }

    pub fn insert_const_point_symbol(&mut self, name: String, dim: &Vec<i32>){
        self.table.insert(name,
                          SymbolInner{symbol_type: SymbolType::ConstPoint(Dimension::from(dim.clone())),
                              value: None,
                              reg: None});
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
    pub fn modify_var_symbol(&mut self, name: &String, value: i32){
        if let Some(_) = self.exist_var_symbol(name){
            if let Some(a) = self.table.get(name){
                self.table.remove(name);
                self.insert_var_symbol(name.to_string(), Some(value));
            } else {
                let mut d = self.last_scpoe.as_ref().unwrap().lock().unwrap();
                d.modify_var_symbol(name, value);
            }
        } else {
            unreachable!()
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
    pub fn is_raw_ptr(&self, name: &String) -> bool{
        if let Some(a) = self.table.get(name){
            if let SymbolType::RawPoint(_) = a.symbol_type{
                return true;
            } else {
                return false;
            }
        } else {
            if let Some(b) = &self.last_scpoe{
                let d = b.lock().unwrap();
                d.is_raw_ptr(name)
            } else {
                false
            }
        }
    }
    pub fn is_var(&self, name: &String) -> bool{
        if let Some(a) = self.table.get(name){
            let c  = match a.symbol_type{
                SymbolType::Var => true,
                _ => false
            };
            c
        } else {
            if let Some(b) = &self.last_scpoe{
                let d = b.lock().unwrap();
                d.is_var(name)
            } else {
                false
            }
        }
    }
    pub fn exist_var_symbol(&self, name: &String)-> Option<i32>{
        if let Some(a) = self.table.get(name){
            let c  = match a.symbol_type{
                SymbolType::Var => true,
                SymbolType::VarPoint(_) => true,
                SymbolType::ConstPoint(_) => true,
                SymbolType::RawPoint(_) => true,
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
#[derive(Debug, Clone)]
pub struct Dimension{
    size: Vec<i32>
}
impl From<Vec<i32>> for Dimension{
    fn from(inner: Vec<i32>) -> Self {
        Dimension{size: inner.clone()}
    }
}

#[derive(Debug, Clone)]
pub enum SymbolType{
    Function(FuncType),
    Const,
    Var,
    ConstPoint(Dimension),
    VarPoint(Dimension),
    RawPoint(Dimension)
}
#[derive(Debug, Clone)]
pub enum Value{
    Int(i32),
}
#[derive(Debug, Clone)]
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
