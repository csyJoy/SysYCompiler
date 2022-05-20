use std::collections::{HashMap, VecDeque};
use std::hash::Hash;
use koopa::ir::{Function, Value};
use crate::optim::cfg::{Interval, IntervalHandler};
use lazy_static::lazy_static;

struct RegAllocator{
    reg_pool: VecDeque<i32>,
    val_use_reg:  HashMap<Value, i32>,
    reg_store_val: HashMap<i32, Value>
}
impl RegAllocator{
    fn new() -> RegAllocator{
        let mut reg_pool = VecDeque::new();
        for i in 0..12{
            reg_pool.push_front(i);
        }
        RegAllocator{reg_pool, val_use_reg: HashMap::with_capacity(12), reg_store_val:
        HashMap::with_capacity(12)}
    }
    fn alloc_reg(&mut self, val: Value) -> Option<i32>{
        if let Some(reg) = self.reg_pool.pop_front(){
            self.val_use_reg.insert(val, reg);
            self.reg_store_val.insert(reg, val);
            Some(reg)
        } else {
            None
        }
    }
    /// if reg is invalid, do nothing
    fn free_reg(&mut self, val: Value){
        if !self.val_use_reg.contains_key(&val){
            let val = self.val_use_reg.remove(&val).unwrap();
            self.reg_store_val.remove(&val);
            self.reg_pool.push_back(val);
        }
    }
}

/// reg_alloc take the message of interval of all values, and return the allocation result
pub fn reg_alloc(all_interval: HashMap<Function, HashMap<Value, Interval>>) -> HashMap<Function,
    HashMap<Value, Option<i32>>>{
    let mut reg_allocator = RegAllocator::new();
    let mut hanles = IntervalHandler::new(all_interval);
    let mut global_result = HashMap::new();
    for (func, handle) in &mut hanles{
        let mut result = HashMap::new();
        handle.into_iter().map(|(val, out_of_use)| -> (Value, Option<i32>){
            for val in out_of_use{
                reg_allocator.free_reg(val);
            }
            (val, reg_allocator.alloc_reg(val))
        }).fold(&mut result, |rst, idx|{
            let (val, reg_idx) = idx;
            rst.insert(val, reg_idx);
            rst
        });
        global_result.insert(func.clone(), result);
    }
    global_result
}