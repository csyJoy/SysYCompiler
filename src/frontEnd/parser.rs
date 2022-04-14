use std::borrow::{Borrow, BorrowMut};
use crate::frontEnd::{ast, symbol_table};
use crate::frontEnd::ast::{AddExp, AddOperator, Block, BlockItem, BranchType, BType, CompUnit, ConstArrayInit, ConstDecl, ConstDef, ConstExp, ConstInitVal, Decl, EqExp, EqOperation, Exp, FuncDef, FuncParams, FuncType, GlobalItem, InitVal, LAndExp, LOrExp, Lval, MulExp, MulOperator, PrimaryExp, RelExp, RelOperation, Stmt, StmtType, UnaryExp, UnaryOp, UnaryOperator, VarArrayInit, VarDecl, VarDef};
use lazy_static::lazy_static;
use std::cell::{Ref, RefCell};
use std::fmt::format;
use std::mem;
use std::ops::{Add, Deref, Mul};
use std::process::id;
use std::sync::Mutex;
use symbol_table::GlobalSymbolTableAllocator;
use crate::frontEnd::ast::StmtType::StmtBlock;
use crate::frontEnd::symbol_table::Value;
use crate::frontEnd::GLOBAL_SYMBOL_TABLE_ALLOCATOR;
use crate::frontEnd::REG_INDEX;
use std::sync::Arc;
use crate::frontEnd::ir_marco::{lor_code_gen, land_code_gen};
lazy_static!{
    static ref global_branch_count:Arc<Mutex<RefCell<i32>>> = Arc::new(Mutex::new(RefCell::new(1)));
    static ref global_return_switch:Arc<Mutex<RefCell<bool>>> = Arc::new(Mutex::new(RefCell::new
        (true)));
    static ref global_while_count: Arc<Mutex<RefCell<(Vec<i32>, i32)>>> = Arc::new(Mutex::new
        (RefCell::new((Vec::new(), 0))));
    static ref global_while_switch:Arc<Mutex<RefCell<bool>>> = Arc::new(Mutex::new(RefCell::new
        (true)));
    static ref now_function_name:Arc<Mutex<RefCell<String>>> = Arc::new(Mutex::new(RefCell::new
        ("".to_string())));
}
pub fn get_while() -> i32{
    let mut g = global_while_count.lock().unwrap();
    let gg = g.borrow_mut().get_mut();
    let (gg, _) = gg;
    gg[gg.len()-1]
}
pub fn record_while(count: i32){
    let mut g = global_while_count.lock().unwrap();
    let gg = g.borrow_mut().get_mut();
    let (while_count, deepth) = gg;
    while_count.push(count);
    *deepth  = *deepth + 1;
}
pub fn leave_while(){
    let mut g = global_while_count.lock().unwrap();
    let gg = g.borrow_mut().get_mut();
    let (vec, deepth) = gg;
    vec.pop();
    *deepth  = *deepth - 1;
}



pub fn check_return(s:String, branch_count: i32) -> String{
    let a = s.split("\n").collect::<Vec<&str>>();
    let b = a[a.len()-2].split(" ").collect::<Vec<&str>>();
    if b.len() >= 2 && b[0] == "\tjump"{
        return s
    } else {
        return s + &format!("\tjump %end_{}\n", branch_count)
    }
}

pub fn is_return(s:&String) -> bool{
    let a = s.split("\n").collect::<Vec<&str>>();
    let b = a[a.len()-2].split(" ").collect::<Vec<&str>>();
    if b.len() >= 2 && b[0] == "\tjump"{
        true
    } else {
        false
    }
}

pub fn alloc_reg_for_const(s: String) -> String{
    if let Ok(i) = s.parse::<i32>(){
        format!("\t%{} = ne 0, {}\n", add_reg_idx(), i)
    }else{
        s
    }
}
pub fn add_branch_count() -> i32{
    let mut a = global_branch_count.lock().unwrap();
    let mut g = a.borrow_mut().get_mut();
    *g = *g + 1;
    *g
}

pub fn add_reg_idx() -> i32{
    let mut a = REG_INDEX.lock().unwrap();
    let mut b = a.get_mut();
    *b = *b + 1;
    *b
}

pub fn check_load_ins(name: &String) -> Option<String>{
    let tmp_str = name.to_string();
    let a = tmp_str.split(' ').collect::<Vec<&str>>();
    if a.len() == 4 && a[2] == "load" {
        Some(a[3][1..a[3].find("_").unwrap()].to_string())
    } else {
        None
    }
}
pub fn get_reg_idx(name: &String) -> i32{
    let a = check_load_ins(name);
    if let Some(name) = a{
        let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
        let mut g = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
        if let Some(i) = g.get_var_reg(&name){
            i
        } else {
            unreachable!()
        }
    } else {
        let mut a = REG_INDEX.lock().unwrap();
        let mut b = a.borrow_mut().get_mut();
        *b
    }
}

fn test(a_string: String, c_string: String, a_reg_idx: i32, c_reg_idx: i32,reg_idx: i32,
        operation: String) -> String{
    if let Ok(d) = c_string.parse::<i32>(){
        if let Ok(e) = a_string.parse::<i32>(){
            format!("\t%{} = {} {}, {}\n", reg_idx, operation,e, d)
        } else {
            a_string + &format!("\t%{} = {} %{}, {}\n",reg_idx, operation,
                                    a_reg_idx,d)
        }
    } else {
        if let Ok(f) = a_string.parse::<i32>(){
            c_string + &format!("\t%{} = {} {}, %{}\n", reg_idx, operation, f, c_reg_idx)
        } else {
            let tmp = format!("\t%{} = {} %{}, %{}\n",reg_idx, operation, a_reg_idx,
                              c_reg_idx);
            let mut tmp1 = "".to_string();
            tmp1 = a_string + &c_string;
            tmp1 + &tmp
        }
    }
}

pub trait GetKoopa{
    fn get_koopa(&self) -> String;
}
pub trait EvalConst{
    fn eval_const(&self) -> Option<Value>;
}
pub trait GetName{
    fn get_name(&self) -> String;
}

impl GetKoopa for CompUnit{
    fn get_koopa(&self) -> String {
        let mut s = "".to_string();
        {
            let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
            let mut g = m.borrow_mut().get_mut();
            let sy = g.allocate_symbol_table();
            g.global_symbol_table = Some(sy.clone());
            s += &g.global_symbol_table.as_ref().unwrap().lock().unwrap().init_lib_fun();
        }
        for i in &self.items{
            s += &i.get_koopa();
        }
        {
            let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
            m.borrow_mut().get_mut().deallocate_symbol_table();
        }
        s
    }
}
impl GetKoopa for GlobalItem{
    fn get_koopa(&self) -> String{
        match &self{
            GlobalItem::Decl(decl) => {
                decl.get_global_definition()
            }
            GlobalItem::FuncDef(func_def) => {
                func_def.get_koopa()
            }
            _ => unreachable!()
        }
    }
}
impl Decl{
    fn get_global_definition(&self) -> String{
        if let Some(var) = &self.var_decl{
            var.get_global_definition()
        } else if let Some(con) = &self.const_decl{
            con.get_global_definition()
        } else {
            unreachable!()
        }
    }
}
impl VarDecl{
   fn get_global_definition(&self) -> String{
       let mut s = "".to_string();
       s += &self.var_def.get_global_definition();
       for var in &self.var_def_vec{
           s += &var.get_global_definition();
       }
       s
   }
}


fn generate_const_init_val(array_init: &Box<ConstArrayInit>, dim_vec: &Vec<i32>, now_count: &mut
                           i32, mut total_count: i32)
                     -> Vec<i32>{
    // 观察当前initVal是否是一个exp，如果是的话就直接加
    let mut result: Vec<i32> = Vec::new();
    let mut now_dim = 1;
    let mut count = 0;
    let init = &array_init.array_init;
    let mut s = "".to_string();
    if let Some(exp) = &init.const_exp{
        let val = exp.exp.eval_const().unwrap();
        let Value::Int(i) = val;
        result.push(i);
        s += &format!(", {}" ,i);
        count = count + 1;
        total_count += 1;
    } else if let Some(array_init_vec) = &init.array_init_vec{
        //迭代进入下一层了
        result.append(&mut generate_const_init_val(&array_init_vec, dim_vec, &mut count,
                                                 total_count));
        let mut align = dim_vec[0];
        let mut tmp = total_count;
        if tmp == 0{
            align = dim_vec.iter().fold(1, |product, x| x * product);
            align /= dim_vec[dim_vec.len() - 1];
        } else if total_count % align == 0{
            tmp /= dim_vec[0];
            while now_dim < dim_vec.len() && count % dim_vec[now_dim] == 0{
                align = align * dim_vec[now_dim];
                tmp /= dim_vec[now_dim];
                now_dim = now_dim + 1;
            }
        }
        total_count += count;
        while count < align {
            result.push(0);
            count += 1;
            total_count += 1;
        }
        now_dim = 1;
        count = 0;
    }
    if !array_init.array_init_vec.is_empty(){
        for k in &array_init.array_init_vec{
            if let Some(exp) = &k.const_exp{
                let val = exp.exp.eval_const().unwrap();
                let Value::Int(i) = val;
                result.push(i);
                count = count + 1;
                total_count += 1;
            } else if let Some(array_init_vec) = &k.array_init_vec{
                //迭代进入下一层了
                result.append(&mut generate_const_init_val(&array_init_vec, dim_vec, &mut count,
                                                  total_count));
                let mut align = dim_vec[0];
                let mut tmp = total_count;
                if tmp == 0{
                    align = dim_vec.iter().fold(1, |product, x| x * product);
                    align /= dim_vec[dim_vec.len() - 1];
                } else if total_count % align == 0{
                    tmp /= dim_vec[0];
                    while now_dim < dim_vec.len() && count % dim_vec[now_dim] == 0{
                        align = align * dim_vec[now_dim];
                        tmp /= dim_vec[now_dim];
                        now_dim = now_dim + 1;
                    }
                }
                // count != 0 是因为要防止for中的{}在一个都没有添加前就添加0
                total_count += count;
                while count != 0 && count < align {
                    result.push(0);
                    count += 1;
                    total_count += 1;
                }
                now_dim = 1;
                count = 0;
            }
        }
    }
    *now_count = count;
    result
}
fn generate_init_val(array_init: &Box<VarArrayInit>, dim_vec: &Vec<i32>,
                     now_count: &mut i32, mut total_count: i32)
    -> Vec<i32>{
    // 观察当前initVal是否是一个exp，如果是的话就直接加
    let mut now_dim = 1;
    let mut count = 0;
    let init = &array_init.array_init;
    let mut result: Vec<i32> = Vec::new();
    if let Some(exp) = &init.exp{
        let val = exp.eval_const().unwrap();
        let Value::Int(i) = val;
        result.push(i);
        count = count + 1;
        total_count += 1;
    } else if let Some(array_init_vec) = &init.array_init_vec{
        //迭代进入下一层了
        result.append(&mut generate_init_val(&array_init_vec, dim_vec, &mut count, total_count));
        let mut align = dim_vec[0];
        let mut tmp = total_count;
        if tmp == 0 {
            align = dim_vec.iter().fold(1, |product, x| x * product);
            align /= dim_vec[dim_vec.len() - 1];
        }else if tmp % align == 0 {
            tmp /= dim_vec[0];
            while now_dim < dim_vec.len() && tmp % dim_vec[now_dim] == 0{
                align = align * dim_vec[now_dim];
                tmp /= dim_vec[now_dim];
                now_dim = now_dim + 1;
            }
        }
        total_count += count;
        while count != 0 && count < align {
            result.push(0);
            count += 1;
            total_count += 1;
        }
        now_dim = 1;
        count = 0;
    }
    if !array_init.array_init_vec.is_empty(){
        for k in &array_init.array_init_vec{
            if let Some(exp) = &k.exp{
                let val = exp.eval_const().unwrap();
                let Value::Int(i) = val;
                result.push(i);
                count = count + 1;
                total_count += 1;
            } else if let Some(array_init_vec) = &k.array_init_vec{
                //迭代进入下一层了
                result.append(&mut generate_init_val(&array_init_vec, dim_vec, &mut  count,
                                                  total_count));
                let mut align = dim_vec[0];
                let mut tmp = total_count;
                if tmp == 0{
                    align = dim_vec.iter().fold(1, |product, x| product * x) /
                        dim_vec[dim_vec.len() - 1];
                } else if  tmp % align == 0{
                    tmp /= dim_vec[0];
                    while now_dim < dim_vec.len() && tmp % dim_vec[now_dim] == 0{
                        align = align * dim_vec[now_dim];
                        tmp /= dim_vec[now_dim];
                        now_dim = now_dim + 1;
                    }
                }
                total_count += count;
                while count != 0 && count < align {
                    result.push(0);
                    count += 1;
                    total_count += 1;
                }
                now_dim = 1;
                count = 0;
            }
        }
    }
    *now_count =  count;
    result
}
fn init_var_handler(mut result: Vec<i32>, dim_vec: &Vec<i32>) ->
                                                                                            String
{
    let mut product = 1;
    let mut count = result.len();
    let total = dim_vec.iter().fold(product, |product, a| product * a);
    while count < total as usize {
        result.push(0);
        count += 1;
    }
    let mut tmp: Vec<String> = Vec::new();
    for k in (0..dim_vec.len()){
        if k == 0{
            let mut s = "".to_string();
            for i in (0..result.len()){
                if i % dim_vec[0] as usize == 0{
                    s = "".to_string();
                    s += &format!("{{ {}",result[i]);
                }else if i % dim_vec[0] as usize == (dim_vec[0] - 1 ) as usize{
                    s += &format!(", {} }}", result[i]);
                    tmp.push(s.clone());
                } else{
                    s += &format!(", {}", result[i]);
                }
            }
        } else {
            let len = tmp.len();
            let mut s = "".to_string();
            for i in (0..len){
                if i % dim_vec[k] as usize == 0{
                    s = "".to_string();
                    s += &format!("{{ {}",tmp[i]);
                }else if i % dim_vec[k] as usize == (dim_vec[k] - 1 ) as usize{
                    s += &format!(", {} }}", tmp[i]);
                    tmp.push(s.clone());
                } else{
                    s += &format!(", {}", tmp[i]);
                }
            }
            for i in (0..len){
                tmp.remove(0);
            }
        }
    }
    format!(", {}\n",tmp[0])
}
fn get_localtion(unique_name: &String, mut number: usize, dim_vec:&Vec<i32>) -> String{
    let mut tmp: Vec<(i32, usize)> = Vec::new();
    let mut idx = 0;
    for dim in dim_vec{
        let t = number % *dim as usize;
        tmp.push((idx, t));
        number /= *dim as usize;
        idx += 1;
        if number == 0 {
            break;
        }
    }
    let mut s = "".to_string();
    let mut first: bool = true;
    let mut last_use = 0;
    let (tmp1, tmp2) = tmp.pop().unwrap();
    let mut idx = tmp1;
    let mut count = tmp2;
    let mut tt  = (0..dim_vec.len()).collect::<Vec<usize>>();
    tt.reverse();
    for i in tt{
        if idx < i as i32 {
            if first{
                let t = add_reg_idx();
                s += &format!("\t%{} = getelemptr @{}, 0\n", t, unique_name);
                last_use = t;
                first = false;
            }else {
                let t = add_reg_idx();
                s += &format!("\t%{} = getelemptr %{}, 0\n", t, last_use );
                last_use = t;
            }
        }else {
            if first{
                let t = add_reg_idx();
                s += &format!("\t%{} = getelemptr @{}, {}\n", t, unique_name, count);
                last_use = t;
                first = false;
            }else {
                let t = add_reg_idx();
                s += &format!("\t%{} = getelemptr %{}, {}\n", t, last_use, count);
                last_use = t;
            }
            if let Some((tmp1, tmp2)) = tmp.pop(){
                idx = tmp1;
                count = tmp2;
            }
        }
    }
    s
}
impl VarDef{
    fn get_global_definition(&self) -> String{
        let s = self.get_name();
        if !self.array_init.is_empty(){
            let mut unique_name = "".to_string();
            {
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = m.borrow_mut().get_mut();
                let mut go =  g.global_symbol_table.as_mut().unwrap().lock().unwrap();
                unique_name = self.get_name() + &format!("_{}",go.symbol_id);
            }
            let mut total = format!("global @{} = alloc", unique_name );
            let mut ss = "".to_string();
            let mut first:bool = true;
            let mut dim_idx: Vec<i32> = Vec::new();
            let mut b = self.array_init.clone();
            b.reverse();
            for a in &b{
                let idx = a.exp.eval_const().unwrap();
                let Value::Int(i) = idx;
                if first{
                    ss = format!("[i32, {}]", i);
                    dim_idx.push(i);
                    first = false;
                } else {
                    ss = format!("[{}, {}]", ss, i);
                    dim_idx.push(i);
                }
            }
            {
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = m.borrow_mut().get_mut();
                let mut go =  g.global_symbol_table.as_mut().unwrap().lock().unwrap();
                go.insert_var_point_symbol((&s).to_string(), &dim_idx);
            }
            total += &ss;
            if let Some(initval) = &self.initval{
                let init_string = "".to_string();
                if let Some(var_array_init) = &initval.array_init_vec{
                    // dim_idx.reverse();
                    let mut a = 0;
                    total += &init_var_handler(generate_init_val(var_array_init, &dim_idx, &mut a,
                                                                 0), &dim_idx);
                } else {
                    total += ", zeroinit\n";
                }
            } else {
                total += ", zeroinit\n";
            }
            total
        } else {
            if let Some(i) = &self.initval{
                let mut k = i.get_koopa();
                if let Ok(l)= k.parse::<i32>(){
                    let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                    let mut g = m.borrow_mut().get_mut();
                    let mut go =  g.global_symbol_table.as_mut().unwrap().lock().unwrap();
                    go.insert_var_symbol(s, Some(l));
                    let unique_name = self.get_name() + &format!("_{}",go.symbol_id);
                    format!("global @{} = alloc {}, {}\n",unique_name, "i32", l)
                } else {
                    unreachable!();
                }
            } else {
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = m.borrow_mut().get_mut();
                let mut go =  g.global_symbol_table.as_mut().unwrap().lock().unwrap();
                go.insert_var_symbol((&s).to_string(), Some(0));
                let unique_name = self.get_name() + &format!("_{}",go.symbol_id);
                format!("global @{} = alloc {}, 0\n", unique_name, "i32")
            }
        }
    }
    // fn get_global_definition(&self) -> String{
    //     let s = self.get_name();
    //     if let Some(a) = &self.array_init{
    //         let Value::Int(i) = a.exp.eval_const().unwrap();
    //         let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
    //         let mut g = m.borrow_mut().get_mut();
    //         let mut go =  g.global_symbol_table.as_mut().unwrap().lock().unwrap();
    //         go.insert_var_point_symbol((&s).to_string());
    //         let unique_name = self.get_name() + &format!("_{}",go.symbol_id);
    //         let mut ss = format!("global @{} = alloc [i32, {}]", unique_name, i);
    //         if let Some(i) = &self.initval{
    //             let array_init_vec = i.array_init_vec.as_ref().unwrap();
    //             let first = &array_init_vec.array_init;
    //             let other = &array_init_vec.array_init_vec;
    //             if let Some(Value::Int(i)) = first.eval_const(){
    //                 ss += &format!(", {{{}", i);
    //                 if !other.is_empty(){
    //                     for k in other{
    //                         if let Some(Value::Int(i)) = k.eval_const(){
    //                             ss += &format!(", {}", i);
    //                         }
    //                     }
    //                 }
    //             }
    //             ss += "}";
    //         }
    //         ss += "\n";
    //         ss
    //     } else {
    //         if let Some(i) = &self.initval{
    //             let mut k = i.get_koopa();
    //             if let Ok(l)= k.parse::<i32>(){
    //                 let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
    //                 let mut g = m.borrow_mut().get_mut();
    //                 let mut go =  g.global_symbol_table.as_mut().unwrap().lock().unwrap();
    //                 go.insert_var_symbol(s, Some(l));
    //                 let unique_name = self.get_name() + &format!("_{}",go.symbol_id);
    //                 format!("global @{} = alloc {}, {}\n",unique_name, "i32", l)
    //             } else {
    //                 unreachable!();
    //             }
    //         } else {
    //             let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
    //             let mut g = m.borrow_mut().get_mut();
    //             let mut go =  g.global_symbol_table.as_mut().unwrap().lock().unwrap();
    //             go.insert_var_symbol((&s).to_string(), Some(0));
    //             let unique_name = self.get_name() + &format!("_{}",go.symbol_id);
    //             format!("global @{} = alloc {}, 0\n", unique_name, "i32")
    //         }
    //     }
    // }
}
impl ConstDecl{
    fn get_global_definition(&self) -> String{
        //todo: 没有加vec的处理
        let mut ss = "".to_string();
        if let Some(a) = self.const_def.eval_const(){
            let Value::Int(i) = a;
            let s = self.const_def.get_name();
            {
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = m.borrow_mut().get_mut();
                let mut k = g.global_symbol_table.as_mut().unwrap().lock().unwrap();
                k.insert_const_symbol(s, i);
            }
            ss += "";
        } else {
            ss += &self.const_def.get_global_definition();
        }
        if let Some(v) = &self.const_def_vec{
            for q in v{
                if let Some(a) = q.eval_const(){
                    let Value::Int(i) = a;
                    let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                    let mut g = m.borrow_mut().get_mut();
                    let mut k = g.global_symbol_table.as_mut().unwrap().lock().unwrap();
                    k.insert_const_symbol(q.get_name(), i);
                    ss += "";
                } else {
                    ss += &self.const_def.get_global_definition();
                }
            }
        }
        ss
    }
}
impl GetKoopa for FuncParams{
    fn get_koopa(& self) -> String {
        let mut ident = &self.param.ident;
        let mut btype = &self.param.btype;
        let mut idx = &self.param.array_idx;
        let mut s_type = "".to_string();
        match btype{
            BType::Int => {
                //todo： 需要对数组参数进行处理
                if let Some(idx) = &self.param.array_idx{
                    let mut ss = "".to_string();
                    let mut ptr = "*".to_string();
                    let mut first = true;
                    if idx.const_exp.is_empty(){
                        ss = "i32".to_string();
                    } else {
                        for a in &idx.const_exp{
                            let idx = a.exp.eval_const().unwrap();
                            let Value::Int(i) = idx;
                            if first{
                                ss = format!("[i32, {}]", i);
                                first = false;
                            } else {
                                ss = format!("[{}, {}]", ss, i);
                            }
                        }
                    }
                    let sss = (ptr + &ss);
                    s_type += &format!("%{}:{}",  ident, sss);
                } else {
                    s_type += &format!("%{}:i32", ident);
                }
            }
            _ => {unreachable!()}
        }
        if !self.params.is_empty(){
            for i in &self.params{
                ident = &i.ident;
                btype = &i.btype;
                idx = &i.array_idx;
                match btype{
                    BType::Int => {
                        //todo 没处理
                        if let Some(idx) = idx{
                            let mut ss = "".to_string();
                            let mut ptr = "*".to_string();
                            let mut first = true;
                            if idx.const_exp.is_empty(){
                                ss = "i32".to_string();
                            } else {
                                for a in &idx.const_exp{
                                    let idx = a.exp.eval_const().unwrap();
                                    let Value::Int(i) = idx;
                                    if first{
                                        ss = format!("[i32, {}]", i);
                                        first = false;
                                    } else {
                                        ss = format!("[{}, {}]", ss, i);
                                    }
                                }
                            }
                            let sss = (ptr + &ss);
                            s_type += &format!(", %{}:{}",  ident, sss);
                        } else {
                            s_type += &format!(", %{}:i32", ident);
                        }
                    }
                    _ => {unreachable!()}
                }
            }
        }
        s_type
    }
}
impl FuncParams{
    fn alloc_local_var(&self) -> String{
        let mut ident = &self.param.ident;
        let mut btype = &self.param.btype;
        let mut idx = &self.param.array_idx;
        let mut s_type = "".to_string();
        match btype{
            BType::Int => {
                if let Some(array_idx) = idx{
                    let mut o = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                    let mut g = o.borrow_mut().get_mut().allocate_symbol_table();
                    let mut S = g.lock().unwrap();
                    let mut vec:Vec<i32> = Vec::new();
                    let mut ss = "".to_string();
                    let mut ptr = "*".to_string();
                    let mut first = true;
                    if array_idx.const_exp.is_empty(){
                        ss = "i32".to_string();
                    } else {
                        for a in &array_idx.const_exp{
                            let idx = a.exp.eval_const().unwrap();
                            let Value::Int(i) = idx;
                            if first{
                                ss = format!("[i32, {}]", i);
                                first = false;
                            } else {
                                ss = format!("[{}, {}]", ss, i);
                            }
                        }
                    }
                    let sss = (ptr + &ss);
                    for i in (0..array_idx.const_exp.len() + 1){
                        vec.push(0);
                    }
                    S.insert_raw_point_symbol((&ident).to_string(), &vec);
                    let s = S.symbol_id;
                    s_type += &format!("\t@{}_{} = alloc {}\n\tstore %{}, @{}_{}\n", ident, s,
                        sss, ident, ident, s);
                }else {
                    let mut o = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                    let mut g = o.borrow_mut().get_mut().allocate_symbol_table();
                    let mut S = g.lock().unwrap();
                    S.insert_var_symbol((&ident).to_string(),None);
                    let s = S.symbol_id;
                    s_type += &format!("\t@{}_{} = alloc i32\n\tstore %{}, @{}_{}\n", ident, s, ident,
                                       ident, s);
                }
            }
            _ => {unreachable!()}
        }
        if !self.params.is_empty(){
            for i in &self.params{
                ident = &i.ident;
                btype = &i.btype;
                idx = &i.array_idx;
                match btype{
                    BType::Int => {
                        if let Some(array_idx) = idx{
                            let mut o = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                            let mut g = o.borrow_mut().get_mut().allocate_symbol_table();
                            let mut S = g.lock().unwrap();
                            let mut vec:Vec<i32> = Vec::new();
                            let mut ss = "".to_string();
                            let mut ptr = "*".to_string();
                            let mut first = true;
                            if array_idx.const_exp.is_empty(){
                                ss = "i32".to_string();
                            } else {
                                for a in &array_idx.const_exp{
                                    let idx = a.exp.eval_const().unwrap();
                                    let Value::Int(i) = idx;
                                    if first{
                                        ss = format!("[i32, {}]", i);
                                        first = false;
                                    } else {
                                        ss = format!("[{}, {}]", ss, i);
                                    }
                                }
                            }
                            let sss = (ptr + &ss);
                            for i in (0..array_idx.const_exp.len() + 1){
                                vec.push(0);
                            }
                            S.insert_raw_point_symbol((&ident).to_string(), &vec);
                            let s = S.symbol_id;
                            s_type += &format!("\t@{}_{} = alloc {}\n\tstore %{}, @{}_{}\n", ident, s,
                                               sss, ident, ident, s);
                        }else {
                            let mut o = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                            let mut g = o.borrow_mut().get_mut().allocate_symbol_table();
                            let mut S = g.lock().unwrap();
                            S.insert_var_symbol((&ident).to_string(),None);
                            let s = S.symbol_id;
                            s_type += &format!("\t@{}_{} = alloc i32\n\tstore %{}, @{}_{}\n", ident, s, ident,
                                               ident, s);
                        }
                    }
                    // BType::Int => {
                    //     let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                    //     let mut g = m.borrow_mut().get_mut().allocate_symbol_table();
                    //     let mut S = g.lock().unwrap();
                    //     S.insert_var_symbol((&ident).to_string(),None);
                    //     let s = S.symbol_id;
                    //     s_type += &format!("\t@{}_{} = alloc i32\n\tstore %{}, @{}_{}\n", ident, s, ident,
                    //                        ident, s);
                    // }
                    _ => {unreachable!()}
                }
            }
        }
        s_type
    }
}

impl GetKoopa for FuncDef{
    fn get_koopa(&self) -> String {
        let mut typ: &str;
        let mut sr: String = "".to_string();
        {
            let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
            let mut g = &m.borrow_mut().get_mut().global_symbol_table;
            let s = g.as_ref().unwrap();
            let mut t:FuncType = FuncType::Void;
            if let FuncType::Int = self.func_type{
                t = FuncType::Int;
            } else if let FuncType::Void = self.func_type{
                t = FuncType::Void;
            }
            s.lock().unwrap().insert_function_symbol((&self.id).to_string(), t);
            let mut o = now_function_name.lock().unwrap();
            let mut func_name = o.borrow_mut().get_mut();
            *func_name = self.id.clone();
        }
        match self.func_type{
            FuncType::Int => {
                typ = "i32";
                if let Some(params) = &self.params{
                    sr = format!("fun @{}({}): {} ", &self.id, params.get_koopa(),typ)
                        .to_string() +
                        &format!
                        ("{{\n%entry:\n\t@result = alloc i32\n");

                } else {
                    sr = format!("fun @{}(): {} ", &self.id, typ)
                        .to_string() +
                        &format!
                        ("{{\n%entry:\n\t@result = alloc i32\n");
                }
            },
            FuncType::Void => {
                if let Some(params) = &self.params{
                    sr = format!("fun @{}({})", &self.id, params.get_koopa()).to_string() + &format!
                    ("{{\n%entry:\n");
                } else {
                    sr = format!("fun @{}()", &self.id).to_string() + &format!
                    ("{{\n%entry:\n");
                }
            },
            _ => {
                unreachable!()
            }
        }
        let mut s0 =  "".to_string();
        if let Some(params) = &self.params{
            s0 += &params.alloc_local_var();
        } else {
            s0 = "".to_string();
        }
        let s1 = &(sr + &s0 + &self.block.get_koopa());
        let idx = add_reg_idx();
        let sv = s1.split("\n").collect::<Vec<&str>>();
        //todo: 没有处理return 是void的情况
        if sv.len() >=2 {
            let len = (sv.len() - 2) as usize;
            let vec = sv[len].split(" ").collect::<Vec<&str>>();
            let c = sv[len].chars().nth(0).unwrap();
            if let FuncType::Int = self.func_type{
                if c == '%' || vec[0] != "\tjump"{
                    let s  = &format!("\tjump %end_{}\n%end_{}:\n\t%{} = load @result\n\tret \
                    %{}\n}}\n\n", self.id, self.id, idx, idx);
                    s1.to_string() + s
                } else {
                    let s  = &format!("%end_{}:\n\t%{} = load @result\n\tret %{}\n}}\n\n", self.id,
                                      idx,
                                      idx);
                    s1.to_string() + s
                }
            }else {
                if c == '%' || vec[0] != "\tjump"{
                    let s  = &format!("\tjump %end_{}\n%end_{}:\n\tret\n}}\n\n", self.id, self.id);
                    s1.to_string() + s
                } else {
                    let s  = &format!("%end_{}:\n\tret\n}}\n\n", self.id);
                    s1.to_string() + s
                }
            }
        } else {
            unreachable!();
        }
    }
}

impl GetKoopa for Block {
    fn get_koopa(&self) -> String {
        {
            let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
            let mut g = m.borrow_mut().get_mut();
            g.allocate_symbol_table();
        }
        let s = self.block_item.get_koopa();
        {
            let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
            let mut g = m.borrow_mut().get_mut();
            g.deallocate_symbol_table();
            let mut o = global_return_switch.lock().unwrap();
            let mut q = o.get_mut();
            *q = true;
        }
        return s;
    }
}

impl GetKoopa for Vec<BlockItem>{
    fn get_koopa(&self) -> String {
        let mut s = "".to_string();
        let mut first = true;
        for v in self{

            let s1 = v.get_koopa();
            // if is_return(&s1){
            //     if first{
            //         first = false;
            //         s += &s1;
            //     } else {
            //         break;
            //     }
            // } else {
            s += &s1;
            // }
        }
        s
    }
}

impl GetKoopa for BlockItem{
    fn get_koopa(&self) -> String {
        if let Some(decl) = &self.decl{
            decl.get_koopa()
        } else if let Some(stmt) = &self.stmt{
            stmt.get_koopa()
        } else {
            "".to_string()
        }
    }
}


impl GetKoopa for Stmt{
    fn get_koopa(&self) -> String {
        let mut o = global_return_switch.lock().unwrap();
        let mut q = *o.get_mut();
        let mut w = global_while_switch.lock().unwrap();
        let mut qq = *w.get_mut();
        std::mem::drop(w);
        std::mem::drop(o);
        if q && qq {
            match &self.stmt_type{
                StmtType::Return(exp) => {
                    let mut o = global_return_switch.lock().unwrap();
                    let mut q = o.get_mut();
                    *q = false;
                    let a = exp.eval_const();
                    let mut function_name = "".to_string();
                    {
                        function_name = now_function_name.lock().unwrap().borrow_mut()
                            .get_mut().to_string();
                    }
                    if let Some(Value::Int(i)) = a{
                        return format!("\tstore {}, @result\n\tjump %end_{}\n", i, function_name);
                    } else {
                        let exp_string = exp.get_koopa();
                        let exp_reg_idx = get_reg_idx(&exp_string);
                        if let Ok(c) = exp_string.parse::<i32>(){
                            return format!("\tstore {}, @result\n\tjump %end_{}\n", c,
                                           function_name);
                        } else {
                            exp_string + &format!("\tstore %{}, @result\n\tjump %end_{}\n",
                                                  exp_reg_idx, function_name)
                        }
                    }
                }
                StmtType::Assign((ident, exp)) => {
                    let s2 = exp.get_koopa();
                    if let Ok(i) = s2.parse::<i32>(){
                        let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                        let mut g = &m.borrow_mut().get_mut().now_symbol.as_ref().unwrap();
                        let mut go = g.lock().unwrap();
                        let unique_name = format!("{}_{}",ident.ident, go.exist_var_symbol(&ident
                            .ident).unwrap());
                        if go.is_var(&ident.ident){
                            go.modify_var_symbol(&ident.ident, i);
                            format!("\tstore {}, @{}\n",i, unique_name)
                        } else {
                            std::mem::drop(go);
                            std::mem::drop(g);
                            std::mem::drop(m);
                            let ss = ident.get_koopa();
                            let reg = get_reg_idx(&ss);
                            ss + &format!("\tstore {}, %{}",i, reg)
                        }
                    } else {
                        let mut unique_name = "".to_string();
                        let mut is_var: bool = true;
                        {
                            let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                            let mut g = &m.borrow_mut().get_mut().now_symbol.as_ref().unwrap();
                            let mut go = g.lock().unwrap();
                            unique_name = format!("{}_{}", ident.ident, go.exist_var_symbol(&ident
                                .ident).unwrap());
                            is_var = go.is_var(&ident.ident);
                        }
                        let reg = get_reg_idx(&s2);
                        if is_var{
                            let s3 = format!("\tstore %{}, @{}\n", reg, unique_name);
                            s2 + &s3
                        } else {
                            let ss = ident.get_koopa();
                            let rreg = get_reg_idx(&ss);
                            ss + &s2 + &format!("\tstore %{}, %{}", reg, rreg)
                        }
                    }
                }
                StmtType::StmtBlock(block) => {
                    block.get_koopa()
                }
                StmtType::Exp(exp) => { if let Some(e) = exp{
                    e.get_koopa()
                } else {
                    "".to_string()
                }
                }
                StmtType::Branch(branch) => {
                    let branch_count = add_branch_count();
                    match branch{
                        BranchType::Matched(a) => {
                            let b = a.deref();
                            if let (c,d,e) = b{
                                let s = alloc_reg_for_const(c.get_koopa());
                                let s1 = format!("\tbr %{}, %then_{}, %else_{}\n",get_reg_idx(&s),
                                                 branch_count, branch_count);
                                let s2 = check_return(format!("%then_{}:\n", branch_count) +
                                                          &alloc_reg_for_const(d
                                                              .get_koopa()), branch_count);
                                {
                                    let mut o = global_return_switch.lock().unwrap();
                                    let mut q = o.get_mut();
                                    let mut w = global_while_switch.lock().unwrap();
                                    let mut qq = w.get_mut();
                                    *qq = true;
                                    *q = true;
                                }
                                let s3 = check_return(format!("%else_{}:\n", branch_count) + &alloc_reg_for_const
                                    (e.get_koopa()),branch_count);
                                {
                                    let mut o = global_return_switch.lock().unwrap();
                                    let mut q = o.get_mut();
                                    *q = true;
                                    let mut w = global_while_switch.lock().unwrap();
                                    let mut qq = w.get_mut();
                                    *qq = true
                                }
                                s + &s1 + &s2 + &s3 + &format!("%end_{}:\n",branch_count)
                            } else {
                                unreachable!()
                            }
                        },
                        BranchType::UnMatched(a) => {
                            let b = a.deref();
                            if let (c, d, Some(e)) = b{
                                let s = alloc_reg_for_const(c.get_koopa());
                                let s1 = format!("\tbr %{}, %then_{}, %else_{}\n",  get_reg_idx(&s),
                                                 branch_count, branch_count);

                                let s2 = check_return(format!("%then_{}:\n", branch_count) +
                                                          &alloc_reg_for_const(d
                                                              .get_koopa()), branch_count);
                                {
                                    let mut o = global_return_switch.lock().unwrap();
                                    let mut q = o.get_mut();
                                    *q = true;
                                    let mut w = global_while_switch.lock().unwrap();
                                    let mut qq = w.get_mut();
                                    *qq = true
                                }
                                let s3 = check_return(format!("%else_{}:\n", branch_count) + &alloc_reg_for_const
                                    (e.get_koopa()),branch_count);
                                {
                                    let mut o = global_return_switch.lock().unwrap();
                                    let mut q = o.get_mut();
                                    *q = true;
                                    let mut w = global_while_switch.lock().unwrap();
                                    let mut qq = w.get_mut();
                                    *qq = true
                                }
                                s + &s1 + &s2 + &s3 + &format!("%end_{}:\n",branch_count)
                            } else if let (c, d, None) = b{
                                let s = alloc_reg_for_const(c.get_koopa());
                                let s1 = format!("\tbr %{}, %then_{}, %else_{}\n",get_reg_idx(&s),
                                                 branch_count, branch_count) ;
                                let s2 = check_return(format!("%then_{}:\n", branch_count) +
                                                          &alloc_reg_for_const(d
                                                              .get_koopa()), branch_count);
                                {
                                    let mut o = global_return_switch.lock().unwrap();
                                    let mut q = o.get_mut();
                                    *q = true;
                                    let mut w = global_while_switch.lock().unwrap();
                                    let mut qq = w.get_mut();
                                    *qq = true
                                }
                                let s3 = check_return(format!("%else_{}:\n", branch_count),branch_count);
                                s + &s1 + &s2 + &s3 + &format!("%end_{}:\n",branch_count)
                            } else {
                                unreachable!()
                            }
                        }
                        _ => unreachable!()
                    }
                }
                StmtType::While(while_stmt) => {
                    let (exp, stmt) = while_stmt.deref();
                    let branch_count = add_branch_count();
                    record_while(branch_count);
                    {
                        let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                        let g = m.borrow_mut().get_mut().allocate_symbol_table();
                    }
                    let preinstructiion = format!("\tjump %while_entry_{}\n",branch_count);
                    let mut while_entry = format!("%while_entry_{}:\n",branch_count);
                    let exp_code = exp.get_koopa();
                    if let Ok(i) = exp_code.parse::<i32>() {
                        while_entry += &format!("\tbr {}, %while_body_{}, %end_{}\n", i
                            , branch_count, branch_count);
                    } else {
                        while_entry += &exp_code;
                        while_entry += &format!("\tbr %{}, %while_body_{}, %end_{}\n", get_reg_idx
                            (&while_entry), branch_count, branch_count);
                    }
                    let mut while_body = format!("%while_body_{}:\n", branch_count);
                    while_body += &stmt.get_koopa();
                    if !is_return(&while_body){
                        while_body += &format!("\tjump %while_entry_{}\n", branch_count);
                    }
                    while_body += &format!("%end_{}:\n",branch_count);
                    {
                        let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                        m.borrow_mut().get_mut().deallocate_symbol_table();
                    }
                    leave_while();
                    {
                        let mut w = global_while_switch.lock().unwrap();
                        let mut qq = w.get_mut();
                        *qq = true;
                    }
                    preinstructiion + &while_entry + &while_body
                }
                StmtType::Break => {
                    {
                        let mut w = global_while_switch.lock().unwrap();
                        let mut qq = w.get_mut();
                        *qq = false;
                    }
                    format!("\tjump %end_{}\n",get_while())
                }
                StmtType::Continue => {
                    {
                        let mut w = global_while_switch.lock().unwrap();
                        let mut qq = w.get_mut();
                        *qq = false;
                    }
                    format!("\tjump %while_entry_{}\n",get_while())
                }
                _ => unreachable!()
            }
        } else {
            "".to_string()
        }

    }
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
impl EvalConst for Exp{
    fn eval_const(&self) -> Option<Value> {
        self.exp.as_ref().unwrap().eval_const()
    }
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
                            let reg_idx = add_reg_idx();
                            format!("\t%{} = add 0, {}\n",reg_idx, c)
                        } else {
                            let reg_idxx = get_reg_idx(&s);
                            let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                            let mut go = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
                            if let Some(_) = go.exist_var_symbol(&s){
                                let reg_idx = add_reg_idx();
                                format!("\t%{} = add 0, %{}\n",reg_idx, reg_idxx)
                            } else {
                                let reg_idx = add_reg_idx();
                                s + &format!("\t%{} = add 0, %{}\n", reg_idx, reg_idxx)
                            }
                        }
                    }
                    UnaryOperator::Sub => {
                        let mut s = b.get_koopa();
                        if let Ok(c) = s.parse::<i32>(){
                            let reg_idx = add_reg_idx();
                            format!("\t%{} = sub 0, {}\n",reg_idx, c)
                        } else {
                            let reg_idxx = get_reg_idx(&s);
                            let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                            let mut go = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
                            if let Some(_) = go.exist_var_symbol(&s){
                                let reg_idx = add_reg_idx();
                                s + &format!("\t%{} = sub 0, %{}\n", reg_idx, reg_idxx)
                            } else {
                                let reg_idx = add_reg_idx();
                                s + &format!("\t%{} = sub 0, %{}\n", reg_idx, reg_idxx)
                            }
                        }
                    }
                    UnaryOperator::False => {
                        let mut s = b.get_koopa();
                        if let Ok(c) = s.parse::<i32>(){
                            let reg_idx = add_reg_idx();
                            format!("\t%{} = eq {}, 0\n",reg_idx, c)
                        } else {
                            let reg_idxx = get_reg_idx(&s);
                            let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                            let mut go = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
                            if let Some(_) = go.exist_var_symbol(&s){
                                let reg_idx = add_reg_idx();
                                format!("\t%{} = eq %{}, 0\n", reg_idx, reg_idxx)
                            } else {
                                let reg_idx = add_reg_idx();
                                s + &format!("\t%{} = eq %{}, 0\n", reg_idx, reg_idxx)
                            }
                        }
                    }
                    _ => "".to_string()
                }
            } else if let Some((ident, params)) = &self.func_call{
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = &m.borrow_mut().get_mut().global_symbol_table.as_ref().unwrap();
                let mut sy = g.lock().unwrap();
                if sy.exist_function_symbol(&ident){
                    if let Some(rparams) = params{
                        if let Some(FuncType::Int) = sy.function_type(&ident){
                            std::mem::drop(sy);
                            std::mem::drop(g);
                            std::mem::drop(m);
                            let exp = &rparams.exp;
                            let mut s = exp.get_koopa();
                            let mut ss = "".to_string();
                            let mut pre_call = "".to_string();
                            if let Ok(i) = s.parse::<i32>() {
                                ss += &format!(" = call @{}(", ident);
                                ss += &format!("{}", i);
                            } else {
                                pre_call += &s;
                                let idx = get_reg_idx(&s);
                                ss += &format!(" = call @{}(%{}", ident, idx);
                            }
                            for r in &rparams.exp_vec{
                                s = r.get_koopa();
                                if let Ok(i) = s.parse::<i32>() {
                                    ss += &format!(", {}", i);
                                } else {
                                    pre_call += &s;
                                    ss += &format!(", %{}", get_reg_idx(&s));
                                }
                            }
                            ss += ")\n";
                            let rst = add_reg_idx();
                            pre_call + &format!("\t%{}", rst) + &ss
                        } else if let Some(FuncType::Void) = sy.function_type(&ident){
                            std::mem::drop(sy);
                            std::mem::drop(g);
                            std::mem::drop(m);
                            let exp = &rparams.exp;
                            let mut s = exp.get_koopa();
                            let mut ss = "".to_string();
                            let mut pre_call = "".to_string();
                            if let Ok(i) = s.parse::<i32>() {
                                ss += &format!("\tcall @{}(",ident);
                                ss += &format!("{}", i);
                            } else {
                                pre_call += &s;
                                ss += &format!("\tcall @{}(%{}",ident, get_reg_idx(&s));
                            }
                            for r in &rparams.exp_vec{
                                s = r.get_koopa();
                                if let Ok(i) = s.parse::<i32>() {
                                    ss += &format!(", {}", i);
                                } else {
                                    pre_call += &s;
                                    ss += &format!(", %{}", get_reg_idx(&s));
                                }
                            }
                            ss += ")\n";
                            let s = pre_call + &ss;
                            s
                        } else {
                            unreachable!()
                        }
                    } else {
                        if let Some(FuncType::Int) = sy.function_type(&ident){
                            let rst = add_reg_idx();
                            format!("\t%{} = call @{}()\n", rst, ident)
                        } else if let Some(FuncType::Void) = sy.function_type(&ident){
                            format!("\tcall @{}()\n", ident)
                        } else {
                            unreachable!()
                        }
                    }
                } else {
                    unreachable!();
                }
            } else {
                "".to_string()
            }
        }
    }
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

impl GetKoopa for Lval{
    fn get_koopa(&self) -> String {
        let mut symbol_id = 0;
        let mut raw_ptr_bool = false;
        {
            let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
            let mut g = &m.borrow_mut().get_mut().now_symbol.as_ref().unwrap();
            let mut go = g.lock().unwrap();
            symbol_id = go.exist_var_symbol(&self.ident).unwrap();
            raw_ptr_bool = go.is_raw_ptr(&self.ident);
        }
        if raw_ptr_bool{
            let mut s = "".to_string();
            let mut first:bool = true;
            let mut last_used = 0;
            for idx_exp in &self.array_idx{
                let idx = idx_exp.get_koopa();
                if first{
                    if let Ok(i) = idx.parse::<i32>(){
                        let unique_name = format!("{}_{}", self.ident, symbol_id);
                        let tmp1 = add_reg_idx();
                        s += &format!("\t%{} = load @{}\n",tmp1, unique_name);
                        let tmp = add_reg_idx();
                        s += &format!("\t%{} = getptr %{}, {}\n",tmp,
                                      tmp1,
                                      i);
                        last_used = tmp;
                    } else {
                        let last_reg = get_reg_idx(&idx);
                        let unique_name = format!("{}_{}", self.ident, symbol_id);
                        let tmp1 = add_reg_idx();
                        let tmp = add_reg_idx();
                        s += &(idx + &format!("\t%{} = load @{}\n",tmp1 ,
                                              unique_name) +
                            &format!("\t%{} = getptr %{}, %{}\n", tmp, tmp1,
                                     last_reg));
                        last_used = tmp;
                    }
                    first = false;
                } else {
                    if let Ok(i) = idx.parse::<i32>(){
                        let tmp = add_reg_idx();
                        s += &format!("\t%{} = getelemptr %{}, {}\n",tmp, last_used, i);
                        last_used = tmp;
                    } else {
                        let last_reg = get_reg_idx(&idx);
                        let tmp = add_reg_idx();
                        s += &(idx + &format!("\t%{} = getelemptr %{}, %{}\n",tmp,
                                              last_used , last_reg));
                        last_used = tmp;
                    }
                }
            }
            s
        } else {
            let mut s = "".to_string();
            let mut first:bool = true;
            let mut last_used = 0;
            for idx_exp in &self.array_idx{
                let idx = idx_exp.get_koopa();
                if first{
                    if let Ok(i) = idx.parse::<i32>(){
                        let tmp = add_reg_idx();
                        let unique_name = format!("{}_{}", self.ident, symbol_id);
                        s += &format!("\t%{} = getelemptr @{}, {}\n",tmp, unique_name,
                                      i);
                        last_used = tmp;
                    } else {
                        let last_reg = get_reg_idx(&idx);
                        let tmp = add_reg_idx();
                        let unique_name = format!("{}_{}", self.ident, symbol_id);
                        s += &(idx + &format!("\t%{} = getelemptr @{}, %{}\n",tmp,
                                              unique_name, last_reg));
                        last_used = tmp;
                    }
                    first = false;
                } else {
                    if let Ok(i) = idx.parse::<i32>(){
                        let tmp = add_reg_idx();
                        s += &format!("\t%{} = getelemptr %{}, {}\n",tmp, last_used, i);
                        last_used = tmp;
                    } else {
                        let last_reg = get_reg_idx(&idx);
                        let tmp = add_reg_idx();
                        s += &(idx + &format!("\t%{} = getelemptr %{}, %{}\n",tmp,
                                              last_used, last_reg));
                        last_used = tmp;
                    }
                }
            }
            s
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
            } else if let Some(a) = &self.lval {
                let mut const_bool = false;
                let mut global_bool = false;
                let mut var_bool = false;
                let mut raw_ptr_bool = false;
                {
                    let mut g = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                    let mut k = g.borrow_mut().get_mut();
                    let mut s = k.now_symbol.as_ref().unwrap().lock().unwrap();
                    const_bool = s.exist_const_symbol(&a.ident)
                }
                {
                    let mut g = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                    let mut k = g.borrow_mut().get_mut();
                    let mut gg = k.global_symbol_table.as_ref().unwrap().lock().unwrap();
                    global_bool = gg.exist_global_inited_symbol(&a.ident);
                }
                {
                    let mut g = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                    let mut k = g.borrow_mut().get_mut();
                    let mut s = k.now_symbol.as_ref().unwrap().lock().unwrap();
                   if let Some(_) = s.exist_var_symbol(&a.ident) {
                       var_bool = true;
                   } else {
                       var_bool = false;
                   }
               }
               {
                    let mut g = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                    let mut k = g.borrow_mut().get_mut();
                    let mut s = k.now_symbol.as_ref().unwrap().lock().unwrap();
                    raw_ptr_bool = s.is_raw_ptr(&a.ident);
               }
               let mut g = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
               let mut m = g.borrow_mut().get_mut();
               let mut k = m.now_symbol.as_ref().unwrap().lock().unwrap();
               if (const_bool || global_bool) && !var_bool{
                    format!("{}", k.get_value(&a.ident))
               } else if let Some(symbol_id) = k.exist_var_symbol(&a.ident){
                   let unique_name = format!("{}_{}", a.ident, symbol_id);
                   if !k.is_var(&a.ident){
                       std::mem::drop(k);
                       std::mem::drop(m);
                       std::mem::drop(g);
                       if raw_ptr_bool{
                           let mut s = "".to_string();
                           let mut first:bool = true;
                           let mut last_used = 0;
                           for idx_exp in &a.array_idx{
                               let idx = idx_exp.get_koopa();
                               if first{
                                   if let Ok(i) = idx.parse::<i32>(){
                                       let tmp1 = add_reg_idx();
                                       s += &format!("\t%{} = load @{}\n",tmp1, unique_name);
                                       let tmp = add_reg_idx();
                                       s += &format!("\t%{} = getptr %{}, {}\n",tmp,
                                                     tmp1,
                                                     i);
                                       last_used = tmp;
                                   } else {
                                       let last_reg = get_reg_idx(&idx);
                                       let unique_name = format!("{}_{}", a.ident, symbol_id);
                                       let tmp1 = add_reg_idx();
                                       let tmp = add_reg_idx();
                                       s += &(idx + &format!("\t%{} = load @{}\n",tmp1 ,
                                       unique_name) +
                                           &format!("\t%{} = getptr %{}, %{}\n", tmp, tmp1,
                                                    last_reg));
                                       last_used = tmp;
                                   }
                                   first = false;
                               } else {
                                   if let Ok(i) = idx.parse::<i32>(){
                                       // let tmp1 = add_reg_idx();
                                       // s += &format!("\t%{} = load %{}\n", tmp1, last_used);
                                       let tmp = add_reg_idx();
                                       s += &format!("\t%{} = getelemptr %{}, {}\n",tmp, last_used, i);
                                       last_used = tmp;
                                   } else {
                                       let last_reg = get_reg_idx(&idx);
                                       // let tmp1 = add_reg_idx();
                                       // s += &format!("\t%{} = load %{}\n", tmp1, last_used);
                                       let tmp = add_reg_idx();
                                       s += &(idx + &format!("\t%{} = getelemptr %{}, %{}\n",tmp,
                                                            last_used , last_reg));
                                       last_used = tmp;
                                   }
                               }
                           }
                            let mut dim: Vec<i32> = Vec::new();
                           {
                               let mut g = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                               let mut m = g.borrow_mut().get_mut();
                               let mut k = m.now_symbol.as_ref().unwrap().lock().unwrap();
                               dim = k.get_dimension(&a.ident).unwrap();
                           }
                           if a.array_idx.len() == 0{
                               let tmp1 = add_reg_idx();
                               s += &format!("\t%{} = getptr @{}, 0\n", tmp1,
                                             &unique_name);
                               last_used = tmp1;
                           } else if dim.len() == a.array_idx.len() {
                               let reg = add_reg_idx();
                               s += &format!("\t%{} = load %{}\n", reg, last_used);
                           } else {
                               let reg = add_reg_idx();
                               s += &format!("\t%{} = getelemptr %{}, 0\n",reg, last_used);
                           }
                           s
                           // } else {
                           //
                           //      for i in (a.array_idx.len()..dim.len()){
                           //          let tmp1 = add_reg_idx();
                           //          if last_used == 0{
                           //              s += &format!("\t%{} = getptr @{}, 0\n", tmp1,
                           //                            &unique_name);
                           //              last_used = tmp1;
                           //          } else {
                           //              s += &format!("\t%{} = load %{}\n", tmp1, last_used);
                           //              let tmp = add_reg_idx();
                           //              s += &format!("\t%{} = getptr %{}, 0\n",tmp, tmp1);
                           //              last_used = tmp;
                           //          }
                           //      }
                           //     s
                           // }
                       } else {
                           let mut s = "".to_string();
                           let mut first:bool = true;
                           let mut last_used = 0;
                           for idx_exp in &a.array_idx{
                               let idx = idx_exp.get_koopa();
                               if first{
                                   if let Ok(i) = idx.parse::<i32>(){
                                       let tmp = add_reg_idx();
                                       let unique_name = format!("{}_{}", a.ident, symbol_id);
                                       s += &format!("\t%{} = getelemptr @{}, {}\n",tmp, unique_name,
                                                     i);
                                       last_used = tmp;
                                   } else {
                                       let last_reg = get_reg_idx(&idx);
                                       let tmp = add_reg_idx();
                                       let unique_name = format!("{}_{}", a.ident, symbol_id);
                                       s += &(idx + &format!("\t%{} = getelemptr @{}, %{}\n",tmp,
                                                             unique_name, last_reg));
                                       last_used = tmp;
                                   }
                                   first = false;
                               } else {
                                   if let Ok(i) = idx.parse::<i32>(){
                                       let tmp = add_reg_idx();
                                       s += &format!("\t%{} = getelemptr %{}, {}\n",tmp, last_used, i);
                                       last_used = tmp;
                                   } else {
                                       let last_reg = get_reg_idx(&idx);
                                       let tmp = add_reg_idx();
                                       s += &(idx + &format!("\t%{} = getelemptr %{}, %{}\n",tmp,
                                                             last_used, last_reg));
                                       last_used = tmp;
                                   }
                               }
                           }
                           let mut dim: Vec<i32> = Vec::new();
                           {
                               let mut g = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                               let mut m = g.borrow_mut().get_mut();
                               let mut k = m.now_symbol.as_ref().unwrap().lock().unwrap();
                               dim = k.get_dimension(&a.ident).unwrap();
                           }
                           if dim.len() == a.array_idx.len(){
                               let reg = add_reg_idx();
                               s += &format!("\t%{} = load %{}\n", reg, last_used);
                           } else if a.array_idx.len() == 0{
                               let tmp1 = add_reg_idx();
                               s += &format!("\t%{} = getelemptr @{}, 0\n",tmp1, &unique_name);
                           } else {
                               let tmp1 = add_reg_idx();
                               s += &format!("\t%{} = getelemptr %{}, 0\n",tmp1, last_used);
                           }
                           s
                           // else {
                           //     for i in (a.array_idx.len()..dim.len()){
                           //         if last_used == 0{
                           //             let tmp1 = add_reg_idx();
                           //             s += &format!("\t%{} = getelemptr @{}, 0\n",tmp1, &unique_name);
                           //             last_used = tmp1;
                           //         } else {
                           //             let tmp = add_reg_idx();
                           //             s += &format!("\t%{} = getelemptr %{}, 0\n",tmp, last_used);
                           //             last_used = tmp;
                           //         }
                           //     }
                           //     s
                           // }
                       }
                   }else {
                       std::mem::drop(k);
                       std::mem::drop(m);
                       std::mem::drop(g);
                       let tmp = add_reg_idx();
                       let mut is_var:bool =  false;
                       let mut symbol_id = 0;
                       {
                           let mut g = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                           let mut m = g.borrow_mut().get_mut();
                           let mut k = m.now_symbol.as_ref().unwrap().lock().unwrap();
                           k.set_var_reg(&a.ident, tmp);
                           symbol_id = k.exist_var_symbol(&a.ident).unwrap();
                           is_var = k.is_var(&a.ident);
                       }
                       let unique_name = (&a.ident).to_string() + &format!("_{}", symbol_id);
                       format!("\t%{} = load @{}\n", tmp, unique_name)
                   }
               } else {
                   "".to_string()
               }
           } else {
               "".to_string()
           }
       }
    }
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
                let a_reg_idx = get_reg_idx(&a_string);
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx(&c_string);
                let e = add_reg_idx();
                test(a_string, c_string, a_reg_idx, c_reg_idx, e, operation)
            } else {
                "ParserError".to_string()
            }
        }
    }
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
                let a_reg_idx = get_reg_idx(&a_string);
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx(&c_string);
                let reg_idx = add_reg_idx();
                test(a_string, c_string, a_reg_idx, c_reg_idx, reg_idx, operation)
            } else {
                "ParserError".to_string()
            }
        }
    }
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
                let a_reg_idx = get_reg_idx(&a_string);
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx(&c_string);
                let reg_idx = add_reg_idx();
                test(a_string, c_string, a_reg_idx, c_reg_idx, reg_idx, operation)
            } else {
                "ParserError".to_string()
            }
        }
    }
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
                let a_reg_idx = get_reg_idx(&a_string);
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx(&c_string);
                let reg_idx = add_reg_idx();
                test(a_string, c_string, a_reg_idx, c_reg_idx, reg_idx, operation)
            } else {
                "ParserError".to_string()
            }
        }
    }
}

impl GetKoopa for LAndExp{
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.eq_exp{
            a.get_koopa()
        } else {
            if let Some((a, c )) = &self.land_operate{
                let mut operation = "and".to_string();
                let a_string = a.get_koopa();
                let a_reg_idx = get_reg_idx(&a_string);
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx(&c_string);
                let e_reg = add_reg_idx();
                let d_reg = add_reg_idx();
                let reg_idx = add_reg_idx();
                if let Ok(d) = c_string.parse::<i32>(){
                    if let Ok(e) = a_string.parse::<i32>(){
                        let s1 = format!("\t%{} = ne 0, {}\n",e_reg, e);
                        let s2 = format!("\t%{} = ne 0, {}\n",d_reg, d);
                        land_code_gen(e_reg, d_reg, s1, s2)
                    }
                    else {
                        let s1 = format!("\t%{} = ne 0, %{}\n",e_reg, a_reg_idx);
                        let s2 = format!("\t%{} = ne 0, {}\n",d_reg, d);
                        let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                        let mut g = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
                        if let Some(_) = g.exist_var_symbol(&a_string){
                            land_code_gen(e_reg, d_reg, s1, s2) } else {
                            let s1_string = a_string + &s1;
                            land_code_gen(e_reg, d_reg, s1_string, s2)
                        }
                    }
                } else {
                    if let Ok(e) = a_string.parse::<i32>(){
                        let s1 = format!("\t%{} = ne 0, {}\n",e_reg, e);
                        let s2 = format!("\t%{} = ne 0, %{}\n",d_reg, c_reg_idx);
                        let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                        let mut g = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
                        if let Some(_) = g.exist_var_symbol(&c_string){
                            land_code_gen(e_reg, d_reg, s1, s2)
                        } else {
                            let s2_string = c_string + &s2;
                            land_code_gen(e_reg, d_reg, s1, s2_string)
                        }
                    } else {
                        let s1 = format!("\t%{} = ne 0, %{}\n",e_reg, a_reg_idx);
                        let s2 = format!("\t%{} = ne 0, %{}\n",d_reg, c_reg_idx);
                        let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                        let mut g = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
                        if let Some(_) = g.exist_var_symbol(&c_string){
                            if let Some(_) = g.exist_var_symbol(&a_string){
                                land_code_gen(e_reg, d_reg, s1, s2)
                            } else {
                                let s1_string = a_string + &s1;
                                land_code_gen(e_reg, d_reg, s1_string, s2)
                            }
                        } else {
                            if let Some(_) = g.exist_var_symbol(&a_string){
                                let s2_string = c_string + &s2;
                                land_code_gen(e_reg, d_reg, s1, s2_string)
                            } else {
                                let s1_string = a_string + &s1;
                                let s2_string = c_string + &s2;
                                land_code_gen(e_reg, d_reg, s1_string, s2_string)
                            }
                        }
                    }
                }
            } else {
                "ParserError".to_string()
            }
        }
    }
}

impl GetKoopa for LOrExp{
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.land_exp{
            a.get_koopa()
        } else {
            if let Some((a, c )) = &self.lor_operate{
                let mut operation = "or".to_string();
                let a_string = a.get_koopa();
                let a_reg_idx = get_reg_idx(&a_string);
                let c_string = c.get_koopa();
                let c_reg_idx = get_reg_idx(&c_string);
                let e_reg = add_reg_idx();
                let d_reg = add_reg_idx();
                if let Ok(d) = c_string.parse::<i32>(){
                    if let Ok(e) = a_string.parse::<i32>(){
                        let s1 = format!("\t%{} = ne 0, {}\n",e_reg, e);
                        let s2 = format!("\t%{} = ne 0, {}\n",d_reg, d);
                        lor_code_gen(e_reg, d_reg, s1, s2)
                    }
                    else {
                        let s1 = format!("\t%{} = ne 0, %{}\n",e_reg, a_reg_idx);
                        let s2 = format!("\t%{} = ne 0, {}\n",d_reg, d);
                        let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                        let mut g = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
                        if let Some(_) = g.exist_var_symbol(&a_string){
                            lor_code_gen(e_reg, d_reg, s1, s2) } else {
                            let s1_string = a_string + &s1;
                            lor_code_gen(e_reg, d_reg, s1_string, s2)
                        }
                    }
                } else {
                    if let Ok(e) = a_string.parse::<i32>(){
                        let s1 = format!("\t%{} = ne 0, {}\n",e_reg, e);
                        let s2 = format!("\t%{} = ne 0, %{}\n",d_reg, c_reg_idx);
                        let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                        let mut g = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
                        if let Some(_) = g.exist_var_symbol(&c_string){
                            lor_code_gen(e_reg, d_reg, s1, s2)
                        } else {
                            let s2_string = c_string + &s2;
                            lor_code_gen(e_reg, d_reg, s1, s2_string)
                        }
                    } else {
                        let s1 = format!("\t%{} = ne 0, %{}\n",e_reg, a_reg_idx);
                        let s2 = format!("\t%{} = ne 0, %{}\n",d_reg, c_reg_idx);
                        let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                        let mut g = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
                        if let Some(_) = g.exist_var_symbol(&c_string){
                            if let Some(_) = g.exist_var_symbol(&a_string){
                                lor_code_gen(e_reg, d_reg, s1, s2)
                            } else {
                                let s1_string = a_string + &s1;
                                lor_code_gen(e_reg, d_reg, s1_string, s2)
                            }
                        } else {
                            if let Some(_) = g.exist_var_symbol(&a_string){
                                let s2_string = c_string + &s2;
                                lor_code_gen(e_reg, d_reg, s1, s2_string)
                            } else {
                                let s1_string = a_string + &s1;
                                let s2_string = c_string + &s2;
                                lor_code_gen(e_reg, d_reg, s1_string, s2_string)
                            }
                        }
                    }
                }
                // if let Ok(d) = c_string.parse::<i32>(){
                //     if let Ok(e) = a_string.parse::<i32>(){
                //         let s1 = format!("\t%{} = ne 0, {}\n",e_reg, e);
                //         let s2 = format!("\t%{} = ne 0, {}\n",d_reg, d);
                //         let reg_idx = add_reg_idx();
                //         s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx, operation,e_reg, d_reg)
                //     } else {
                //         let branch_count = add_branch_count();
                //         let s1 = format!("\t%{} = ne 0, %{}\n",e_reg, a_reg_idx);
                //         let s2 = format!("\t%{} = ne 0, {}\n",d_reg, d);
                //         let s3 =  format!("\tbr %{}, %then_{}", e_reg, branch_count);
                //         let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                //         let mut g = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
                //         if let Some(_) = g.exist_var_symbol(&a_string){
                //             s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                //         } else {
                //             let s4 = format!("%then_{}\n", branch_count);
                //             a_string + &s1 + &s3 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,
                //                                              operation, e_reg, d_reg)
                //         }
                //     }
                // } else {
                //     if let Ok(e) = a_string.parse::<i32>(){
                //         let s1 = format!("\t%{} = ne 0, {}\n",e_reg, e);
                //         let s2 = format!("\t%{} = ne 0, %{}\n",d_reg, c_reg_idx);
                //         let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                //         let mut g = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
                //         if let Some(_) = g.exist_var_symbol(&c_string){
                //             s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                //         } else {
                //             c_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation, e_reg, d_reg)
                //         }
                //     } else {
                //         let s1 = format!("\t%{} = ne 0, %{}\n",e_reg, a_reg_idx);
                //         let s2 = format!("\t%{} = ne 0, %{}\n",d_reg, c_reg_idx);
                //         let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                //         let mut g = m.borrow_mut().get_mut().now_symbol.as_ref().unwrap().lock().unwrap();
                //         if let Some(_) = g.exist_var_symbol(&c_string){
                //             if let Some(_) = g.exist_var_symbol(&a_string){
                //                 s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                //                                     e_reg, d_reg)
                //             } else {
                //                 a_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                //                                                 e_reg, d_reg)
                //             }
                //         } else {
                //             if let Some(_) = g.exist_var_symbol(&a_string){
                //                 c_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                //                                                 e_reg, d_reg)
                //             } else {
                //                 a_string + &c_string + &s1 + &s2 + &format!("\t%{} = {} %{}, %{}\n", reg_idx,operation,
                //                                                             e_reg, d_reg)
                //             }
                //         }
                //     }
                // }
            } else {
                "ParserError".to_string()
            }
        }
    }
}
impl GetKoopa for Decl{
    fn get_koopa(&self) -> String {
        if let Some(a) = &self.const_decl{
            a.get_koopa()
        } else if let Some(b) = &self.var_decl{
            b.get_koopa()
        } else {
            "".to_string()
        }
    }
}

impl GetKoopa for VarDecl{
    fn get_koopa(&self) -> String {
        let mut s = "".to_string();
        s += &self.var_def.get_koopa();
        for var in &self.var_def_vec{
            s += &var.get_koopa();
        }
        s
    }
}

impl GetKoopa for VarDef{
    fn get_koopa(&self) -> String{
        let s = self.get_name();
        if !self.array_init.is_empty(){
            let mut unique_name = "".to_string();
            {
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = m.borrow_mut().get_mut();
                let mut go =  g.now_symbol.as_mut().unwrap().lock().unwrap();
                unique_name = self.get_name() + &format!("_{}",go.symbol_id)
            }
            let mut total = format!("\t@{} = alloc ", unique_name );
            let mut ss = "".to_string();
            let mut first:bool = true;
            let mut dim_idx: Vec<i32> = Vec::new();
            let mut a = self.array_init.clone();
            a.reverse();
            for a in &(a){
                let idx = a.exp.eval_const().unwrap();
                let Value::Int(i) = idx;
                if first{
                    ss = format!("[i32, {}]", i);
                    dim_idx.push(i);
                    first = false;
                } else {
                    ss = format!("[{}, {}]", ss, i);
                    dim_idx.push(i);
                }
            }
            {
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = m.borrow_mut().get_mut();
                let mut go =  g.now_symbol.as_mut().unwrap().lock().unwrap();
                go.insert_var_point_symbol((&s).to_string(), &dim_idx);
            }
            total += &ss;
            total += "\n";
            if let Some(initval) = &self.initval{
                if let Some(var_array_init) = &initval.array_init_vec{
                    // dim_idx.reverse();
                    let mut a = 0;
                    let mut vec = generate_init_val(var_array_init, &dim_idx, &mut a,
                                                0);
                    let product = dim_idx.iter().fold(1, |x, a| x * a);
                    let len = vec.len() as i32;
                    for i in (0..product - len){
                        vec.push(0);
                    }
                    let mut idx = 0 as usize;
                    for i in vec{
                        total += &get_localtion(&unique_name, idx, &dim_idx);
                        total += &format!("\tstore {}, %{}\n",i, get_reg_idx(&total));
                    }
                } else {
                    total += "\n";
                }
            } else {
                total += "\n";
            }
            total
        }else{
            if let Some(i) = &self.initval{
                let mut k = i.get_koopa();
                if let Ok(l)= k.parse::<i32>(){
                    let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                    let mut g = m.borrow_mut().get_mut();
                    let mut go =  g.now_symbol.as_mut().unwrap().lock().unwrap();
                    go.insert_var_symbol(s, Some(l));
                    let unique_name = self.get_name() + &format!("_{}",go.symbol_id);
                    format!("\t@{} = alloc {}\n",unique_name, "i32")
                        + &format!("\tstore {}, @{}\n",l, unique_name)
                } else {
                    let mut unique_name = "".to_string();
                    {
                        let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                        let mut g = m.borrow_mut().get_mut();
                        let mut go =  g.now_symbol.as_mut().unwrap().lock().unwrap();
                        go.insert_var_symbol((&s).to_string(), None);
                        unique_name = self.get_name() + &format!("_{}",go.symbol_id);
                    }
                    k + &format!("\t@{} = alloc {}\n",unique_name, "i32")
                        + &format!("\tstore %{}, @{}\n",get_reg_idx(&s), unique_name)
                }
            } else {
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = m.borrow_mut().get_mut();
                let mut go =  g.now_symbol.as_mut().unwrap().lock().unwrap();
                go.insert_var_symbol((&s).to_string(), None);
                let unique_name = self.get_name() + &format!("_{}",go.symbol_id);
                format!("\t@{} = alloc {}\n", unique_name, "i32")
            }
        }
    }
    // fn get_koopa(&self) -> String {
    //     let s = self.get_name();
    //     if let Some(a) = &self.array_init{
    //         let mut s = "".to_string();
    //         let Value::Int(array_len) = a.exp.eval_const().unwrap();
    //         let mut unique_name = "".to_string();
    //         {
    //             let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
    //             let mut g = m.borrow_mut().get_mut();
    //             let mut go =  g.now_symbol.as_mut().unwrap().lock().unwrap();
    //             go.insert_var_point_symbol((&self.ident).to_string());
    //             unique_name = ((&self.ident).to_string() + &format!("_{}",go.symbol_id));
    //         }
    //         s += &format!("\t@{} = alloc [i32, {}]\n", unique_name, array_len);
    //         if let Some(initVal) =  &self.initval{
    //             let array_init_vec = &initVal.array_init_vec.as_ref().unwrap();
    //             let first = &array_init_vec.array_init;
    //             let other = &array_init_vec.array_init_vec;
    //             let first_string = first.get_koopa();
    //             if let Ok(i) = first_string.parse::<i32>(){
    //                 let idx = add_reg_idx();
    //                 s += &format!("\t%{} = getelemptr @{}, 0\n\tstore {}, %{}\n", idx, unique_name, i, idx);
    //             } else {
    //                 let s_reg = get_reg_idx(&first_string);
    //                 let reg = add_reg_idx();
    //                 s += &first_string;
    //                 s += &format!("\t%{} = getelemptr @{}, 0\n\tstore %{}, %{}\n", reg, unique_name, s_reg,
    //                               reg);
    //             }
    //             if !other.is_empty(){
    //                 let mut count = 1;
    //                 for i in other{
    //                     let i_string = i.get_koopa();
    //                     if let Ok(i) = i_string.parse::<i32>(){
    //                         let idx = add_reg_idx();
    //                         s += &format!("\t%{} = getelemptr @{}, {}\n\tstore {}, %{}\n", idx,
    //                                       unique_name, count,i, idx);
    //                     } else {
    //                         let s_reg = get_reg_idx(&first_string);
    //                         let reg = add_reg_idx();
    //                         s += &i_string;
    //                         s += &format!("\t%{} = getelemptr @{}, {}\n\tstore %{}, %{}\n", reg,
    //                                       unique_name, count, s_reg, reg);
    //                     }
    //                     count = count + 1;
    //                 }
    //             }
    //         }
    //         s
    //     } else {
    //         if let Some(i) = &self.initval{
    //             let mut k = i.get_koopa();
    //             if let Ok(l)= k.parse::<i32>(){
    //                 let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
    //                 let mut g = m.borrow_mut().get_mut();
    //                 let mut go =  g.now_symbol.as_mut().unwrap().lock().unwrap();
    //                 go.insert_var_symbol(s, Some(l));
    //                 let unique_name = self.get_name() + &format!("_{}",go.symbol_id);
    //                 format!("\t@{} = alloc {}\n",unique_name, "i32")
    //                     + &format!("\tstore {}, @{}\n",l, unique_name)
    //             } else {
    //                 let mut unique_name = "".to_string();
    //                 {
    //                     let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
    //                     let mut g = m.borrow_mut().get_mut();
    //                     let mut go =  g.now_symbol.as_mut().unwrap().lock().unwrap();
    //                     go.insert_var_symbol((&s).to_string(), None);
    //                     unique_name = self.get_name() + &format!("_{}",go.symbol_id);
    //                 }
    //                 k + &format!("\t@{} = alloc {}\n",unique_name, "i32")
    //                     + &format!("\tstore %{}, @{}\n",get_reg_idx(&s), unique_name)
    //             }
    //         } else {
    //             let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
    //             let mut g = m.borrow_mut().get_mut();
    //             let mut go =  g.now_symbol.as_mut().unwrap().lock().unwrap();
    //             go.insert_var_symbol((&s).to_string(), None);
    //             let unique_name = self.get_name() + &format!("_{}",go.symbol_id);
    //             format!("\t@{} = alloc {}\n", unique_name, "i32")
    //         }
    //     }
    // }
}

impl GetName for VarDef{
    fn get_name(&self) -> String {
        (&self.ident).to_string()
    }
}

impl GetKoopa for InitVal{
    fn get_koopa(&self) -> String {
        if let Some(a) = self.exp.as_ref().unwrap().eval_const(){
            if let Value::Int(i) = a {
                format!("{}", i)
            } else {
                "".to_string()
            }
        } else {
            self.exp.as_ref().unwrap().get_koopa()
        }
    }
}
impl InitVal{
    fn get_global_definition(&self) -> String {
        if let Some(a) = self.exp.as_ref().unwrap().eval_const(){
            if let Value::Int(i) = a {
                format!("{}", i)
            } else {
                "".to_string()
            }
        } else {
            unreachable!()
        }
    }
}

impl GetKoopa for ConstDecl{
    fn get_koopa(&self) -> String {
        //todo: 没有加vec的处理
        let mut s = "".to_string();
        if let Some(a) = self.const_def.eval_const(){
            let Value::Int(i) = a;
            let s = self.const_def.get_name();
            {
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = m.borrow_mut().get_mut();
                let mut k = g.now_symbol.as_mut().unwrap().lock().unwrap();
                k.insert_const_symbol(s, i);
            }
        } else {
            //todo 这是const array的定义部分
            s += &self.const_def.get_koopa();
        }
        if let Some(v) = &self.const_def_vec{
            for q in v{
                if let Some(a) = self.const_def.eval_const(){
                    let Value::Int(i) = a;
                    let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                    let mut g = m.borrow_mut().get_mut();
                    let mut k = g.now_symbol.as_mut().unwrap().lock().unwrap();
                    k.insert_const_symbol(q.get_name(), i);
                } else {
                    s += &q.get_koopa();
                }
            }
        }
        s
    }
}
impl ConstDef{
    fn get_global_definition(&self) -> String{
        let s = self.get_name();
        if !self.array_idx.is_empty(){
            let mut unique_name = "".to_string();
            {
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = m.borrow_mut().get_mut();
                let mut go =  g.global_symbol_table.as_mut().unwrap().lock().unwrap();
                unique_name = self.get_name() + &format!("_{}",go.symbol_id);
            }
            let mut total = format!("global @{} = alloc ", unique_name );
            let mut ss = "".to_string();
            let mut first:bool = true;
            let mut dim_idx: Vec<i32> = Vec::new();
            let mut b = self.array_idx.clone();
            b.reverse();
            for a in &b{
                let idx = a.exp.eval_const().unwrap();
                let Value::Int(i) = idx;
                if first{
                    ss = format!("[i32, {}]", i);
                    dim_idx.push(i);
                    first = false;
                } else {
                    ss = format!("[{}, {}]", ss, i);
                    dim_idx.push(i);
                }
            }
            {
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = m.borrow_mut().get_mut();
                let mut go =  g.global_symbol_table.as_mut().unwrap().lock().unwrap();
                go.insert_const_point_symbol((&s).to_string(), &dim_idx);
            }
            total += &ss;
            if let Some(const_init_val) = &self.const_init_val{
                if let Some(const_array_init) = &const_init_val.array_init_vec{
                    // dim_idx.reverse();
                    let mut a = 0;
                    total += &init_var_handler(generate_const_init_val(const_array_init, &dim_idx,
                                                                      &mut a, 0), &dim_idx);
                }
            }
            total
        } else {
            unreachable!()
        }
    }
    // fn get_global_definition(&self) -> String{
    //     let mut s = "".to_string();
    //     if let Some(const_exp) = &self.array_idx{
    //         let array_len = const_exp.exp.eval_const().unwrap();
    //         let Value::Int(i) = array_len;
    //         let mut unique_name = "".to_string();
    //         {
    //             let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
    //             let mut g = m.borrow_mut().get_mut();
    //             let mut go =  g.global_symbol_table.as_mut().unwrap().lock().unwrap();
    //             go.insert_const_point_symbol((&s).to_string());
    //             unique_name = self.get_name() + &format!("_{}",go.symbol_id);
    //         }
    //         s += &format!("\tglobal @{} = alloc [i32, {}]", unique_name,i);
    //         if let Some(const_init_val) = &self.const_init_val{
    //             let array_init = &const_init_val.array_init_vec.as_ref().unwrap();
    //             let first = &array_init.array_init;
    //             let other = &array_init.array_init_vec;
    //             let Value::Int(first_val) = first.exp.eval_const().unwrap();
    //             s += &format!(", {{{}", first_val);
    //             if !other.is_empty(){
    //                 for i in other{
    //                     let Value::Int(j) = i.exp.eval_const().unwrap();
    //                     s += &format!(", {}", j);
    //                 }
    //             }
    //             s += "}";
    //         }
    //         s += "\n";
    //         s
    //     } else {
    //         unreachable!()
    //     }
    // }
}
// this impl only for the const array
impl GetKoopa for ConstDef{
    fn get_koopa(&self) -> String{
        let mut s = "".to_string();
        if !self.array_idx.is_empty(){
            let mut unique_name = "".to_string();
            {
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = m.borrow_mut().get_mut();
                let mut go =  g.now_symbol.as_mut().unwrap().lock().unwrap();
                unique_name = self.get_name() + &format!("_{}",go.symbol_id);
            }
            let mut total = format!("\t@{} = alloc", unique_name );
            let mut ss = "".to_string();
            let mut first:bool = true;
            let mut dim_idx: Vec<i32> = Vec::new();
            let mut b = self.array_idx.clone();
            b.reverse();
            for a in &self.array_idx{
                let idx = a.exp.eval_const().unwrap();
                let Value::Int(i) = idx;
                if first{
                    ss = format!("[i32, {}]", i);
                    dim_idx.push(i);
                    first = false;
                } else {
                    ss = format!("[{}, {}]", ss, i);
                    dim_idx.push(i);
                }
            }
            {
                let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                let mut g = m.borrow_mut().get_mut();
                let mut go =  g.now_symbol.as_mut().unwrap().lock().unwrap();
                go.insert_const_point_symbol((&s).to_string(), &dim_idx);
            }
            total += &ss;
            total += "\n";
            if let Some(const_init_val) = &self.const_init_val{
                if let Some(const_array_init) = &const_init_val.array_init_vec{
                    // dim_idx.reverse();
                    let mut a = 0;
                    let mut vec = generate_const_init_val(const_array_init, &dim_idx, &mut a,
                                                    0);
                    let product = dim_idx.iter().fold(1, |x, a| x * a);
                    let len = vec.len() as i32;
                    for i in (0..product - len){
                        vec.push(0);
                    }
                    let mut idx = 0 as usize;
                    for i in vec{
                        total += &get_localtion(&unique_name, idx, &dim_idx);
                        total += &format!("\tstore {}, %{}\n",i, get_reg_idx(&total));
                    }
                }
            }
            total
        } else {
            unreachable!()
        }
    }
    // fn get_koopa(&self) -> String {
    //     let mut s = "".to_string();
    //     if let Some(const_exp) = &self.array_idx{
    //         let array_len = const_exp.exp.eval_const().unwrap();
    //         let Value::Int(i) = array_len;
    //         let mut unique_name = "".to_string();
    //         {
    //             let mut m = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
    //             let mut g = m.borrow_mut().get_mut();
    //             let mut go =  g.global_symbol_table.as_mut().unwrap().lock().unwrap();
    //             go.insert_const_point_symbol((&s).to_string());
    //             unique_name = self.get_name() + &format!("_{}",go.symbol_id);
    //         }
    //         s += &format!("\t@{} = alloc [i32, {}]", unique_name,i);
    //         if let Some(const_init_val) = &self.const_init_val{
    //             let array_init = &const_init_val.array_init_vec.as_ref().unwrap();
    //             let first = &array_init.array_init;
    //             let other = &array_init.array_init_vec;
    //             let Value::Int(first_val) = first.exp.eval_const().unwrap();
    //             s += &format!(", {{{}", first_val);
    //             if !other.is_empty(){
    //                 for i in other{
    //                     let Value::Int(j) = i.exp.eval_const().unwrap();
    //                     s += &format!(", {}", j);
    //                 }
    //             }
    //             s += "}";
    //         }
    //         s += "\n";
    //         s
    //     } else {
    //         unreachable!()
    //     }
    // }
}

impl EvalConst for ConstDef{
    fn eval_const(&self) -> Option<Value> {
        if !self.array_idx.is_empty(){
            return None;
        } else {
            let a = &self.const_init_val.as_ref().unwrap().const_exp.as_ref().unwrap().exp;
            a.eval_const()
        }
    }
}
impl GetName for ConstDef{
    fn get_name(&self) -> String {
        (&self.ident).to_string()
    }
}
impl EvalConst for LOrExp{
    fn eval_const(&self) -> Option<Value> {
        if let Some(a) = self.land_exp.as_ref(){
            a.eval_const()
        } else if let Some((lor, land)) = &self.lor_operate{
            let lor_val = lor.eval_const();
            if let Some(v1) = lor_val{
                if let Some(v2) = land.eval_const(){
                    let Value::Int(i1) = v1;
                    let Value::Int(i2) = v2;
                    return Some(Value::Int(if i1 != 0 || i2 != 0 {1} else {0}));
                } else {
                    return None;
                }
            } else {
                return None;
            }
        } else {
            return None;
        }
    }
}

impl EvalConst for LAndExp{
    fn eval_const(&self) -> Option<Value> {
        if let Some(a) = self.eq_exp.as_ref(){
            a.eval_const()
        } else if let Some((land, eq)) = &self.land_operate{
            let land_val = land.eval_const();
            if let Some(v1) = land_val{
                if let Some(v2) = eq.eval_const(){
                    let Value::Int(i1) = v1;
                    let Value::Int(i2) = v2;
                    return Some(Value::Int(if i1 != 0 && i2 != 0{1} else {0}));
                } else {
                    return None;
                }
            } else {
                return None;
            }
        } else {
            return None;
        }
    }
}

impl EvalConst for EqExp{
    fn eval_const(&self) -> Option<Value> {
        if let Some(a) = self.rel_exp.as_ref(){
            a.eval_const()
        } else if let Some((eq, op, rel)) = &self.eq_operate{
            let eq_val = eq.eval_const();
            if let Some(v1) = eq_val{
                if let Some(v2) = rel.eval_const(){
                    let Value::Int(i1) = v1;
                    let Value::Int(i2) = v2;
                    match op{
                        EqOperation::Eq => return Some(Value::Int(if i1 == i2 {1} else {0})),
                        EqOperation::NEq => return Some(Value::Int(if i1 != i2 {1} else {0})),
                        _ => return None,
                    }
                } else {
                    return None;
                }
            } else {
                return None;
            }
        } else {
            return None;
        }
    }
}

impl EvalConst for RelExp{
    fn eval_const(&self) -> Option<Value> {
        if let Some(a) = self.add_exp.as_ref(){
            a.eval_const()
        } else if let Some((rel, op, add)) = &self.rel_operate{
            let rel_val = rel.eval_const();
            if let Some(v1) = rel_val{
                if let Some(v2) = add.eval_const(){
                    let Value::Int(i1) = v1;
                    let Value::Int(i2) = v2;
                    match op{
                        RelOperation::Greater => return Some(Value::Int(if i1 > i2 {1} else {0})),
                        RelOperation::Less => return Some(Value::Int(if i1 < i2 {1} else {0})),
                        RelOperation::LessEq => return Some(Value::Int(if i1 <= i2 {1} else {0})),
                        RelOperation::GreaterEq => return Some(Value::Int(if i1 >= i2 {1} else
                        {0})),
                        _ => return None,
                    }
                } else {
                    return None;
                }
            } else {
                return None;
            }
        } else {
            return None;
        }
    }
}

impl EvalConst for AddExp{
    fn eval_const(&self) -> Option<Value> {
        if let Some(a) = self.mul_exp.as_ref(){
            a.eval_const()
        } else if let Some((add_exp, op, mul_exp)) = &self.add_operate{
            let add_val = add_exp.eval_const();
            if let Some(v1) = add_val{
                if let Some(v2) = mul_exp.eval_const(){
                    let Value::Int(i1) = v1;
                    let Value::Int(i2) = v2;
                    match op{
                        AddOperator::Add => return Some(Value::Int(i1 + i2)),
                        AddOperator::Sub => return Some(Value::Int(i1 - i2)),
                        _ => return None,
                    }
                } else {
                    return None;
                }
            } else {
                return None;
            }
        } else {
            return None;
        }
    }
}

impl EvalConst for MulExp{
    fn eval_const(&self) -> Option<Value> {
        if let Some(exp) = &self.unary_exp{
            exp.eval_const()
        } else if let Some((mul, op, un)) = &self.mul_operate{
            let mul_val = mul.eval_const();
            if let Some(v1) = mul_val{
                if let Some(v2) = un.eval_const(){
                    let Value::Int(i1) = v1;
                    let Value::Int(i2) = v2;
                    match op{
                        MulOperator::Times => return Some(Value::Int(i1 * i2)),
                        MulOperator::Divide => return Some(Value::Int(i1 / i2)),
                        MulOperator::Quote => return Some(Value::Int(i1 % i2)),
                        _ => return None,
                    }
                } else {
                    return None;
                }
            } else {
                return None;
            }
        } else {
            return None;
        }
    }
}

impl EvalConst for UnaryExp{
    fn eval_const(&self) -> Option<Value> {
        if let Some(exp) = &self.primary_exp{
            exp.eval_const()
        } else if let Some((op, exp))  = &self.unary_exp{
            let mut tmp:Option<Value>;
            match op.unary_op{
                UnaryOperator::Add => tmp = exp.eval_const(),
                UnaryOperator::False => {
                    if let Some(v) = exp.eval_const(){
                        match v{
                            Value::Int(i) => {
                                if i == 0{
                                    tmp = Some(Value::Int(1));
                                } else {
                                    tmp = Some(Value::Int(0));
                                }
                            },
                            _ => tmp = None
                        }
                    } else {
                        tmp = None;
                    }
                } ,
                UnaryOperator::Sub => {
                    if let Some(v) = exp.eval_const(){
                        match v{
                            Value::Int(i) => tmp = Some(Value::Int(-i)),
                            _ => tmp = None,
                        }
                    } else {
                        tmp = None;
                    }
                },
                _ => tmp = None,
            }
            return tmp;
        } else {
            return None;
        }
    }
}

impl EvalConst for PrimaryExp{
    fn eval_const(&self) -> Option<Value> {
        if let Some(n) = self.num{
            Some(Value::Int(n))
        } else {
            if let Some(tmp) = &self.lval{
                let mut const_bool = false;
                let mut global_bool = false;
                {
                    let mut g = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                    let mut k = g.borrow_mut().get_mut();
                    let mut s = k.now_symbol.as_ref().unwrap().lock().unwrap();
                    const_bool = s.exist_const_symbol(&tmp.ident)
                }
                {
                    let mut g = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                    let mut k = g.borrow_mut().get_mut();
                    let mut gg = k.global_symbol_table.as_ref().unwrap().lock().unwrap();
                    global_bool = gg.exist_global_inited_symbol(&tmp.ident);
                }
                if  const_bool || global_bool{
                    let mut g = GLOBAL_SYMBOL_TABLE_ALLOCATOR.lock().unwrap();
                    let mut k = g.borrow_mut().get_mut();
                    let mut s = k.now_symbol.as_ref().unwrap().lock().unwrap();
                    let i = s.get_value(&tmp.ident);
                    return Some(Value::Int(i))
                } else {
                    return None
                }
            } else if let Some(tmp) = &self.exp{
                return tmp.eval_const();
            } else {
                return None
            }
        }
    }
}


