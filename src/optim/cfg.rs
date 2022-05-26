use std::cell::Ref;
use std::cmp::{Ordering, Reverse};
use std::collections::{BinaryHeap, HashMap, HashSet, VecDeque};
use std::collections::hash_map::DefaultHasher;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use koopa::ir::{BasicBlock, Function, FunctionData, Program, Type, TypeKind, Value};
use koopa::ir::entities::ValueData;
use koopa::ir::ValueKind;

#[derive(Debug)]
pub struct ControlFlowGraph{
    pub enter: CfgInner,
    pub exit: CfgInner,
    pub other: HashMap<BasicBlock, CfgInner>,
    pub name: String,
}

#[derive(Debug, Clone)]
pub struct CfgInner{
    pub father: Vec<Option<BasicBlock>>,
    pub son: Vec<Option<BasicBlock>>,
    pub code: Option<BasicBlock>,
}
impl CfgInner{
    fn new(code: BasicBlock) -> Self{
        CfgInner{father: Vec::new(), son: Vec::new(), code: Some(code)}
    }
    fn new_enter_node() -> CfgInner{
        CfgInner{father: Vec::new(), son: Vec:: new(), code: None}
    }
    fn new_exit_node() ->  CfgInner{
        CfgInner{father: Vec::new(), son: Vec:: new(), code: None}
    }
    fn attach_with_son_node(&mut self, son: BasicBlock){
        self.son.push(Some(son));
    }
    fn attach_with_father_node(&mut self, father: BasicBlock){
        self.father.push(Some(father));
    }
}
#[derive(Debug)]
pub struct ActiveVar{
    in_var: HashMap<BBType, HashSet<Value>>,
    out_var: HashMap<BBType, HashSet<Value>>,
}
impl ActiveVar{
    fn new() -> Self{
        ActiveVar{
            in_var: HashMap::new(),
            out_var: HashMap::new()
        }
    }
}

pub trait ActiveAnalysis: BuildControlFlowGraph{
    fn get_define_and_uses(&self) -> HashMap<Function, HashMap<BasicBlock, (HashSet<Value>, HashSet<Value>)>>;
    fn active_analysis(&self) -> (HashMap<Function, ActiveVar>, HashMap<Function, ControlFlowGraph>);
}


pub trait BuildControlFlowGraph{
    fn build_control_flow_graph(&self) -> HashMap<Function, ControlFlowGraph>;
}

impl BuildControlFlowGraph for Program{
    ///build control flow graph for function in program
    fn build_control_flow_graph(&self) -> HashMap<Function, ControlFlowGraph> {
        let mut control_flow_graph_map: HashMap<Function, ControlFlowGraph> = HashMap::new();
        for func in self.func_layout(){
            let mut cfg = ControlFlowGraph::new();
            let func_data = self.func(func.clone());
            cfg.name = func_data.name().to_string();
            for (bb, bbn) in func_data.layout().bbs(){
                if let None = cfg.other.get(bb){
                    let mut cfg_inner = CfgInner::new(bb.clone());
                    let bb_data = func_data.dfg().bbs().get(&bb);
                    let bb_data = bb_data.unwrap();
                    if let Some(name) = bb_data.name(){
                        if name == "%entry"{
                            cfg.enter.son.push(Some(bb.clone()));
                            cfg_inner.father.push(None);
                        }
                    }
                    cfg.other.insert(bb.clone(), cfg_inner);
                }
                for inst in bbn.insts().keys(){
                    let val = func_data.dfg().value(inst.clone());
                    match val.kind(){
                       ValueKind::Jump(jmp) => {
                           let target = jmp.target();
                           if let Some(tar) = cfg.other.get_mut(&target){
                                tar.attach_with_father_node(bb.clone());
                                let cfg_inner = cfg.other.get_mut(&bb.clone()).unwrap();
                                cfg_inner.attach_with_son_node(target.clone());
                           } else {
                                let mut tar = CfgInner::new(target.clone());
                                tar.attach_with_father_node(bb.clone());
                                let cfg_inner = cfg.other.get_mut(&bb.clone()).unwrap();
                                cfg_inner.attach_with_son_node(target.clone());
                                cfg.other.insert(target, tar);
                           }
                       }
                       ValueKind::Branch(br) => {
                           let true_bb = br.true_bb();
                           let false_bb = br.false_bb();
                           if let Some(tar) = cfg.other.get_mut(&true_bb){
                               tar.attach_with_father_node(bb.clone());
                               let cfg_inner = cfg.other.get_mut(&bb.clone()).unwrap();
                               cfg_inner.attach_with_son_node(true_bb.clone());
                           } else {
                               let mut tar = CfgInner::new(true_bb.clone());
                               tar.attach_with_father_node(bb.clone());
                               let cfg_inner = cfg.other.get_mut(&bb.clone()).unwrap();
                               cfg_inner.attach_with_son_node(true_bb.clone());
                               cfg.other.insert(true_bb, tar);
                           }
                           if let Some(tar) = cfg.other.get_mut(&false_bb){
                               tar.attach_with_father_node(bb.clone());
                               let cfg_inner = cfg.other.get_mut(&bb.clone()).unwrap();
                               cfg_inner.attach_with_son_node(false_bb.clone());
                           } else {
                               let mut tar = CfgInner::new(false_bb.clone());
                               tar.attach_with_father_node(bb.clone());
                               let cfg_inner = cfg.other.get_mut(&bb.clone()).unwrap();
                               cfg_inner.attach_with_son_node(false_bb.clone());
                               cfg.other.insert(false_bb, tar);
                           }
                       }
                       ValueKind::Return(_) => {
                            let cfg_inner = cfg.other.get_mut(&bb.clone()).unwrap();
                            cfg_inner.son.push(None);
                            cfg.exit.father.push(Some(bb.clone()));
                       }
                       _ => {
                            continue;
                       }
                    }
                }
            }
            control_flow_graph_map.insert(func.clone(), cfg);
        }
        control_flow_graph_map
    }
}

impl ControlFlowGraph {
    fn new() -> Self {
        ControlFlowGraph {
            enter: CfgInner::new_enter_node(),
            exit: CfgInner::new_enter_node(),
            other: HashMap::new(),
            name: "".to_string(),
        }
    }

    fn flatten_back<'a>(&self, now_cfg_inner: &CfgInner, queue: &'a mut VecDeque<BasicBlock>,
                       visited:
    &mut HashMap<BBType, bool>){
        if visited.is_empty(){
            visited.insert(BBType::Enter, false);
            visited.insert(BBType::Exit, false);
            let mut queue = VecDeque::new();
            for s in &now_cfg_inner.father{
                if let Some(bb) = s{
                    if !visited.contains_key(&BBType::Other(bb.clone())){
                        queue.push_back(bb.clone());
                    }
                }
            }
            while !queue.is_empty(){
                let now = queue.pop_front().unwrap();
                if !visited.contains_key(&BBType::Other(now.clone())){
                    visited.insert(BBType::Other(now.clone()), false);
                }
                for s in &self.other.get(&now).unwrap().father{
                    if let Some(bb) = s{
                        if !visited.contains_key(&BBType::Other(bb.clone())){
                            queue.push_back(bb.clone());
                        }
                    }
                }
            }
        }
        if let Some(bb) = &now_cfg_inner.code{
            *visited.get_mut(&BBType::Other(bb.clone())).unwrap() = true;
        } else {
            if now_cfg_inner.father.is_empty(){
                *visited.get_mut(&BBType::Exit).unwrap() = true;
            } else {
                *visited.get_mut(&BBType::Enter).unwrap() = true;
            }
        }
        for s in &now_cfg_inner.father{
            if let Some(bb) = s{
                if !(*visited.get(&BBType::Other(bb.clone())).unwrap()){
                    self.flatten_back(self.other.get(bb).unwrap(), queue, visited);
                }
            }
        }
        if let Some(bb) = now_cfg_inner.code{
            queue.push_front(bb.clone());
        }
    }
    fn flatten<'a>(&self, now_cfg_inner: &CfgInner, queue: &'a mut VecDeque<BasicBlock>, visited:
    &mut HashMap<BBType, bool>){
        if visited.is_empty(){
            visited.insert(BBType::Enter, false);
            visited.insert(BBType::Exit, false);
            let mut queue = VecDeque::new();
            for s in &now_cfg_inner.son{
                if let Some(bb) = s{
                    if !visited.contains_key(&BBType::Other(bb.clone())){
                        queue.push_back(bb.clone());
                    }
                }
            }
            while !queue.is_empty(){
                let now = queue.pop_front().unwrap();
                if !visited.contains_key(&BBType::Other(now.clone())){
                    visited.insert(BBType::Other(now.clone()), false);
                }
                for s in &self.other.get(&now).unwrap().son{
                    if let Some(bb) = s{
                        if !visited.contains_key(&BBType::Other(bb.clone())){
                            queue.push_back(bb.clone());
                        }
                    }
                }
            }
        }
        if let Some(bb) = &now_cfg_inner.code{
            *visited.get_mut(&BBType::Other(bb.clone())).unwrap() = true;
        } else {
            if now_cfg_inner.son.is_empty(){
                *visited.get_mut(&BBType::Exit).unwrap() = true;
            } else {
                *visited.get_mut(&BBType::Enter).unwrap() = true;
            }
        }
        for s in &now_cfg_inner.son{
            if let Some(bb) = s{
                if !(*visited.get(&BBType::Other(bb.clone())).unwrap()){
                    self.flatten(self.other.get(bb).unwrap(), queue, visited);
                }
            }
        }
        if let Some(bb) = now_cfg_inner.code{
            queue.push_front(bb.clone());
        }
    }
}
/// this is function use out[B] and get In[B]
fn get_in<'a>(out: &'a mut HashSet<Value>, define_value: &HashSet<Value>, use_value:
&HashSet<Value>) -> &'a HashSet<Value> {
    for val in define_value{
        out.remove(val);
    }
    for val in use_value{
        out.insert(val.clone());
    }
    out
}
/// this function merge all the son's In[B] and get self Out[B]
fn merge_in(in_vec: &Vec<HashSet<Value>>) -> HashSet<Value>{
    let mut out: HashSet<Value> = HashSet::new();
    for i in in_vec{
        for val in i{
            out.insert(val.clone());
        }
    }
    out
}
#[derive(Debug, Eq, Hash, PartialEq)]
enum BBType{
    Enter,
    Exit,
    Other(BasicBlock)
}
fn get_in_and_out(cfg: &ControlFlowGraph, define_and_use: &HashMap<BasicBlock, (HashSet<Value>,
                                                                                HashSet<Value>)
>) -> (HashMap<BBType, HashSet<Value>>, HashMap<BBType, HashSet<Value>>){
    let mut bb_in: HashMap<BBType, HashSet<Value>> = HashMap::new();
    let mut bb_out: HashMap<BBType, HashSet<Value>> = HashMap::new();
    // init of the bb_in and bb_out
    bb_in.insert(BBType::Exit, HashSet::new());
    bb_in.insert(BBType::Enter, HashSet::new());
    for (bb, _) in &cfg.other{
        bb_in.insert(BBType::Other(bb.clone()), HashSet::new());
    }
    let mut in_changed = true;
    let mut count = 0;
    let mut flatten = VecDeque::new();
    let mut visited = HashMap::new();
    cfg.flatten_back(&cfg.exit, &mut flatten, &mut visited);
    while in_changed{
        in_changed = false;
        count += 1;
        for i in 0..flatten.len(){
            let now_bb = flatten.get(i).unwrap();
            let now_cfg = cfg.other.get(&now_bb).unwrap();
            let mut vec: Vec<HashSet<Value>> = Vec::new();
            for son in &now_cfg.son{
                if let Some(son) = son{
                    let t = bb_in.get(&BBType::Other(son.clone())).unwrap().clone();
                    vec.push(t);
                }
            }
            let mut b_out =  merge_in(&vec);
            if let Some(pre_out) = bb_out.get(&BBType::Other(now_bb.clone())){
                let col1 = b_out.difference(&pre_out).collect::<HashSet<&Value>>();
                let col2 = pre_out.difference(&b_out).collect::<HashSet<&Value>>();
                if col1.is_empty() && col2.is_empty(){
                    continue;
                } else {
                    in_changed = true;
                }
            } else {
                in_changed = true;
            }
            bb_out.remove(&BBType::Other(now_bb.clone()));
            bb_out.insert(BBType::Other(now_bb.clone()), b_out.clone());
            let (define_value, use_value) = define_and_use.get(&now_bb).unwrap();
            let b_in= get_in(&mut b_out, define_value, use_value);
            bb_in.remove(&BBType::Other(now_bb.clone()));
            bb_in.insert(BBType::Other(now_bb.clone()), b_in.clone());
        }
    }
    (bb_in, bb_out)
}

/// recursively solve
/// now = None means this is the enter BB of function
fn check_int(func_data: &FunctionData, val: &Value) -> bool{
    let dfg = func_data.dfg();
    let value_kind = dfg.value(val.clone()).kind();
    if let ValueKind::Integer(_) = value_kind{
        return true;
    } else {
        return false;
    }
}
fn check_func_args(func_data: &FunctionData, val: &Value) -> bool{
    let dfg = func_data.dfg();
    if let ValueKind::FuncArgRef(_) = dfg.value(val.clone()).kind(){
        return true;
    } else {
        return false;
    }
}
fn check_global(map: &Ref<HashMap<Value, ValueData>>, val: &Value) -> bool{
    if let Some(_) = map.get(val){
        return true;
    } else {
        return false;
    }
}
pub fn check_used(func_data: &FunctionData, val: &Value, map: &Ref<HashMap<Value, ValueData>>) -> bool{
    let dfg = func_data.dfg();
    if !check_global(map, val){
        let used = dfg.value(val.clone()).used_by();
        for used_elem in used{
            if let ValueKind::Store(store) = dfg.value(used_elem.clone()).kind(){
                if store.dest() == *val{
                    if let ValueKind::Alloc(_) = func_data.dfg().value(val.clone()).kind(){
                        continue;
                    } else {
                        return true;
                    }
                } else {
                    return true;
                }
            } else {
                return true;
            }
        }
        return false;
    } else {
        return true;
    }
}
fn check_vec(func_data: &FunctionData, map: &Ref<HashMap<Value, ValueData>>, val: &Value) -> bool{
    let dfg = func_data.dfg();
    if let Some(value_data) = map.get(val){
        if let TypeKind::Pointer(point) = value_data.ty().kind(){
            if let TypeKind::Array(_, _) = point.kind(){
                return true;
            } else {
                return false;
            }
        } else {
            return false;
        }
    } else {
        if let ValueKind::GetElemPtr(_) = dfg.value(val.clone()).kind(){
            return false;
        } else if let ValueKind::GetPtr(_) = dfg.value(val.clone()).kind(){
            return false;
        } else {
            if let TypeKind::Pointer(point) = dfg.value(val.clone()).ty().kind(){
                if let TypeKind::Array(_, _) = point.kind(){
                    return true;
                } else {
                    return false;
                }
            } else {
                return false;
            }
        }
    }
}

impl ActiveAnalysis for Program{
    fn active_analysis(&self) -> (HashMap<Function, ActiveVar>, HashMap<Function, ControlFlowGraph>) {
        let mut active_var_vec = HashMap::new();
        let define_and_use_all = self.get_define_and_uses();
        let cfg_all = Self::build_control_flow_graph(self);
        for (func, cfg) in &cfg_all{
            if let Some(define_and_use) = define_and_use_all.get(func){
                let (bb_in, bb_out) = get_in_and_out(&cfg, &define_and_use);
                active_var_vec.insert(func.clone() ,ActiveVar{in_var: bb_in, out_var: bb_out});
            } else {
                unreachable!()
            }
        }
        (active_var_vec, cfg_all)
    }
    // if the value is a plvalue, it should not be included
    fn get_define_and_uses(&self) -> HashMap<Function, HashMap<BasicBlock, (HashSet<Value>,
                                                                            HashSet<Value>)>> {
        let mut define_uses_map = HashMap::new();
        let global_val = self.borrow_values();
        for func in self.func_layout(){
            let mut define_and_uses = HashMap::new();
            let func_data = self.func(func.clone());
            for (bb, bbn) in func_data.layout().bbs(){
                let mut define_value = HashSet::new();
                let mut use_value = HashSet::new();
                for inst in bbn.insts().keys(){
                    let value_data = func_data.dfg().value(*inst);
                    match value_data.kind(){
                        ValueKind::Return(ret) => {
                            if let Some(val) = ret.value(){
                                if !define_value.contains(&val) &&!check_global(&global_val, &val)
                                    && !check_int(func_data, &val)
                                    {
                                    use_value.insert(val.clone());
                                }
                            }
                        }
                        ValueKind::Binary(bin) => {
                            if !define_value.contains(&bin.lhs()) && !check_global(&global_val, &bin.lhs())&& !check_int(func_data, &bin
                                .lhs()) {
                                use_value.insert(bin.lhs());
                            }
                            if !define_value.contains(&bin.rhs()) && !check_global(&global_val, &bin.rhs())&& !check_int(func_data, &bin
                                .rhs()) {
                                use_value.insert(bin.rhs());
                            }
                            if check_used(func_data, &inst,&global_val){
                                define_value.insert(inst.clone());
                            }
                        }
                        ValueKind::Store(store) => {
                            if !check_vec(func_data, &global_val, &store.dest()) && check_used
                                (func_data, &store.dest(), &global_val){
                                define_value.insert(store.dest().clone());
                            }
                            if !define_value.contains(&store.value()) && !check_global
                                (&global_val, &store.value())&& !check_int(func_data,
                                                                                    &store.value
                                                                                    ()) &&
                                !check_func_args(func_data, &store.value()) {
                                use_value.insert(store.value());
                            }
                        }
                        ValueKind::Load(load) => {
                            if !define_value.contains(&load.src()) && !check_global(&global_val,
                                                                                    &load.src())
                                && !check_int(func_data, &load.src()){
                                use_value.insert(load.src());
                            }
                            define_value.insert(inst.clone());
                        }
                        ValueKind::Alloc(_) =>{
                            if let TypeKind::Pointer(typeid) = func_data.dfg().value(inst.clone()).ty()
                                .kind(){
                                if let TypeKind::Array(_, _) = typeid.kind(){

                                } else if check_used(func_data, &inst, &global_val){
                                    define_value.insert(inst.clone());
                                }
                            }
                        }
                        ValueKind::Branch(branch) => {
                            if !define_value.contains(&branch.cond()) && !check_global
                                (&global_val, &branch.cond())&& !check_int(func_data,
                                                                                    &branch.cond()){
                                use_value.insert(branch.cond().clone());
                            }
                        }
                        ValueKind::Jump(_) => {
                        }
                        ValueKind::Call(call) => {
                            for arg in call.args(){
                                if !define_value.contains(arg)  && !check_global
                                    (&global_val, &arg)&& !check_int(func_data, arg){
                                    use_value.insert(arg.clone());
                                }
                            }
                            let a = func_data.dfg().value(inst.clone()).ty();
                            if a.eq(&Type::get_i32()) && check_used(func_data, inst, &global_val){
                                define_value.insert(inst.clone());
                            }
                        }
                        ValueKind::GetElemPtr(get_elem_ptr) => {
                            if check_used(func_data, inst, &global_val){
                                define_value.insert(inst.clone());
                            }
                            if !define_value.contains(&get_elem_ptr.src()) && !check_global
                                (&global_val, &get_elem_ptr.src())&& !check_int
                                (func_data, &get_elem_ptr.src()) && !check_vec(func_data,
                                                                               &global_val,
                                                                               &get_elem_ptr.src()){
                                use_value.insert(get_elem_ptr.src().clone());
                            }
                            if !define_value.contains(&get_elem_ptr.index())  && !check_global
                                (&global_val, &get_elem_ptr.index())&& !check_int
                                (func_data, &get_elem_ptr.index()){
                                use_value.insert(get_elem_ptr.index().clone());
                            }
                        }
                        ValueKind::GetPtr(get_ptr) => {
                            if check_used(func_data, inst, &global_val){
                                define_value.insert(inst.clone());
                            }
                            if !define_value.contains(&get_ptr.src())  && !check_global
                                (&global_val, &get_ptr.src())&& !check_int(func_data,
                                                                                      &get_ptr
                                                                                          .src())
                               {
                                use_value.insert(get_ptr.src().clone());
                            }
                            if !define_value.contains(&get_ptr.index()) && !check_global
                                (&global_val, &get_ptr.index())&& !check_int(func_data,
                                                                                      &get_ptr
                                                                                          .index
                                                                                          ()) {
                                use_value.insert(get_ptr.index().clone());
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                define_and_uses.insert(bb.clone(), (define_value, use_value));
            }
            define_uses_map.insert(func.clone(), define_and_uses);
        }
        define_uses_map
    }
}

struct StartQueueInner(Value, i32);

impl Eq for StartQueueInner {}

impl PartialEq<Self> for StartQueueInner {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1
    }
}

impl PartialOrd<Self> for StartQueueInner {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.1 < other.1{
            Some(Ordering::Less)
        } else if self.1 > other.1{
            Some(Ordering::Greater)
        } else {
            let mut hasher = DefaultHasher::new();
            self.0.hash(&mut hasher);
            let a = hasher.finish();
            other.0.hash(&mut hasher);
            let b = hasher.finish();
            if  a < b{
                Some(Ordering::Less)
            } else {
                Some(Ordering::Greater)
            }
        }
    }
}

impl Ord for StartQueueInner {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}
pub struct IntervalHandler{
    inner: HashMap<Value, Interval>,
    start: BinaryHeap<Reverse<StartQueueInner>>,
    end: BinaryHeap<Reverse<StartQueueInner>>
}
impl IntervalHandler{
    pub(crate) fn new(inner: HashMap<Function, HashMap<Value, Interval>>) -> HashMap<Function, IntervalHandler>{
        let mut tmp = HashMap::new();
        for (func, mut hash_inner) in inner{
            let size = hash_inner.len();
            let mut start = BinaryHeap::with_capacity(size);
            let mut end = BinaryHeap::with_capacity(size);
            for (val, interval) in &mut hash_inner{
                let (l ,r) = interval.interval.pop_front().unwrap();
                start.push(std::cmp::Reverse(StartQueueInner(val.clone(), l)));
                end.push(std::cmp::Reverse(StartQueueInner(val.clone(),  r)));
            }
            tmp.insert(func, IntervalHandler{inner: hash_inner, start, end});
        }
        tmp
    }
}
impl Iterator for IntervalHandler{
    type Item = (Value, Vec<Value>);
    fn next(&mut self) -> Option<Self::Item> {
        if !self.start.is_empty(){
            let mut tmp = Vec::new();
            let StartQueueInner(val, idx) = self.start.pop().unwrap().0;
            while idx > self.end.peek().unwrap().0.1{
                let StartQueueInner(val, _) = self.end.pop().unwrap().0;
                tmp.push(val.clone());
            }
            Some((val, tmp))
        } else {
            None
        }
    }
}

pub struct Interval{
    interval: VecDeque<(i32, i32)>,
    margins: HashMap<BasicBlock, (i32, i32)>
}
impl Interval{
    fn new() -> Interval{
        Interval{interval: VecDeque::new(), margins: HashMap::new()}
    }
    fn new_margin(&mut self, bb: BasicBlock, left: i32, right: i32){
        if !self.margins.contains_key(&bb){
            self.margins.insert(bb, (left, right));
        }
    }
    /// cut the range, if not contain, do nothing
    fn cut(&mut self, now: i32){
        if let Some((left, right)) = self.interval.pop_front(){
            if now > left {
                self.interval.push_front((now, right));
            } else {
                self.interval.push_front((left, right));
            }
        }
    }
    fn insert(&mut self, bb: &BasicBlock, now: i32){
        let (left, _) = self.margins.get(bb).unwrap();
        if let Some((l, r)) = self.interval.front(){
            if !(*left >= *l && now <= *r){
                self.interval.push_front((*left, now));
            }
        } else {
            self.interval.push_front((*left, now));
        }
    }
    //now strategy: ignore the internal blank
    fn merge_interval(&mut self){
        let mut tmp = VecDeque::new();
        let mut merged: (i32, i32) = (0, 0);
        if let Some(first) = self.interval.pop_front(){
            merged.0 = first.0;
            if let Some(last) = self.interval.pop_back(){
                merged.1 = last.1;
            } else {
                merged.1 = first.1;
            }
            tmp.push_back(merged);
            self.interval = tmp;
        } else {
            unreachable!();
        }
    }
}
pub trait IntervalAnalysis{
    fn get_interval(&self) -> HashMap<Function, HashMap<Value, Interval>>;
    fn print_interval(&self, interval: &HashMap<Function, HashMap<Value, Interval>>);
}
impl IntervalAnalysis for Program{
    fn get_interval(&self) -> HashMap<Function, HashMap<Value, Interval>> {
        let mut all_interval = HashMap::new();
        let (act, cfg) = self.active_analysis();
        let global_var = self.borrow_values();
        for (func, cfg) in cfg.iter(){
            if !cfg.other.is_empty(){
                let mut flatten = VecDeque::new();
                let mut visited = HashMap::new();
                cfg.flatten(&cfg.enter, &mut flatten, &mut visited);
                let act = act.get(func).unwrap();
                let mut cnt = 0 as i32;
                let mut func_interval = HashMap::new();
                while !flatten.is_empty(){
                    let bb = flatten.pop_back().unwrap();
                    if let Some(bbn) = self.func(func.clone()).layout().bbs().node(&bb) {
                        let func_data = self.func(func.clone());
                        let end = cnt;
                        let begin  = cnt - bbn.insts().len() as i32;
                        if let Some(out_var) = act.out_var.get(&BBType::Other(bb)){
                            for elem in out_var {
                                if !check_int(func_data, elem) && !check_global(&global_var, &elem){
                                    if !func_interval.contains_key(elem){
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, cnt);
                                        interval.insert(&bb, cnt);
                                        func_interval.insert(elem.clone(), interval);
                                    } else {
                                        func_interval.get_mut(elem).unwrap().new_margin(bb.clone(),
                                                                                        begin ,cnt);
                                        func_interval.get_mut(elem).unwrap().insert(&bb,
                                                                                    cnt);
                                    }
                                }
                            }
                        }
                        let mut vec = Vec::new();
                        for inst in bbn.insts().keys(){
                            vec.push(inst);
                        }
                        for inst in vec.iter().rev(){
                            let value_data = func_data.dfg().value(*(*inst));
                            match value_data.kind() {
                                ValueKind::Return(ret) => {
                                    if let Some(val) = ret.value() {
                                        if !check_int(func_data, &val){
                                            if !func_interval.contains_key(&val){
                                                let mut interval = Interval::new();
                                                interval.new_margin(bb.clone(), begin, end);
                                                func_interval.insert(val.clone(), interval);
                                            }
                                            func_interval.get_mut(&val).unwrap().new_margin(bb.clone
                                            (), begin, end);
                                            func_interval.get_mut(&val).unwrap().insert(&bb, cnt);
                                        }
                                    }
                                }
                                ValueKind::Binary(bin) => {
                                    if !check_int(func_data, &bin.rhs()){
                                        if !func_interval.contains_key(&bin.rhs()){
                                            let mut interval = Interval::new();
                                            interval.new_margin(bb.clone(), begin, end);
                                            func_interval.insert(bin.rhs().clone(), interval);
                                        }
                                        func_interval.get_mut(&bin.rhs()).unwrap().new_margin(bb.clone
                                        (), begin, end);
                                        func_interval.get_mut(&bin.rhs()).unwrap().insert(&bb, cnt);
                                    }
                                    if !check_int(func_data, &bin.lhs()){
                                        if !func_interval.contains_key(&bin.lhs()){
                                            let mut interval = Interval::new();
                                            interval.new_margin(bb.clone(), begin, end);
                                            func_interval.insert(bin.lhs().clone(), interval);
                                        }
                                        func_interval.get_mut(&bin.lhs()).unwrap().new_margin(bb.clone
                                        (), begin, end);
                                        func_interval.get_mut(&bin.lhs()).unwrap().insert(&bb, cnt);
                                    }
                                    if check_used(func_data, inst, &global_var){
                                        if !func_interval.contains_key(inst){
                                            let mut interval = Interval::new();
                                            interval.new_margin(bb.clone(), begin, end);
                                            func_interval.insert(*inst.clone(), interval);
                                        }
                                        func_interval.get_mut(&inst).unwrap().new_margin(bb.clone
                                        (), begin, end);
                                        func_interval.get_mut(&inst).unwrap().cut(cnt);
                                    }
                                }
                                ValueKind::Store(store) => {
                                    if !check_int(func_data, &store.value()) && !check_func_args
                                        (func_data, &store.value()){
                                        if !func_interval.contains_key(&store.value()){
                                            let mut interval = Interval::new();
                                            interval.new_margin(bb.clone(), begin, end);
                                            func_interval.insert(store.value().clone(), interval);
                                        }
                                        func_interval.get_mut(&store.value()).unwrap().new_margin
                                        (bb, begin, end);
                                        func_interval.get_mut(&store.value()).unwrap().insert(&bb, cnt);
                                    }
                                    if !check_global(&global_var, &store.dest()) && check_used
                                        (func_data, &store.dest(), &global_var){
                                        if let ValueKind::GetElemPtr(_)= func_data.dfg().value
                                        (store.dest()).kind(){
                                            if !func_interval.contains_key(&store.dest()){
                                                let mut interval = Interval::new();
                                                interval.new_margin(bb.clone(), begin, end);
                                                func_interval.insert(store.dest().clone(), interval);
                                            }
                                            func_interval.get_mut(&store.dest()).unwrap().new_margin(bb, begin, end);
                                            func_interval.get_mut(&store.dest()).unwrap().insert(&bb, cnt);
                                        } else if let ValueKind::GetPtr(_)= func_data.dfg().value
                                        (store.dest()).kind(){
                                            if !func_interval.contains_key(&store.dest()){
                                                let mut interval = Interval::new();
                                                interval.new_margin(bb.clone(), begin, end);
                                                func_interval.insert(store.dest().clone(), interval);
                                            }
                                            func_interval.get_mut(&store.dest()).unwrap().new_margin(bb, begin, end);
                                            func_interval.get_mut(&store.dest()).unwrap().insert(&bb, cnt);
                                        }else {
                                            if !func_interval.contains_key(&store.dest()){
                                                let mut interval = Interval::new();
                                                interval.new_margin(bb.clone(), begin, end);
                                                func_interval.insert(store.dest().clone(), interval);
                                            }
                                            func_interval.get_mut(&store.dest()).unwrap().new_margin(bb, begin, end);
                                            func_interval.get_mut(&store.dest()).unwrap().cut(cnt);
                                        }
                                    }
                                }
                                ValueKind::Load(load) => {
                                    if check_used(func_data, inst, &global_var){
                                        if !func_interval.contains_key(inst){
                                            let mut interval = Interval::new();
                                            interval.new_margin(bb.clone(), begin, end);
                                            func_interval.insert(*inst.clone(), interval);
                                        }
                                        func_interval.get_mut(&inst).unwrap().new_margin(bb, begin,
                                                                                         end);
                                        func_interval.get_mut(&inst).unwrap().cut(cnt);
                                    }
                                    if !check_global(&global_var, &load.src()){
                                        if !func_interval.contains_key(&load.src()){
                                            let mut interval = Interval::new();
                                            interval.new_margin(bb.clone(), begin, end);
                                            func_interval.insert(load.src().clone(), interval);
                                        }
                                        func_interval.get_mut(&load.src()).unwrap().new_margin(bb,
                                                                                               begin, end);
                                        func_interval.get_mut(&load.src()).unwrap().insert(&bb, cnt);
                                    }
                                }
                                ValueKind::Alloc(_) => {
                                    if check_used(func_data, inst, &global_var) && !check_vec(func_data,
                                                                                  &global_var,
                                                                                 inst){
                                        if !func_interval.contains_key(inst){
                                            let mut interval = Interval::new();
                                            interval.new_margin(bb.clone(), begin, end);
                                            func_interval.insert(*inst.clone(), interval);
                                        }
                                        func_interval.get_mut(&inst).unwrap().new_margin(bb, begin,
                                                                                         end);
                                        func_interval.get_mut(&inst).unwrap().cut(cnt);
                                    }
                                }
                                ValueKind::Branch(branch) => {
                                    if !check_int(func_data, &branch.cond()){
                                        if !func_interval.contains_key(&branch.cond()){
                                            let mut interval = Interval::new();
                                            interval.new_margin(bb.clone(), begin, end);
                                            func_interval.insert(branch.cond().clone(), interval);
                                        }
                                        func_interval.get_mut(&branch.cond()).unwrap().new_margin(bb,
                                                                                                  begin, end);
                                        func_interval.get_mut(&branch.cond()).unwrap().insert(&bb, cnt);
                                    }
                                }
                                ValueKind::Jump(_) => {}
                                ValueKind::Call(call) => {
                                    if let a = func_data.dfg().value(*inst.clone()).ty(){
                                        if a.eq(&Type::get_i32()) && check_used(func_data, inst,
                                                                                &global_var){
                                            if !func_interval.contains_key(inst){
                                                let mut interval = Interval::new();
                                                interval.new_margin(bb.clone(), begin, end);
                                                func_interval.insert(*inst.clone(), interval);
                                            }
                                            func_interval.get_mut(&inst).unwrap().new_margin(bb, begin,
                                                                                             end);
                                            func_interval.get_mut(&inst).unwrap().cut(cnt);
                                        }
                                        for arg in call.args(){
                                            if !check_int(func_data, arg){
                                                if !func_interval.contains_key(arg){
                                                    let mut interval = Interval::new();
                                                    interval.new_margin(bb.clone(), begin, end);
                                                    func_interval.insert(arg.clone(), interval);
                                                }
                                                func_interval.get_mut(arg).unwrap().new_margin(bb,
                                                                                               begin, end);
                                                func_interval.get_mut(arg).unwrap().insert(&bb, cnt);
                                            }
                                        }
                                    }
                                }
                                ValueKind::GetElemPtr(get_elem_ptr) => {
                                    if check_used(func_data, inst, &global_var){
                                        if !func_interval.contains_key(inst){
                                            let mut interval = Interval::new();
                                            interval.new_margin(bb.clone(), begin, end);
                                            func_interval.insert(*inst.clone(), interval);
                                        }
                                        func_interval.get_mut(&inst).unwrap().new_margin(bb, begin,
                                                                                         end);
                                        func_interval.get_mut(&inst).unwrap().cut(cnt);
                                    }
                                    if !check_vec(func_data,&global_var, &get_elem_ptr.src()){
                                        if !func_interval.contains_key(&get_elem_ptr.src()){
                                            let mut interval = Interval::new();
                                            interval.new_margin(bb.clone(), begin, end);
                                            func_interval.insert(get_elem_ptr.src().clone(), interval);
                                        }
                                        func_interval.get_mut(&get_elem_ptr.src()).unwrap().new_margin(bb,
                                                                                                       begin, end);
                                        func_interval.get_mut(&get_elem_ptr.src()).unwrap().insert(&bb, cnt);
                                    }
                                    if !check_int(func_data, &get_elem_ptr.index()){
                                        if !func_interval.contains_key(&get_elem_ptr.index()){
                                            let mut interval = Interval::new();
                                            interval.new_margin(bb.clone(), begin, end);
                                            func_interval.insert(get_elem_ptr.index().clone(), interval);
                                        }
                                        func_interval.get_mut(&get_elem_ptr.index()).unwrap()
                                            .new_margin(bb, begin, end);
                                        func_interval.get_mut(&get_elem_ptr.index()).unwrap().insert(&bb, cnt);
                                    }
                                }
                                ValueKind::GetPtr(get_ptr) => {
                                    if check_used(func_data, inst, &global_var){
                                        if !func_interval.contains_key(inst) {
                                            let mut interval = Interval::new();
                                            interval.new_margin(bb.clone(), begin, end);
                                            func_interval.insert(*inst.clone(), interval);
                                        }
                                        func_interval.get_mut(&inst).unwrap().new_margin(bb.clone(),
                                                                                         begin, end);
                                        func_interval.get_mut(&inst).unwrap().cut(cnt);
                                    }
                                    if !func_interval.contains_key(&get_ptr.src()) {
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(get_ptr.src().clone(), interval);
                                    }
                                    if !check_int(func_data, &get_ptr.index()){
                                        if !func_interval.contains_key(&get_ptr.index()){
                                            let mut interval = Interval::new();
                                            interval.new_margin(bb.clone(), begin, end);
                                            func_interval.insert(get_ptr.index().clone(), interval);
                                        }
                                        func_interval.get_mut(&get_ptr.index()).unwrap().new_margin(bb, begin, end);
                                        func_interval.get_mut(&get_ptr.index()).unwrap().insert(&bb, cnt);
                                    }
                                    //todo: 在进入一个新的bb之后，我们需要将bb的margin加入interval中
                                    func_interval.get_mut(&get_ptr.src()).unwrap().new_margin(bb,
                                                                                              begin, end);
                                    func_interval.get_mut(&get_ptr.src()).unwrap().insert(&bb, cnt);
                                }
                                _ => unreachable!(),
                            }
                            cnt -= 1;
                        }
                    }
                }
                for (_, idx) in &mut func_interval{
                    for i in 0..idx.interval.len(){
                        if let Some((left, right)) = idx.interval.get_mut(i){
                            *left -= cnt;
                            *right -= cnt;
                        }
                    }
                    for (_, (left, right)) in &mut idx.margins{
                        *left -= cnt;
                        *right -= cnt;
                    }
                }
                all_interval.insert(func.clone(), func_interval);
            }
        }
        for (func, interval) in &mut all_interval {
            for (val, interval_1) in interval{
                interval_1.merge_interval();
            }
        }
        all_interval
    }
    fn print_interval(&self, interval: &HashMap<Function, HashMap<Value, Interval>>) {
        for (func, inter) in interval{
            if !inter.is_empty(){
                let dfg = self.func(func.clone()).dfg();
                let mut cnt = 1;
                for (value, interval) in inter{
                    if let Some(a) = dfg.value(value.clone()).name().as_ref(){
                        let mut str = format!("{}: ", *a);
                        for (left, right) in &interval.interval{
                            str += &format!("({}, {}) ",left, right);
                        }
                        str += "\n";
                        print!("{}", str);
                    } else {
                        let mut str = format!("%{}: ", cnt);
                        for (left, right) in &interval.interval{
                            str += &format!("({}, {}) ",left, right);
                        }
                        str += "\n";
                        print!("{}", str);
                        cnt += 1;
                    }
                }
            }
        }
    }
}