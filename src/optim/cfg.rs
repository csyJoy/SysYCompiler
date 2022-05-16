use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;
use koopa::ir::{BasicBlock, Function, FunctionData, Program, Value};
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
    fn get_define_and_use(&self, func_data: &FunctionData) -> (HashSet<Value>, HashSet<Value>){
        if let Some(bbn) = func_data.layout().bbs().node(&self.code.unwrap()){
            let mut define_value:HashSet<Value> = HashSet::new();
            let mut use_value:HashSet<Value> = HashSet::new();
            for inst in bbn.insts().keys(){
                let value_data = func_data.dfg().value(*inst);
                match value_data.kind(){
                    ValueKind::Return(ret) => {
                        // println!("{:#?}", ret);
                        // println!("{:#?}", self.dfg().value(ret.value().unwrap()));
                        // println!("=============================================");
                        if let Some(val) = ret.value(){
                            if define_value.contains(&val){
                                use_value.insert(val.clone());
                            }
                        }
                    }
                    ValueKind::Binary(bin) => {
                        if define_value.contains(&bin.lhs()){
                            use_value.insert(bin.lhs());
                        }
                        if define_value.contains(&bin.rhs()){
                            use_value.insert(bin.rhs());
                        }
                        define_value.insert(inst.clone());
                    }
                    ValueKind::Store(store) => {
                    }
                    ValueKind::Load(load) => {
                        define_value.insert(inst.clone());
                    }
                    ValueKind::Alloc(alloc) =>{
                        define_value.insert(inst.clone());
                    }
                    ValueKind::Branch(branch) => {
                        if define_value.contains(&branch.cond()){
                            use_value.insert(branch.cond().clone());
                        }
                    }
                    ValueKind::Jump(jump) => {
                    }
                    ValueKind::Call(call) => {
                    }
                    ValueKind::GetElemPtr(get_elem_ptr) => {
                        define_value.insert(inst.clone());
                        if define_value.contains(&get_elem_ptr.src()){
                            use_value.insert(get_elem_ptr.src().clone());
                        }
                        if define_value.contains(&get_elem_ptr.index()){
                            use_value.insert(get_elem_ptr.index().clone());
                        }
                    }
                    ValueKind::GetPtr(get_ptr) => {
                        define_value.insert(inst.clone());
                        if define_value.contains(&get_ptr.index()){
                            use_value.insert(get_ptr.src().clone());
                        }
                        if define_value.contains(&get_ptr.index()){
                            use_value.insert(get_ptr.index().clone());
                        }
                    }
                    _ => unreachable!(),
                }
            }
            (define_value, use_value)
        } else {
            unreachable!()
        }
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
    fn print_control_flow_graph(&self, cfg: HashMap<Function, ControlFlowGraph>);
}

impl BuildControlFlowGraph for Program{
    fn print_control_flow_graph(&self, cfg: HashMap<Function, ControlFlowGraph>) {
        todo!()
    }
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
                       ValueKind::Return(ret) => {
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
    fn flatten(&self) -> VecDeque<BasicBlock>{
        let mut flatten = VecDeque::new();
        let mut son = &self.enter.son;
        let mut middle = VecDeque::new();
        middle.push_back(son);
        while(!middle.is_empty()){
            let son = middle.pop_front().unwrap();
            for s in son{
                if let Some(bb) = s{
                    if !flatten.contains(bb){
                        flatten.push_back(bb.clone());
                        middle.push_back(&self.other.get(bb).unwrap().son);
                    }
                }
            }
        }
        flatten
    }
}
impl ControlFlowGraph{
    fn get_all_defines_and_uses(&self, func_data: &FunctionData) -> HashMap<BasicBlock, (HashSet<Value>, HashSet<Value>)>{
        let begin = &self.enter;
        let mut defines_and_uses: HashMap<BasicBlock, (HashSet<Value>, HashSet<Value>)> =
            HashMap::new();
        for i in &begin.son{
            if let Some(bb) =  i{
                if let Some(a) = self.other.get(&bb){
                    let result = a.get_define_and_use(func_data);
                    defines_and_uses.insert(bb.clone(), result);
                } else {
                    unreachable!()
                }
            } else {
                unreachable!()
            }
        }
        defines_and_uses
    }
}
/// this is function use out[B] and get In[B]
fn get_in<'a>(out: &'a mut HashSet<Value>, define_value: &HashSet<Value>, use_value:
&HashSet<Value>) -> (&'a HashSet<Value>, bool) {
    let mut changed = false;
    let mut define_set:HashSet<Value> = HashSet::new();
    let mut use_set:HashSet<Value> = HashSet::new();
    for val in define_value{
        let result = out.remove(val);
        if result {
            define_set.insert(val.clone());
        }
    }
    for val in use_value{
        let result = out.insert(val.clone());
        if result {
            use_set.insert(val.clone());
        }
    }
    let tmp1 = use_set.difference(&define_set);
    let tmp2 = define_set.difference(&use_set);
    let tmp1 = tmp1.collect::<HashSet<&Value>>();
    let tmp2 = tmp2.collect::<HashSet<&Value>>();
    if !tmp1.is_empty() || !tmp2.is_empty(){
        changed = true;
    }
    (out, changed)
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
    for (bb, cfg_inner) in &cfg.other{
        bb_in.insert(BBType::Other(bb.clone()), HashSet::new());
    }
    let mut in_changed = true;
    let mut count = 0;
    while in_changed{
        in_changed = false;
        count += 1;
        let now = &cfg.exit;
        let mut global_vec: Vec<BasicBlock> = Vec::new();
        for fa in &now.father{
            if let Some(bb) = fa{
                global_vec.push(bb.clone());
            }
        }
        // println!("====================iter{}===========================", count);
        // for (bb, set) in bb_in.iter(){
        //     let mut s: String = "".to_string();
        //     for value in set.iter(){
        //         s += &format!("{:#?} ", value);
        //     }
        //     if let BBType::Other(bb) = bb{
        //         println!("{:#?}: {}", bb, s);
        //     } else if let BBType::Enter = bb{
        //         println!("enter: {}", s);
        //     } else if let BBType::Exit = bb{
        //         println!("exit: {}", s);
        //     }
        // }
        // for (bb, set) in bb_out.iter(){
        //     let mut s: String = "".to_string();
        //     for value in set.iter(){
        //         s += &format!("{:#?} ", value);
        //     }
        //     if let BBType::Other(bb) = bb{
        //         println!("{:#?}: {}", bb, s);
        //     } else if let BBType::Enter = bb{
        //         println!("enter: {}", s);
        //     } else if let BBType::Exit = bb{
        //         println!("exit: {}", s);
        //     }
        // }
        while !global_vec.is_empty(){
            let now_bb = global_vec.remove(0);
            let now_cfg = cfg.other.get(&now_bb).unwrap();
            let mut vec: Vec<HashSet<Value>> = Vec::new();
            for son in &now_cfg.son{
                if let Some(son) = son{
                    let t = bb_in.get(&BBType::Other(son.clone())).unwrap().clone();
                    vec.push(t);
                }
            }
            let mut b_out =  merge_in(&vec);
            if let Some(pre_out) = bb_out.get(&BBType::Other(now_bb)){
                let col1 = b_out.difference(&pre_out).collect::<HashSet<&Value>>();
                let col2 = pre_out.difference(&b_out).collect::<HashSet<&Value>>();
                if col1.is_empty() && col2.is_empty(){
                    continue;
                }
            }
            bb_out.remove(&BBType::Other(now_bb.clone()));
            bb_out.insert(BBType::Other(now_bb.clone()), b_out.clone());
            let (define_value, use_value) = define_and_use.get(&now_bb).unwrap();
            let (b_in, result) = get_in(&mut b_out, define_value, use_value);
            bb_in.remove(&BBType::Other(now_bb.clone()));
            bb_in.insert(BBType::Other(now_bb.clone()), b_in.clone());
            if result{
                in_changed = true;
                for fa in &now_cfg.father{
                    if let Some(fa) = fa{
                        global_vec.push(fa.clone());
                    }
                }
            }
        }
        // while !global_vec.is_empty() {
        //     let mut now = global_vec.get(0).unwrap();
        //     global_vec.remove(0);
        //     let mut vec: Vec<HashSet<Value>> = Vec::new();
        //     for father in now.father{
        //         if let Some(bb) = father{
        //             global_vec.push(bb);
        //             for son in cfg.other.get(&bb){
        //                 for now_son in son.son{
        //                     if let Some(b) = now_son{
        //                         vec.push(bb_in.get(&BBType::Other(b)).unwrap().clone());
        //                     }
        //                 }
        //             }
        //             let mut b_out =  merge_in(&vec);
        //             bb_out.insert(BBType::Other(bb), b_out.clone());
        //             let (define_value, use_value) = define_and_use.get(&bb).unwrap();
        //             let (b_in, result) = get_in(&mut b_out, define_value, use_value);
        //             bb_in.insert(BBType::Other(bb), b_in.clone());
        //             if result{
        //                 in_changed = true;
        //             }
        //             vec.clear();
        //         }
        //     }
        // }
    }
    (bb_in, bb_out)
}

/// recursively solve
/// now = None means this is the enter BB of function
// fn solve(now: Option<BasicBlock>, now_in_map: &mut HashMap<BasicBlock, HashSet<Value>>,now_out_map:
// &mut
// HashMap<BasicBlock, HashSet<Value>>, cfg: &ControlFlowGraph, define_and_use: &HashMap<BasicBlock,
//     (HashMap<usize, Value>, HashMap<usize, Value>)>){
//     let mut cfg_inner;
//     if let Some(now) = now{
//         cfg_inner = cfg.other.get(&now).unwrap();
//     } else {
//         cfg_inner = &cfg.enter;
//     }
//     // already get the value or the bb is exit
//     if let Some(HashSet) = now_in_map.get(&now.unwrap()) {
//         return;
//     } else {
//         if cfg_inner.code == None{
//             return;
//         }
//         let mut son_vec: Vec<&HashSet<Value>> = Vec::new();
//         for son in cfg_inner.son{
//             if let Some(bb) = son{
//                 if let Some(HashSet) = now_map.get(&bb){
//                     son_vec.push(HashSet);
//                     continue;
//                 } else {
//                     solve(Some(bb), now_in_map,now_out_map, cfg, define_and_use);
//                     son_vec.push(now_in_map.get(&bb).unwrap());
//                 }
//             }else {
//                 unreachable!()
//             }
//         }
//         let mut out = merge_in(son_vec);
//         now_out_map.insert(now.unwrap(), out.clone());
//         let define_value =  define_and_use.get(&now.unwrap()).unwrap().clone().0;
//         let use_value = define_and_use.get(&now.unwrap()).unwrap().clone().1;
//         let in_val = get_in(out.clone(), define_value, use_value);
//         now_in_map.insert(now.unwrap(), in_val);
//     }
// }


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
    fn get_define_and_uses(&self) -> HashMap<Function, HashMap<BasicBlock, (HashSet<Value>,
                                                                            HashSet<Value>)>> {
        let mut define_uses_map = HashMap::new();
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
                                if !define_value.contains(&val){
                                    use_value.insert(val.clone());
                                }
                            }
                        }
                        ValueKind::Binary(bin) => {
                            if !define_value.contains(&bin.lhs()){
                                use_value.insert(bin.lhs());
                            }
                            if !define_value.contains(&bin.rhs()){
                                use_value.insert(bin.rhs());
                            }
                            define_value.insert(inst.clone());
                        }
                        ValueKind::Store(store) => {
                            if !define_value.contains(&store.dest()){
                                use_value.insert(store.dest());
                            }
                            if !define_value.contains(&store.value()){
                                use_value.insert(store.value());
                            }
                        }
                        ValueKind::Load(load) => {
                            if !define_value.contains(&load.src()){
                                use_value.insert(load.src());
                            }
                            define_value.insert(inst.clone());
                        }
                        ValueKind::Alloc(alloc) =>{
                            define_value.insert(inst.clone());
                        }
                        ValueKind::Branch(branch) => {
                            if !define_value.contains(&branch.cond()){
                                use_value.insert(branch.cond().clone());
                            }
                        }
                        ValueKind::Jump(jump) => {
                        }
                        ValueKind::Call(call) => {
                            for arg in call.args(){
                                if !define_value.contains(arg){
                                    use_value.insert(arg.clone());
                                }
                            }
                            define_value.insert(inst.clone());
                        }
                        ValueKind::GetElemPtr(get_elem_ptr) => {
                            define_value.insert(inst.clone());
                            if !define_value.contains(&get_elem_ptr.src()){
                                use_value.insert(get_elem_ptr.src().clone());
                            }
                            if !define_value.contains(&get_elem_ptr.index()){
                                use_value.insert(get_elem_ptr.index().clone());
                            }
                        }
                        ValueKind::GetPtr(get_ptr) => {
                            define_value.insert(inst.clone());
                            if !define_value.contains(&get_ptr.index()){
                                use_value.insert(get_ptr.src().clone());
                            }
                            if !define_value.contains(&get_ptr.index()){
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
    fn cut(&mut self, bb: &BasicBlock, now: i32){
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
    fn merge_interval(&mut self){
        let mut tmp = VecDeque::new();
        let mut merged: (i32, i32) = (0, 0);
        for interval in &self.interval{
            if merged.1 != interval.0{
                if merged != (0, 0){
                    tmp.push_back(merged.clone());
                }
                merged = interval.clone();
            } else {
                merged.1 = interval.1;
            }
        }
        tmp.push_back(merged);
        self.interval = tmp;
    }
}
pub trait IntervalAnalysis{
    fn get_interval(&self) -> HashMap<Function, HashMap<Value, Interval>>;
    fn print_interval(&self, interval: &HashMap<Function, HashMap<Value, Interval>>);
}
impl IntervalAnalysis for Program{
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
    fn get_interval(&self) -> HashMap<Function, HashMap<Value, Interval>> {
        let mut all_interval = HashMap::new();
        let (act, cfg) = self.active_analysis();
        for (func, cfg) in cfg.iter(){
            if !cfg.other.is_empty(){
                let mut flatten = cfg.flatten();
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
                        let mut vec = Vec::new();
                        for inst in bbn.insts().keys(){
                            vec.push(inst);
                        }
                        for inst in vec.iter().rev(){
                            let value_data = func_data.dfg().value(*(*inst));
                            match value_data.kind() {
                                ValueKind::Return(ret) => {
                                    if let Some(val) = ret.value() {
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
                                ValueKind::Binary(bin) => {
                                    if !func_interval.contains_key(inst){
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(*inst.clone(), interval);
                                    }
                                    if !func_interval.contains_key(&bin.rhs()){
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(bin.rhs().clone(), interval);
                                    }
                                    if !func_interval.contains_key(&bin.lhs()){
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(bin.lhs().clone(), interval);
                                    }
                                    func_interval.get_mut(&inst).unwrap().new_margin(bb.clone
                                    (), begin, end);
                                    func_interval.get_mut(&inst).unwrap().cut(&bb, cnt);
                                    func_interval.get_mut(&bin.rhs()).unwrap().new_margin(bb.clone
                                    (), begin, end);
                                    func_interval.get_mut(&bin.rhs()).unwrap().insert(&bb, cnt);
                                    func_interval.get_mut(&bin.lhs()).unwrap().new_margin(bb.clone
                                    (), begin, end);
                                    func_interval.get_mut(&bin.lhs()).unwrap().insert(&bb, cnt);
                                }
                                ValueKind::Store(store) => {
                                    if !func_interval.contains_key(&store.value()){
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(store.value().clone(), interval);
                                    }
                                    func_interval.get_mut(&store.value()).unwrap().new_margin
                                    (bb, begin, end);
                                    func_interval.get_mut(&store.value()).unwrap().insert(&bb, cnt);
                                    if !func_interval.contains_key(&store.dest()){
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(store.dest().clone(), interval);
                                    }
                                    func_interval.get_mut(&store.dest()).unwrap().new_margin(bb, begin, end);
                                    func_interval.get_mut(&store.dest()).unwrap().insert(&bb, cnt);
                                }
                                ValueKind::Load(load) => {
                                    if !func_interval.contains_key(inst){
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(*inst.clone(), interval);
                                    }
                                    func_interval.get_mut(&inst).unwrap().new_margin(bb, begin,
                                                                                     end);
                                    func_interval.get_mut(&inst).unwrap().cut(&bb, cnt);
                                    if !func_interval.contains_key(&load.src()){
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(load.src().clone(), interval);
                                    }
                                    func_interval.get_mut(&load.src()).unwrap().new_margin(bb,
                                                                                           begin, end);
                                    func_interval.get_mut(&load.src()).unwrap().insert(&bb, cnt);
                                }
                                ValueKind::Alloc(alloc) => {
                                    if !func_interval.contains_key(inst){
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(*inst.clone(), interval);
                                    }
                                    func_interval.get_mut(&inst).unwrap().new_margin(bb, begin,
                                                                                     end);
                                    func_interval.get_mut(&inst).unwrap().cut(&bb, cnt);
                                }
                                ValueKind::Branch(branch) => {
                                    if !func_interval.contains_key(&branch.cond()){
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(branch.cond().clone(), interval);
                                    }
                                    func_interval.get_mut(&branch.cond()).unwrap().new_margin(bb,
                                                                                              begin, end);
                                    func_interval.get_mut(&branch.cond()).unwrap().insert(&bb, cnt);
                                }
                                ValueKind::Jump(jump) => {}
                                ValueKind::Call(call) => {}
                                ValueKind::GetElemPtr(get_elem_ptr) => {
                                    if !func_interval.contains_key(inst){
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(*inst.clone(), interval);
                                    }
                                    if !func_interval.contains_key(&get_elem_ptr.src()){
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(get_elem_ptr.src().clone(), interval);
                                    }
                                    if !func_interval.contains_key(&get_elem_ptr.index()){
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(get_elem_ptr.index().clone(), interval);
                                    }
                                    func_interval.get_mut(&inst).unwrap().new_margin(bb, begin,
                                                                                     end);
                                    func_interval.get_mut(&inst).unwrap().cut(&bb, cnt);
                                    func_interval.get_mut(&get_elem_ptr.src()).unwrap().new_margin(bb,
                                                                                           begin, end);
                                    func_interval.get_mut(&get_elem_ptr.src()).unwrap().insert(&bb, cnt);
                                    func_interval.get_mut(&get_elem_ptr.index()).unwrap()
                                        .new_margin(bb, begin, end);
                                    func_interval.get_mut(&get_elem_ptr.index()).unwrap().insert(&bb, cnt);
                                }
                                ValueKind::GetPtr(get_ptr) => {
                                    if !func_interval.contains_key(inst) {
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(*inst.clone(), interval);
                                    }
                                    if !func_interval.contains_key(&get_ptr.src()) {
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(get_ptr.src().clone(), interval);
                                    }
                                    if !func_interval.contains_key(&get_ptr.index()){
                                        let mut interval = Interval::new();
                                        interval.new_margin(bb.clone(), begin, end);
                                        func_interval.insert(get_ptr.index().clone(), interval);
                                    }
                                    //todo: 在进入一个新的bb之后，我们需要将bb的margin加入interval中
                                    func_interval.get_mut(&inst).unwrap().new_margin(bb.clone(),
                                                                                     begin, end);
                                    func_interval.get_mut(&inst).unwrap().cut(&bb, cnt);
                                    func_interval.get_mut(&get_ptr.src()).unwrap().new_margin(bb,
                                                                                              begin, end);
                                    func_interval.get_mut(&get_ptr.src()).unwrap().insert(&bb, cnt);
                                    func_interval.get_mut(&get_ptr.index()).unwrap().new_margin(bb, begin, end);
                                    func_interval.get_mut(&get_ptr.index()).unwrap().insert(&bb, cnt);
                                }
                                _ => unreachable!(),
                            }
                            cnt -= 1;
                        }
                    }
                }
                for (val, mut idx) in &mut func_interval{
                    for i in 0..idx.interval.len(){
                        if let Some((left, right)) = idx.interval.get_mut(i){
                            *left -= cnt;
                            *right -= cnt;
                        }
                    }
                    for (bb, (left, right)) in &mut idx.margins{
                        *left -= cnt;
                        *right -= cnt;
                    }
                }
                all_interval.insert(func.clone(), func_interval);
            }
        }
        for (_, interval) in &mut all_interval {
            for (_, interval_1) in interval{
                interval_1.merge_interval();
            }
        }

        self.print_interval(&all_interval);
        all_interval
    }
}