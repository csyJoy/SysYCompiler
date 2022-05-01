use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::ops::Deref;
use std::sync::{Arc, Weak};
use koopa::ir::{BasicBlock, Function, FunctionData, Program, Value};
use koopa::ir::dfg::DataFlowGraph;
use koopa::ir::layout::BasicBlockNode;
use koopa::ir::ValueKind;

pub struct ControlFlowGraph{
    pub enter: Arc<CfgInner>,
    pub exit: Arc<CfgInner>,
    pub other: HashMap<BasicBlock, Arc<CfgInner>>,
    pub name: String,
}

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
    fn get_define_and_use(&self, func_data: FunctionData) -> (HashSet<Value>, HashSet<Value>){
        if let Some(bbn) = &self.inst{
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
                            use_value.insert(val.clone());
                        }
                    }
                    ValueKind::Binary(bin) => {
                        use_value.insert(bin.lhs());
                        use_value.insert(bin.rhs());
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
                        use_value.insert(branch.cond().clone());
                    }
                    ValueKind::Jump(jump) => {
                    }
                    ValueKind::Call(call) => {
                    }
                    ValueKind::GetElemPtr(get_elem_ptr) => {
                        define_value.insert(inst.clone());
                        use_value.insert(get_elem_ptr.src().clone());
                        use_value.insert(get_elem_ptr.index().clone());
                    }
                    ValueKind::GetPtr(get_ptr) => {
                        define_value.insert(inst.clone());
                        use_value.insert(get_ptr.src().clone());
                        use_value.insert(get_ptr.index().clone());
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
trait ActiveAnalysis: BuildControlFlowGraph{
    fn get_define_and_uses(&self) -> HashMap<BasicBlock, (HashMap<usize, Value>,
                                                          HashSet<usize, Value>)>;
    fn active_analysis(&self) -> Vec<ActiveVar>;
}


trait BuildControlFlowGraph{
    type CodeType;
    fn build_control_flow_graph(code: Self::CodeType) -> Vec<ControlFlowGraph>;
}
impl BuildControlFlowGraph for Program{
    type CodeType = Self;
    ///build control flow graph for function in program
    fn build_control_flow_graph(code: Self::CodeType) -> HashMap<Function, ControlFlowGraph> {
        let mut control_flow_graph_map: HashMap<Function, ControlFlowGraph> = HashMap::new();
        for func in code.func_layout(){
            let mut cfg = ControlFlowGraph::new();
            let func_data = code.func(func.clone());
            cfg.name = func_data.name().to_string();
            for (bb, bbn) in func_data.layout().bbs(){
                let mut cfg_inner = Arc::new(CfgInner::new(bb.clone()));
                let bb_data = func_data.dfg().bbs().get(&bb);
                let bb_data = bb_data.unwrap();
                if let Some(name) = bb_data.name(){
                    if name == "%enter"{
                        cfg.enter.son.push(Some(bb.clone()));
                        cfg_inner.father.push(Some(bb.clone()));
                    }
                }
                cfg.other.insert(bb.clone(), cfg_inner.clone());
                for inst in bbn.insts().keys(){
                    let val = func_data.dfg().value(inst.clone());
                    match val.kind(){
                       ValueKind::Jump(jmp) => {
                           let target = jmp.target();
                           if let Some(tar) = cfg.other.get_mut(&target){
                                tar.attach_with_father_node(bb.clone());
                                cfg_inner.attach_with_son_node(target.clone());
                           }
                       }
                       ValueKind::Branch(br) => {
                           let true_bb = br.true_bb();
                           let false_bb = br.false_bb();
                           if let Some(tar) = cfg.other.get_mut(&true_bb){
                               tar.attach_with_father_node(bb.clone());
                               cfg_inner.attach_with_son_node(true_bb.clone());
                           }
                           if let Some(tar) = cfg.other.get_mut(&false_bb){
                               tar.attach_with_father_node(bb.clone());
                               cfg_inner.attach_with_son_node(false_bb.clone());
                           }
                       }
                       ValueKind::Return(ret) => {
                            cfg_inner.son.push(None);
                            cfg.exit.father.push(Some(bb.clone()));
                       }
                       _ => {
                            continue;
                       }
                    }
                }
            }
            control_flow_graph_map(func, cfg);
        }
        control_flow_vec
    }
}

impl ControlFlowGraph {
    fn new() -> Self {
        ControlFlowGraph {
            enter: Arc::new(CfgInner::new_enter_node()),
            exit: Arc::new(CfgInner::new_enter_node()),
            other: HashMap::new(),
            name: "".to_string(),
        }
    }
}
impl ControlFlowGraph{
    fn get_all_defines_and_uses(&self) -> HashMap<BasicBlock, (HashSet<Value>, HashSet<Value>)>{
        let mut begin = &self.enter;
        let mut defines_and_uses: HashMap<BasicBlock, (HashSet<Value>, HashSet<Value>)> =
            HashMap::new();
        for i in begin.son{
            if let Some(bb) =  i{
                if let Some(a) = self.other.get(&bb){
                    if let Some(func_data) = &self.func_data{
                        let result = a.get_define_and_use(*func_data);
                        defines_and_uses.insert(bb, result);
                    } else {
                        unreachable!()
                    }
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
fn get_in<'a>(out: &'a mut HashSet<Value>, define_value: &HashMap<usize, Value>, use_value:
&HashMap<usize, Value>) -> (&'a HashSet<Value>, bool) {
    let mut changed = false;
    let mut define_set:HashSet<Value> = HashSet::new();
    let mut use_set:HashSet<Value> = HashSet::new();
    for (idx, val) in define_value{
        let result = out.remove(val);
        if result {
            define_set.insert(val.clone());
        }
    }
    for (idx, val) in use_value{
        let result = out.insert(val.clone());
        use_set.insert(val.clone());
    }
    let tmp = use_set.difference(&define_set);
    let tmp = tmp.collect::<HashSet<&Value>>();
    if !tmp.is_empty(){
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
enum BBType{
    Enter,
    Exit,
    Other(BasicBlock)
}
fn get_in_and_out(cfg: &ControlFlowGraph, define_and_use: &HashMap<BasicBlock, (HashMap<usize, Value>,
                                                                                HashMap<usize, Value>)
>) -> (HashMap<BBType, HashSet<Value>>, HashMap<BBType, HashSet<Value>>){
    let mut bb_in: HashMap<BBType, HashSet<Value>> = HashMap::new();
    let mut bb_out: HashMap<BBType, HashSet<Value>> = HashMap::new();
    // init of the bb_in and bb_out
    bb_in.insert(BBType::Exit, HashSet::new());
    bb_in.insert(BBType::Enter, HashSet::new());
    for (bb, cfg_inner) in cfg.other{
        bb_in.insert(BBType::Other(bb), HashSet::new());
    }
    let mut in_changed = true;
    while in_changed{
        in_changed = false;
        let mut now = &cfg.exit;
        let mut global_vec: Vec<BasicBlock> = Vec::new();
        for fa in now.father{
            if let Some(bb) = fa{
                global_vec.push(bb);
            }
        }
        while !global_vec.is_empty(){
            let mut now_bb = global_vec.get(0).unwrap();
            global_vec.remove(0);
            let now_cfg = cfg.other.get(now_bb).unwrap();
            let mut vec: Vec<HashSet<Value>> = Vec::new();
            for son in now_cfg.son{
                if let Some(son) = son{
                    let t = bb_in.get(&BBType::Other(son)).unwrap().clone();
                    vec.push(t);
                }
            }
            let mut b_out =  merge_in(&vec);
            bb_out.remove(&BBType::Other(bb));
            bb_out.insert(BBType::Other(bb), b_out.clone());
            let (define_value, use_value) = define_and_use.get(&bb).unwrap();
            let (b_in, result) = get_in(&mut b_out, define_value, use_value);
            bb_in.remove(&BBType::Other(bb));
            bb_in.insert(BBType::Other(bb), b_in.clone());
            if result{
                in_changed = true;
            }
            for fa in now_cfg.father{
                if let Some(fa) = fa{
                    global_vec.push(fa);
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
    fn active_analysis(&self) -> Vec<ActiveVar> {
        let mut active_var_vec: Vec<ActiveVar> = Vec::new();
        let define_and_use_all = self.get_define_and_uses();
        let cfg_all = Self::build_control_flow_graph();
        for (func, cfg) in &cfg_all{
            if let Some(define_and_use) = define_and_use_all.get(func){
                let (bb_in, bb_out) = get_in_and_out(&cfg, &define_and_use);
                active_var_vec.push(ActiveVar{in_var: bb_in, out_var: bb_out});
            } else {
                unreachable!()
            }
        }
        active_var_vec
    }
    fn get_define_and_uses(&self) -> HashMap<Function, HashMap<BasicBlock, (HashMap<usize, Value>,
                                                                            HashMap<usize, Value>)
    >> {
        let mut define_uses_map: HashMap<Function, HashMap<BasicBlock, (HashMap<usize, Value>,
                                                                     HashMap<usize, Value>)>> =
            HashMap::new();
        for func in self.func_layout(){
            let mut define_and_uses: HashMap<BasicBlock, (HashMap<usize, Value>, HashMap<usize,
                Value>)> = HashMap::new();
            let func_data = self.func(func.clone());
            for (bb, bbn) in func_data.layout().bbs(){
                let mut inst_cnt = 0 as usize;
                let mut define_value: HashMap<usize, Value> = HashMap::new();
                let mut use_value: HashMap<usize, Value> = HashMap::new();
                let bb_data = func_data.dfg().bbs().get(&bb);
                let bb_data = bb_data.unwrap();
                for inst in bbn.insts().keys(){
                    let val = func_data.dfg().value(inst.clone());
                    match value_data.kind(){
                        ValueKind::Return(ret) => {
                            // println!("{:#?}", ret);
                            // println!("{:#?}", self.dfg().value(ret.value().unwrap()));
                            // println!("=============================================");
                            if let Some(val) = ret.value(){
                                use_value.insert(inst_cnt, val.clone());
                            }
                        }
                        ValueKind::Binary(bin) => {
                            use_value.insert(inst_cnt, bin.lhs());
                            use_value.insert(inst_cnt, bin.rhs());
                            define_value.insert(inst_cnt, inst.clone());
                        }
                        ValueKind::Store(store) => {
                        }
                        ValueKind::Load(load) => {
                            define_value.insert(inst_cnt, inst.clone());
                        }
                        ValueKind::Alloc(alloc) =>{
                            define_value.insert(inst_cnt, inst.clone());
                        }
                        ValueKind::Branch(branch) => {
                            use_value.insert(inst_cnt, branch.cond().clone());
                        }
                        ValueKind::Jump(jump) => {
                        }
                        ValueKind::Call(call) => {
                        }
                        ValueKind::GetElemPtr(get_elem_ptr) => {
                            define_value.insert(inst_cnt, inst.clone());
                            use_value.insert(inst_cnt, get_elem_ptr.src().clone());
                            use_value.insert(inst_cnt, get_elem_ptr.index().clone());
                        }
                        ValueKind::GetPtr(get_ptr) => {
                            define_value.insert(inst_cnt, inst.clone());
                            use_value.insert(inst_cnt, get_ptr.src().clone());
                            use_value.insert(inst_cnt, get_ptr.index().clone());
                        }
                        _ => unreachable!(),
                    }
                    inst_cnt += 1;
                }
                define_and_uses.insert(bb.clone(), (define_value, use_value));
            }
            define_uses_map.insert(func.clone(), define_and_uses);
        }
        define_uses_map
    }
}