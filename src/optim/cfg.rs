use std::rc::Weak;
use std::sync::Arc;

pub struct Cfg{
    pub enter: CfgInner,
    pub exit: CfgInner,
    pub other: Vec<CfgInner>,
    pub name: String
}

pub struct CfgInner{
    pub father: Vec<Weak<CfgInner>>,
    pub son: Vec<Arc<CfgInner>>,
    pub code: Vec<String>
}
impl CfgInner{
    fn new_enter_node() -> CfgInner{
        CfgInner{father: Vec::new(), son: Vec:: new(), code: Vec::new()}
    }
    fn new_exit_node() ->  CfgInner{
        CfgInner{father: Vec::new(), son: Vec:: new(), code: Vec::new()}
    }
    fn attach_with_son_node(&self, son: &CfgInner){

    }
    fn attach_with_father_node(&self, father: &CfgInner){

    }
}

impl Cfg{
    fn build_cfg(code: String) -> Vec<Cfg>{
        let split_code = code.split("\n").collect::<Vec<&str>>();
        let vec: Vec<Cfg> = Vec::new();
        let mut now_cfg = Cfg{enter: CfgInner::new_enter_node(), exit: CfgInner::new_exit_node(),
            other: Vec::new(), name: "".to_string()};
        for i in split_code{
            if i[0] == 'f' && i[1] == 'n'{ // start build a cfg
                let func_signature = i.split(" ").collect::<Vec<&str>>();
                let func_name = func_signature[1].to_string()[1..].to_string();
                now_cfg.name = func_name;
            } else if i[0] == '%'{
                if i.to_string() == format!("%enter"){
                }
            } else if i[0] == '{'{

            } else {
                continue;
            }
        }
        vec
    }
}