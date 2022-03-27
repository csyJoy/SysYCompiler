use koopa::ir::{FunctionData, Program,ValueKind};
use koopa::ir::values::Return;

pub trait GenerateAsm{
    fn generate(&self) -> String;
}

impl GenerateAsm for Program{
    fn generate(&self) -> String {
        let mut head = "\t.text\n".to_string();
        let mut func_def = "".to_string();
        for &func in self.func_layout(){
            let tmp = &self.func(func).name().to_string()[1..];
            head += &format!("\t.global {}\n", tmp);
            func_def += &self.func(func).generate()
        }
        head + &func_def
    }
}
impl GenerateAsm for FunctionData{
    fn generate(&self) -> String {
        let mut s = "".to_string();
        s += &format!("{}:\n", &self.name().to_string()[1..]);
        for (&bb, node) in self.layout().bbs(){
            for &inst in node.insts().keys(){
                let value_data = self.dfg().value(inst);
                match value_data.kind(){
                    ValueKind::Return(ret) => {
                        self.return_gen(&mut s, ret);
                    }
                    _ => unreachable!(),
                }
            }
        }
        s
    }
}

trait splitGen{
    fn return_gen(&self, s: &mut String, ret: &Return);
}
impl splitGen for FunctionData {
    fn return_gen(&self, s: &mut String, ret: &Return) {
        if let Some(val) = ret.value() {
            let a = self.dfg().value(val);
            let b = a.kind();
            match b {
                ValueKind::Integer(i) =>
                    *s += &format!("\tli a0, {}\n", i.value()),
                _ => unreachable!(),
            }
        }
        *s += &format!("\tret\n");
    }
}
