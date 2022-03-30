use lalrpop_util::lalrpop_mod;
use std::env::args;
use std::fs::read_to_string;
use std::io::{Result, Write};
use std::fs::File;
mod ast;
mod codeGenerator;

use crate::ast::GetKoopa;
use crate::codeGenerator::code_generator::GenerateAsm;
// 引用 lalrpop 生成的解析器
// 因为我们刚刚创建了 sysy.lalrpop, 所以模块名是 sysy
lalrpop_mod!(sysy);

fn main() -> Result<()> {
    // 解析命令行参数
    let mut args = args();
    args.next();
    let mode = args.next().unwrap();
    let input = args.next().unwrap();
    args.next();
    let output = args.next().unwrap();
    let mut file = File::create(output).unwrap();

    // 读取输入文件
    let input = read_to_string(input)?;

    // 调用 lalrpop 生成的 parser 解析输入文件
    let ast = sysy::CompUnitParser::new().parse(&input).unwrap();

    // 输出解析得到的 AST
    // println!("{:#?}", ast);
    // println!("{}", ir);
    if mode == "-koopa"{
        let ir = ast.get_koopa();
        println!("{}", ir);
        file.write(ir.as_bytes());
    } else if mode == "-riscv"{
        let ir = ast.get_koopa();
        let driver = koopa::front::Driver::from(ir);
        let program = driver.generate_program().unwrap();
        let ir = program.generate();
        println!("{}", ir);
        file.write(ir.as_bytes());
    }

    Ok(())
}
