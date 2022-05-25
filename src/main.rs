extern crate koopa;

use lalrpop_util::lalrpop_mod;
use std::env::args;
use std::fs::read_to_string;
use std::io::{Result, Write};
use std::fs::File;


mod code_generator;
mod front_end;
mod optim;

use front_end::parser::GetKoopa;
use crate::code_generator::code_generator::GenerateAsm;
use crate::optim::cfg::IntervalAnalysis;
// 引用 lalrpop 生成的解析器
// 因为我们刚刚创建了 sysy.lalrpop, 所以模块名是 sysy


lalrpop_mod!(sysy);

fn main() {
    let a = try_main();
    match a{
        Ok(_) => return,
        Err(e) => eprintln!("{}", e)
    }
}
fn try_main() -> Result<()> {
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
    if mode == "-koopa"{
        let ir = ast.get_koopa();
        file.write(ir.as_bytes());
    } else if mode == "-riscv"{
        let ir = ast.get_koopa();
        println!("{}", ir);
        let driver = koopa::front::Driver::from(ir);
        let program = driver.generate_program().unwrap();
        let ir = program.generate();
        file.write(ir.as_bytes());
    } else if mode == "-perf"{
        let ir = ast.get_koopa();
        println!("{}", ir);
        let driver = koopa::front::Driver::from(ir);
        let program = driver.generate_program().unwrap();
        let ir = program.generate();
        file.write(ir.as_bytes());
    }
    Ok(())
}

#[test]
fn test(){
    // 读取输入文件
    let input = read_to_string("/Users/csy/testcases/lv5/6_complex_scopes.c").unwrap();


    // 调用 lalrpop 生成的 parser 解析输入文件
    let ast = sysy::CompUnitParser::new().parse(&input).unwrap();
    let ir = ast.get_koopa();
    println!("{}", ir);
    let driver = koopa::front::Driver::from(ir);
    let program = driver.generate_program().unwrap();
    // println!("{:#?}", program.func_layout());
    let a = program.get_interval();
    let b = program.get_interval();
    for (func, map_1) in a{
        for (func, map_2) in b{
            println!("{}", map_2 == map_1);
        }
    }

}


