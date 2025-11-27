use lalrpop_util::lalrpop_mod;

mod ast;
mod ir2riscv;
mod riscv_infra;
use ast::Convert2Koopa;

use crate::{
    ast::AstGenContext,
    ir2riscv::{AsmGenContext, GenerateAsm},
};

lalrpop_mod!(sysy);

fn main() -> std::io::Result<()> {
    let mut args = std::env::args();
    args.next();
    let mode = args.next().unwrap();
    let input = args.next().unwrap();
    args.next();
    let output = args.next().unwrap();

    let input = std::fs::read_to_string(input)?;
    // #[cfg(feature = "DEBUG")]
    println!("{input}");

    let ast = sysy::CompUnitParser::new().parse(&input).unwrap();
    let mut ctx = AstGenContext::new();
    // #[cfg(feature = "DEBUG")]
    {
        println!("{:#?}", ast);
    }
    ast.convert(&mut ctx);
    match mode.as_str() {
        "-koopa" => {
            let mut g = koopa::back::KoopaGenerator::new(Vec::new());
            g.generate_on(&ctx.end()).unwrap();
            let text_from_ir = std::str::from_utf8(&g.writer()).unwrap().to_string();
            println!("{text_from_ir}");
            std::fs::write(output, text_from_ir)?;
        }
        "-riscv" => {
            let mut g = koopa::back::KoopaGenerator::new(Vec::new());
            g.generate_on(&ctx.end()).unwrap();
            let text_from_ir = std::str::from_utf8(&g.writer()).unwrap().to_string();
            let driver = koopa::front::Driver::from(text_from_ir);
            let program = driver.generate_program().unwrap();
            let mut ctx = AsmGenContext::new();
            program.generate(&mut ctx);
            std::fs::write(output, ctx.end())?;
        }
        invalid_mode => {
            eprintln!("Invalid output mode: {invalid_mode}");
            std::process::exit(1);
        }
    }
    Ok(())
}
