use lalrpop_util::lalrpop_mod;

mod ast;
mod ast_utils;
mod ir2riscv;
mod riscv_utils;

use crate::{
    ast_utils::{AstGenContext, ToKoopaIR},
    riscv_utils::AsmGenContext,
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
    println!("{input}");

    let ast = sysy::CompUnitsParser::new().parse(&input).unwrap();
    let mut ir_ctx = AstGenContext::new();
    if let Err(e) = ast.convert(&mut ir_ctx) {
        eprintln!("Encounter error: {e}");
        std::process::exit(1);
    };
    match mode.as_str() {
        "-koopa" => {
            let mut g = koopa::back::KoopaGenerator::new(Vec::new());
            g.generate_on(&ir_ctx.end()).unwrap();
            let ir_text = std::str::from_utf8(&g.writer()).unwrap().to_string();
            #[cfg(debug_assertions)]
            eprintln!("{ir_text}");
            std::fs::write(output, ir_text)?;
        }
        "-riscv" => {
            let mut g = koopa::back::KoopaGenerator::new(Vec::new());
            g.generate_on(&ir_ctx.end()).unwrap();
            let ir_text = std::str::from_utf8(&g.writer()).unwrap().to_string();
            let driver = koopa::front::Driver::from(ir_text);
            // Because we want name to be unique :)
            let program = driver.generate_program().unwrap();
            let mut asm_ctx = AsmGenContext::new();
            asm_ctx.generate(&program).unwrap();
            std::fs::write(output.clone(), asm_ctx.end())?;
        }
        invalid_mode => {
            eprintln!("Invalid output mode: {invalid_mode}");
            std::process::exit(1);
        }
    }
    Ok(())
}
