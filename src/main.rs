use lalrpop_util::lalrpop_mod;

mod ast;
mod ast_infra;
mod ir2riscv;
mod riscv_infra;
use ast::ToKoopaIR;

use crate::{ast_infra::AstGenContext, riscv_infra::AsmGenContext};

lalrpop_mod!(sysy);

fn main() -> std::io::Result<()> {
    let mut args = std::env::args();
    args.next();
    let mode = args.next().unwrap();
    let input = args.next().unwrap();
    args.next();
    let output = args.next().unwrap();

    let input = std::fs::read_to_string(input)?;
    #[cfg(debug_assertions)]
    println!("{input}");

    let ast = sysy::CompUnitParser::new().parse(&input).unwrap();
    let mut ir_ctx = AstGenContext::new();
    if let Err(e) = ast.convert(&mut ir_ctx) {
        eprintln!("Encounter error: {e}");
        std::process::exit(1);
    };
    match mode.as_str() {
        "-koopa" => {
            let mut g = koopa::back::KoopaGenerator::new(Vec::new());
            g.generate_on(&ir_ctx.end()).unwrap();
            let text_from_ir = std::str::from_utf8(&g.writer()).unwrap().to_string();
            println!("{text_from_ir}");
            std::fs::write(output, text_from_ir)?;
        }
        "-riscv" => {
            let mut asm_ctx = AsmGenContext::new();
            asm_ctx.generate(&ir_ctx.program).unwrap();
            std::fs::write(output.clone(), asm_ctx.end())?;
        }
        invalid_mode => {
            eprintln!("Invalid output mode: {invalid_mode}");
            std::process::exit(1);
        }
    }
    Ok(())
}
