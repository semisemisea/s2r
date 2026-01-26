use koopa::opt::{Pass, PassManager};
use lalrpop_util::lalrpop_mod;

mod ast;
mod ast_utils;
mod ir2riscv;
mod opt;
mod register_alloc;
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
    // #[cfg(debug_assertions)]
    // println!("{input}");

    let ast = sysy::CompUnitsParser::new().parse(&input).unwrap();
    let mut ir_ctx = AstGenContext::new();
    if let Err(e) = ast.convert(&mut ir_ctx) {
        eprintln!("Encounter error: {e}");
        std::process::exit(1);
    };

    let mut pass_manager = PassManager::new();

    // let rdv = opt::dce::RemoveDiscardedValue;
    // pass_manager.register(Pass::Module(Box::new(rdv)));

    let ubb = opt::dce::UnreachableBasicBlock;
    pass_manager.register(Pass::Function(Box::new(ubb)));

    let ssa = opt::ssa::SSATransform;
    pass_manager.register(Pass::Function(Box::new(ssa)));

    pass_manager.run_passes(&mut ir_ctx.program);
    match mode.as_str() {
        "-koopa" => {
            let mut g = koopa::back::KoopaGenerator::new(Vec::new());
            g.generate_on(&ir_ctx.end()).unwrap();
            let ir_text = std::str::from_utf8(&g.writer()).unwrap().to_string();
            // #[cfg(debug_assertions)]
            // eprintln!("{ir_text}");
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
        "test" => {
            let mut g = koopa::back::KoopaGenerator::new(Vec::new());
            g.generate_on(&ir_ctx.end()).unwrap();
            let ir_text = std::str::from_utf8(&g.writer()).unwrap().to_string();
            #[cfg(debug_assertions)]
            eprintln!("{ir_text}");
            std::fs::write("hello.koopa", ir_text.clone())?;

            let driver = koopa::front::Driver::from(ir_text);
            // Because we want name to be unique :)
            let program = driver.generate_program().unwrap();
            let mut asm_ctx = AsmGenContext::new();
            asm_ctx.generate(&program).unwrap();
            std::fs::write("hello.riscv", asm_ctx.end())?;
        }
        invalid_mode => {
            eprintln!("Invalid output mode: {invalid_mode}");
            std::process::exit(1);
        }
    }
    Ok(())
}
