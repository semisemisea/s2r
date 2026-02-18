use koopa::opt::{Pass, PassManager};
use lalrpop_util::lalrpop_mod;

mod asm_opt;
mod asm_pass_utils;
mod ast;
mod ast_utils;
mod ir2riscv;
mod opt;
mod register_alloc;
mod riscv_utils;

const SSA_ENABLE: bool = true;
const SCCP_ENABLE: bool = false;
const DCE_ENABLE: bool = true;

use crate::{
    asm_pass_utils::AsmPassManager,
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

    if SSA_ENABLE {
        let ssa = opt::ssa::SSATransform;
        pass_manager.register(Pass::Function(Box::new(ssa)));
    }

    if DCE_ENABLE {
        // let dpe = opt::dce::DeadPhiElimination;
        // pass_manager.register(Pass::Function(Box::new(dpe)));
        let dce = opt::dce::DeadCodeElimination;
        pass_manager.register(Pass::Module(Box::new(dce)));
    }

    if SCCP_ENABLE {
        let sccp = opt::const_prop::SparseConditionConstantPropagation;
        pass_manager.register(Pass::Function(Box::new(sccp)));
        let ubb = opt::dce::UnreachableBasicBlock;
        pass_manager.register(Pass::Function(Box::new(ubb)));
        // let joe = opt::dce::JumpOnlyElimination;
        // pass_manager.register(Pass::Function(Box::new(joe)));
    }

    if DCE_ENABLE {
        let dpe = opt::dce::DeadPhiElimination;
        pass_manager.register(Pass::Function(Box::new(dpe)));
        let dce = opt::dce::DeadCodeElimination;
        pass_manager.register(Pass::Module(Box::new(dce)));
    }

    pass_manager.run_passes(&mut ir_ctx.program);

    register_alloc::liveness_analysis(&ir_ctx.program);

    let mut g = koopa::back::KoopaGenerator::new(Vec::new());
    g.generate_on(&ir_ctx.end()).unwrap();
    let ir_text = std::str::from_utf8(&g.writer()).unwrap().to_string();

    let driver = koopa::front::Driver::from(ir_text.clone());
    // Because we want name to be unique :)
    let program = driver.generate_program().unwrap();
    let asm_ctx = AsmGenContext::new();
    let mut insts = asm_ctx.generate(&program).unwrap();

    let mut asm_pass_manager = AsmPassManager::new();

    let useless_load = asm_opt::peekhole_load::PeekholeLoadElimination;
    asm_pass_manager.register(Box::new(useless_load));

    asm_pass_manager.run_passes(&mut insts);
    match mode.as_str() {
        "-koopa" => {
            std::fs::write(output, ir_text)?;
        }
        "-riscv" => {
            std::fs::write(output.clone(), riscv_utils::end(insts))?;
        }
        "test" => {
            std::fs::write("hello.koopa", ir_text)?;
            std::fs::write("hello.riscv", riscv_utils::end(insts))?;
        }
        invalid_mode => {
            eprintln!("Invalid output mode: {invalid_mode}");
            std::process::exit(1);
        }
    }
    Ok(())
}
