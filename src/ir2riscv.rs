use koopa::ir::{FunctionData, Program, Value, ValueKind, values};

use crate::riscv_utils::{AsmGenContext, GenerateAsm};

fn inst_size(func: &FunctionData, val: Value) -> usize {
    let data = func.dfg().value(val);
    match func.dfg().value(val).kind() {
        ValueKind::Alloc(_alloc) => 4,
        _ => data.ty().size(),
    }
}

impl GenerateAsm for FunctionData {
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        ctx.writeln(&format!("{}:", self.name().strip_prefix("@").unwrap()));
        ctx.incr_indent();
        // we first figure out how much the stack size should be.
        let mut sp_offset = 0;
        for (&_bb, node) in self.layout().bbs() {
            sp_offset += (self.dfg().bb(_bb).params())
                .iter()
                .map(|&param| inst_size(self, param))
                .sum::<usize>();
            sp_offset += node
                .insts()
                .keys()
                .map(|&inst| {
                    #[cfg(debug_assertions)]
                    eprintln!(
                        "{inst:?} {:?} {}",
                        self.dfg().value(inst).kind(),
                        self.dfg().value(inst).ty().size()
                    );
                    inst_size(self, inst)
                })
                .sum::<usize>();
        }

        #[cfg(debug_assertions)]
        eprintln!("sp_offset: {sp_offset}");
        let epilogue = ctx.prologue(sp_offset);

        for (&bb, node) in self.layout().bbs() {
            // then handle each instruction.
            if self.dfg().bb(bb).name().as_ref().unwrap() != "%entry" {
                ctx.decr_indent();
                ctx.writeln(&ctx.get_bb_name(bb, program));
                ctx.incr_indent();
            }
            let mut acc_offset = 0;
            for inst in node.insts().keys() {
                // give instruction a stack slot.
                let single_inst_offset = inst_size(self, *inst);
                if single_inst_offset != 0 {
                    ctx.insert_inst(*inst, acc_offset);
                }
                acc_offset += single_inst_offset;

                // update the current instruction.
                ctx.curr_inst_mut().replace(*inst);
                inst.generate(program, ctx)?;
            }
        }

        // add epilogue to the funciton at the end
        epilogue.finish(ctx);
        ctx.decr_indent();
        Ok(())
    }
}

impl GenerateAsm for Value {
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        match ctx.curr_func_data(program).dfg().value(*self).kind() {
            ValueKind::Integer(int) => int.generate(program, ctx),
            ValueKind::Alloc(alloc) => alloc.generate(program, ctx),
            ValueKind::Store(store) => store.generate(program, ctx),
            ValueKind::Load(load) => load.generate(program, ctx),
            ValueKind::Branch(_branch) => todo!(),
            ValueKind::Jump(_jump) => todo!(),
            ValueKind::Return(ret) => ret.generate(program, ctx),
            ValueKind::Binary(op) => op.generate(program, ctx),
            _ => todo!(),
        }
    }
}

///```
/// Branch {
///     cond: Value,
///     true_bb: BasicBlock,
///     false_bb: BasicBlock,
///     true_args: Vec<Value>,
///     false_args: Vec<Value>,
/// }
///```
impl GenerateAsm for values::Branch {
    fn generate(&self, _program: &Program, _ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        Ok(())
    }
}

///```
/// Jump {
///     target: BasicBlock,
///     args: Vec<Value>,
/// }
///```
impl GenerateAsm for values::Jump {
    fn generate(&self, _program: &Program, _ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        Ok(())
    }
}

impl GenerateAsm for values::Return {
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        if let Some(ret_val) = self.value() {
            ctx.helper(program, ret_val);
            // let offset = ctx.get_inst_offset(ret_val).unwrap() as i32;
            // ctx.load_word(offset);
            ctx.ret();
        }
        Ok(())
    }
}

impl GenerateAsm for values::Binary {
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        ctx.helper(program, self.lhs());
        ctx.helper(program, self.rhs());
        ctx.binary_op(self.op());
        ctx.save_at_curr_inst();
        Ok(())
    }
}

/// ```
/// Load {
///    src: Value // alloc
/// }
/// ```
/// Get 1 register
impl GenerateAsm for values::Load {
    fn generate(&self, _program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        // need to optimize.
        let offset = ctx.get_inst_offset(self.src()).unwrap() as i32;
        ctx.load_word(offset);
        ctx.save_at_curr_inst();
        Ok(())
    }
}

impl GenerateAsm for values::Alloc {
    /// alloc is marker instruction for ir representation, we have already allocate a stack(sp) to
    /// store the instruction, so it won't have counterpart in RISC-V instruction
    #[allow(unused)]
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        Ok(())
    }
}

/// ```
/// Store {
///    val: Value,
///    dest: Value, // From alloc instruction
/// }
/// ```
impl GenerateAsm for values::Store {
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        // store the value where it's located.
        ctx.helper(program, self.value());
        ctx.save_word_at_inst(self.dest());
        Ok(())
    }
}

///```
/// Integer {
///     val: i32,
/// }
/// ```
/// This instruction produce a i32 as instruction return value.
impl GenerateAsm for values::Integer {
    /// Load a ingeter immediate to a register.
    fn generate(&self, _program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        ctx.load_imm(self.value());
        Ok(())
    }
}
