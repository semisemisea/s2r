use koopa::ir::{FunctionData, Program, TypeKind, Value, ValueKind, values};

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
        let (inst_offset, call_ra, max_args) = self
            .layout()
            .bbs()
            .iter()
            .flat_map(|(&bb, node)| self.dfg().bb(bb).params().iter().chain(node.insts().keys()))
            .fold(
                (0, false, 0),
                |(mut inst_offset, mut call_ra, mut max_args), &inst| {
                    inst_offset += inst_size(self, inst);
                    if let ValueKind::Call(call) = self.dfg().value(inst).kind() {
                        call_ra = true;
                        max_args = max_args.max(call.args().len())
                    }

                    (inst_offset, call_ra, max_args)
                },
            );

        // #[cfg(debug_assertions)]
        // {
        //     eprintln!("function:     {}", self.name().strip_prefix('@').unwrap());
        //     eprintln!("inst_offset:  {inst_offset}");
        //     eprintln!("call_ra:      {call_ra}");
        //     eprintln!("max_args:     {max_args}");
        //     eprintln!();
        // }

        let offset = inst_offset + if call_ra { 4 } else { 0 } + (max_args.max(8) - 8) * 4;
        // According to RISC-V, sp_offset should be aligned with 16.
        let offset = if (offset & 0x0F) != 0 {
            (offset + 0x0F) >> 4 << 4
        } else {
            offset
        };
        ctx.prologue(offset, call_ra);

        self.params()
            .iter()
            .skip(8)
            .fold(0usize, |acc_offset, &param| {
                ctx.insert_inst(param, offset + acc_offset);
                acc_offset + self.dfg().value(param).ty().size()
            });

        let mut curr_offset = (max_args.max(8) - 8) * 4;

        for &bb_param in self
            .layout()
            .bbs()
            .iter()
            .flat_map(|(&bb, _)| self.dfg().bb(bb).params())
        {
            ctx.insert_inst(bb_param, curr_offset);
            curr_offset += inst_size(self, bb_param);
        }

        // then handle each instruction.
        for (&bb, node) in self.layout().bbs() {
            if self.dfg().bb(bb).name().as_ref().unwrap() != "%entry" {
                ctx.decr_indent();
                ctx.writeln(&format!("{}:", ctx.get_bb_name(bb, program)));
                ctx.incr_indent();
            }
            let insts_iter = node.insts().keys();
            for &inst in insts_iter {
                // update the current instruction.
                let single_inst_size = inst_size(self, inst);
                if single_inst_size != 0 {
                    ctx.insert_inst(inst, curr_offset);
                }
                ctx.curr_inst_mut().replace(inst);
                inst.generate(program, ctx)?;
                curr_offset += inst_size(self, inst);
            }
        }

        // ctx.stack_slots_debug(self);

        ctx.decr_indent();
        ctx.pop_epilogue();
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
            ValueKind::Branch(branch) => branch.generate(program, ctx),
            ValueKind::Jump(jump) => jump.generate(program, ctx),
            ValueKind::Return(ret) => ret.generate(program, ctx),
            ValueKind::Binary(op) => op.generate(program, ctx),
            ValueKind::BlockArgRef(block_arg_ref) => block_arg_ref.generate(program, ctx),
            ValueKind::Call(call) => call.generate(program, ctx),
            _ => todo!(),
        }
    }
}

impl GenerateAsm for values::Call {
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        // arity of the function
        let arity = self.args().len();

        // reference to function arguments
        let args = self.args();

        // function data
        let func_data = program.func(self.callee());

        // name of the function
        let name = func_data.name().strip_prefix('@').unwrap();

        // move the 1st-8th parameters to the register
        for (i, &arg) in args[..8.min(arity)].iter().enumerate() {
            use crate::riscv_utils::Register::*;
            let rd = (a0 as u8 + i as u8).try_into().unwrap();
            ctx.load_to_para_register(program, arg, rd);
        }

        // move the 8th and more parameters to the stack
        for (i, &arg) in args.iter().skip(8).enumerate() {
            ctx.load_to_register(program, arg);
            ctx.save_word_with_offset(4 * i as i32);
        }

        // write the call instruction
        use crate::riscv_utils::RiscvInst::call;
        ctx.write_inst(call {
            callee: name.to_string(),
        });

        let TypeKind::Function(_param_ty, ret_ty) = func_data.ty().kind() else {
            unreachable!()
        };
        if !ret_ty.is_unit() {
            ctx.alloc_ret_reg();
            ctx.save_word_at_curr_inst();
        }

        Ok(())
    }
}

impl GenerateAsm for values::BlockArgRef {
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        let curr_inst = ctx.curr_inst_mut().unwrap();
        ctx.load_to_register(program, curr_inst);
        Ok(())
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
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        ctx.load_to_register(program, self.cond());
        let true_args_and_params = self
            .true_args()
            .iter()
            .zip(ctx.bb_params(self.true_bb(), program));
        let false_args_and_params = self
            .false_args()
            .iter()
            .zip(ctx.bb_params(self.false_bb(), program));
        true_args_and_params
            .chain(false_args_and_params)
            .for_each(|(&arg, &param)| {
                ctx.load_to_register(program, arg);
                ctx.save_word_at_inst(param);
            });
        ctx.if_jump(self.true_bb(), self.false_bb(), program);
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
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        let args_and_params = self
            .args()
            .iter()
            .zip(ctx.bb_params(self.target(), program));
        args_and_params.for_each(|(&arg, &param)| {
            ctx.load_to_register(program, arg);
            ctx.save_word_at_inst(param);
        });
        ctx.jump(self.target(), program);
        Ok(())
    }
}

impl GenerateAsm for values::Return {
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        if let Some(ret_val) = self.value() {
            ctx.load_to_register(program, ret_val);
            ctx.ret();
        } else {
            ctx.void_ret();
        }
        Ok(())
    }
}

impl GenerateAsm for values::Binary {
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        ctx.load_to_register(program, self.lhs());
        ctx.load_to_register(program, self.rhs());
        ctx.binary_op(self.op());
        ctx.save_word_at_curr_inst();
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
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        if self.src().is_global() {
            ctx.load_address(get_glob_var_name(self.src(), program));
            ctx.load_from_address();
            ctx.save_word_at_curr_inst();
        } else {
            let offset = ctx.get_inst_offset(self.src()).unwrap() as i32;
            ctx.load_word(offset);
            ctx.save_word_at_curr_inst();
        }
        Ok(())
    }
}

impl GenerateAsm for values::Alloc {
    /// alloc is marker instruction for IR representation, we have already allocate a stack(sp) to
    /// store the instruction, so it won't have counterpart in RISC-V instruction
    #[allow(unused)]
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        Ok(())
    }
}

/// ```
/// Store {
///    value: Value,
///    dest: Value, // From alloc instruction
/// }
/// ```
impl GenerateAsm for values::Store {
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()> {
        if self.dest().is_global() {
            ctx.load_address(get_glob_var_name(self.dest(), program));
            ctx.load_to_register(program, self.value());
            ctx.save_word_at_address();
        } else {
            // store the value where it's located.
            ctx.load_to_register(program, self.value());
            ctx.save_word_at_inst(self.dest());
        }
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

/// also we remove the prefix '%'
#[inline]
fn get_glob_var_name(var: Value, program: &Program) -> String {
    assert!(var.is_global());
    program
        .borrow_value(var)
        .name()
        .clone()
        .unwrap()
        .strip_prefix('%')
        .unwrap()
        .to_string()
}
