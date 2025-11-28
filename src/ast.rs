use crate::ast_infra::{AstGenContext, Symbol, item};
use anyhow::{Result, anyhow, ensure};
use koopa::ir::{builder::EntityInfoQuerier, builder_traits::*, *};

/// Define how a AST node should convert to Koopa IR.
///
/// Required method: `fn convert(&self, ctx: &mut AstGenContext) -> Result<()>;`
///
/// @param `ctx`: Context that store everything needed to convert.
pub trait ToKoopaIR {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()>;
}

impl ToKoopaIR for item::CompUnit {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.func_def.convert(ctx)?;
        Ok(())
    }
}

impl ToKoopaIR for item::FuncDef {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        let func = ctx.program.new_func(FunctionData::new(
            format!("@{}", self.ident),
            vec![],
            self.func_type.clone(),
        ));
        ctx.push_func(func);
        let func_data = ctx.curr_func_data_mut();
        let bb = func_data
            .dfg_mut()
            .new_bb()
            .basic_block(Some("%entry".into()));
        func_data.layout_mut().bbs_mut().push_key_back(bb).unwrap();
        let prev_bb = ctx.set_curr_bb(bb);
        self.block.convert(ctx)?;
        ctx.pop_func();
        ctx.reset_bb(prev_bb);
        Ok(())
    }
}

impl ToKoopaIR for item::Block {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        for block_item in self.block_items.iter() {
            block_item.convert(ctx)?;
        }
        Ok(())
    }
}

impl ToKoopaIR for item::BlockItem {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::BlockItem::Decl(decl) => decl.convert(ctx)?,
            item::BlockItem::Stmt(stmt) => stmt.convert(ctx)?,
        }
        Ok(())
    }
}

impl ToKoopaIR for item::Decl {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::Decl::ConstDecl(c_decl) => c_decl.convert(ctx)?,
            item::Decl::VarDecl(v_decl) => v_decl.convert(ctx)?,
        }
        Ok(())
    }
}

impl ToKoopaIR for item::ConstDecl {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        ensure!(
            self.btype.is_i32(),
            "Unknown type for constant declaration."
        );
        self.const_defs
            .iter()
            .try_for_each(|const_def| const_def.convert(ctx))?;
        Ok(())
    }
}

impl ToKoopaIR for item::ConstDef {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        // Get the init val
        self.const_init_val.convert(ctx)?;
        let init_val = ctx.pop_val().unwrap();
        // Not a constant val
        if !ctx.curr_func_data().dfg().value(init_val).ty().is_i32() {
            return Err(anyhow!("Value can't be calculated at compile time."));
        };
        ctx.insert_const(self.ident.clone(), init_val)?;
        Ok(())
    }
}

impl ToKoopaIR for item::ConstInitVal {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.const_exp.convert(ctx)?;
        Ok(())
    }
}

impl ToKoopaIR for item::ConstExp {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.exp.convert(ctx)?;
        Ok(())
    }
}

impl ToKoopaIR for item::VarDecl {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        ensure!(self.btype.is_i32(), "Unknown type for variable declaration");
        ctx.set_def_type(self.btype.clone());
        self.var_defs
            .iter()
            .try_for_each(|var_def| var_def.convert(ctx))?;
        Ok(())
    }
}

impl ToKoopaIR for item::VarDef {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        let ty = ctx.curr_def_type().unwrap();
        // Allocate a target type of variable.
        let alloc_var = ctx.new_value().alloc(ty);
        ctx.push_inst(alloc_var);
        if let Some(ref init_val) = self.init_val {
            init_val.convert(ctx)?;
            // store the calculated value.
            let val = ctx.pop_val().unwrap();
            let store = ctx.new_value().store(val, alloc_var);
            ctx.push_inst(store);
        }
        ctx.insert_var(self.ident.clone(), alloc_var)?;
        Ok(())
    }
}

impl ToKoopaIR for item::InitVal {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.exp.convert(ctx)?;
        Ok(())
    }
}

impl ToKoopaIR for item::Stmt {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::Stmt::Assign(l_val, exp) => {
                if ctx.is_constant(l_val) {
                    return Err(anyhow!("Can't modify a constant."));
                }
                l_val.convert(ctx)?;
                let lhs_l_val = ctx.pop_val().unwrap();
                exp.convert(ctx)?;
                let rhs_exp = ctx.pop_val().unwrap();

                // Compile time type-check.
                let lhs_ptr_type = ctx.new_value().value_type(lhs_l_val);
                let rhs_exp_type = ctx.new_value().value_type(rhs_exp);
                ensure!(
                    Type::get_pointer(rhs_exp_type.clone()) == lhs_ptr_type.clone(),
                    "Type not match. {rhs_exp_type} can't store in {lhs_ptr_type}"
                );
                let store = ctx.new_value().store(rhs_exp, lhs_l_val);
                ctx.push_inst(store);
            }
            item::Stmt::Return(ret_exp) => {
                ret_exp.convert(ctx)?;
                let v_ret = ctx.pop_val();
                let func_data = ctx.curr_func_data_mut();
                let ret = func_data.dfg_mut().new_value().ret(v_ret);
                ctx.push_inst(ret);
            }
        }
        Ok(())
    }
}

impl ToKoopaIR for item::Exp {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.lor_exp.convert(ctx)?;
        Ok(())
    }
}

impl ToKoopaIR for item::LOrExp {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::LOrExp::LAndExp(land_exp) => land_exp.convert(ctx)?,
            item::LOrExp::Comp(lor_exp, land_exp) => {
                // handle lhs
                lor_exp.convert(ctx)?;
                let lhs = ctx.pop_val().unwrap();

                // check if lhs != 0
                let zero = ctx.new_value().integer(0);
                let lhs_ne_0 = ctx.new_value().binary(BinaryOp::NotEq, lhs, zero);
                ctx.push_inst(lhs_ne_0);

                // two basic block for short circuit logic
                let rhs_bb = ctx.new_bb().basic_block(Some("%lor_rhs".into()));
                ctx.register_bb(rhs_bb);
                let merge_bb = ctx
                    .new_bb()
                    .basic_block_with_params(Some("%lor_merge".into()), vec![Type::get_i32()]);
                ctx.register_bb(merge_bb);

                // short circuit logic
                let br = ctx.new_value().branch_with_args(
                    lhs_ne_0,
                    merge_bb,
                    rhs_bb,
                    vec![lhs_ne_0],
                    vec![],
                );
                ctx.push_inst(br);

                // check rhs
                let original = ctx.set_curr_bb(rhs_bb).unwrap();
                land_exp.convert(ctx)?;
                let rhs = ctx.pop_val().unwrap();

                // Constant folding
                if let ValueKind::Integer(int_lhs) = ctx.curr_func_data().dfg().value(lhs).kind()
                    && let ValueKind::Integer(int_rhs) =
                        ctx.curr_func_data().dfg().value(rhs).kind()
                {
                    // Get lhs and rhs value.
                    let int_lhs = int_lhs.value();
                    let int_rhs = int_rhs.value();

                    // remove the previous instruction
                    ctx.set_curr_bb(original);
                    ctx.remove_inst(lhs_ne_0);
                    ctx.remove_inst(br);
                    ctx.remove_bb(rhs_bb);
                    ctx.remove_bb(merge_bb);

                    let result = ctx
                        .curr_func_data_mut()
                        .dfg_mut()
                        .new_value()
                        .integer((int_lhs != 0 || int_rhs != 0) as _);
                    ctx.push_val(result);

                    return Ok(());
                }
                let rhs_ne_0 = ctx.new_value().binary(BinaryOp::NotEq, rhs, zero);
                ctx.push_inst(rhs_ne_0);

                // jump to the merge block and pass the information
                let jump = ctx.new_value().jump_with_args(merge_bb, vec![rhs_ne_0]);
                ctx.push_inst(jump);

                ctx.set_curr_bb(merge_bb);
                let result = ctx.bb_params(merge_bb)[0];
                ctx.push_val(result);
            }
        }
        Ok(())
    }
}

impl ToKoopaIR for item::LAndExp {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::LAndExp::EqExp(eq_exp) => eq_exp.convert(ctx)?,
            item::LAndExp::Comp(land_exp, eq_exp) => {
                // handle lhs
                land_exp.convert(ctx)?;
                let lhs = ctx.pop_val().unwrap();

                // check if lhs == 0
                let zero = ctx.new_value().integer(0);
                let lhs_eq_0 = ctx.new_value().binary(BinaryOp::Eq, lhs, zero);
                ctx.push_inst(lhs_eq_0);

                // two basic block for short circuit logic
                let rhs_bb = ctx.new_bb().basic_block(Some("%land_rhs".into()));
                ctx.register_bb(rhs_bb);
                let merge_bb = ctx
                    .new_bb()
                    .basic_block_with_params(Some("%land_merge".into()), vec![Type::get_i32()]);
                ctx.register_bb(merge_bb);

                //short circuit logic
                let br = ctx.new_value().branch_with_args(
                    lhs_eq_0,
                    merge_bb,
                    rhs_bb,
                    vec![zero],
                    vec![],
                );
                ctx.push_inst(br);

                // check rhs
                let original = ctx.set_curr_bb(rhs_bb).unwrap();
                eq_exp.convert(ctx)?;
                let rhs = ctx.pop_val().unwrap();

                // Constant folding
                if let ValueKind::Integer(int_lhs) = ctx.curr_func_data().dfg().value(lhs).kind()
                    && let ValueKind::Integer(int_rhs) =
                        ctx.curr_func_data().dfg().value(rhs).kind()
                {
                    // Get lhs and rhs value.
                    let int_lhs = int_lhs.value();
                    let int_rhs = int_rhs.value();

                    // remove the previous instruction
                    ctx.set_curr_bb(original);
                    ctx.remove_inst(lhs_eq_0);
                    ctx.remove_inst(br);
                    ctx.remove_bb(rhs_bb);
                    ctx.remove_bb(merge_bb);

                    let result = ctx
                        .curr_func_data_mut()
                        .dfg_mut()
                        .new_value()
                        .integer((int_lhs != 0 && int_rhs != 0) as _);
                    ctx.push_val(result);

                    return Ok(());
                }
                let rhs_ne_0 = ctx.new_value().binary(BinaryOp::NotEq, rhs, zero);
                ctx.push_inst(rhs_ne_0);

                // jump to merge block and pass the information
                let jump = ctx.new_value().jump_with_args(merge_bb, vec![rhs_ne_0]);
                ctx.push_inst(jump);

                ctx.set_curr_bb(merge_bb);
                let result = ctx.bb_params(merge_bb)[0];
                ctx.push_val(result);
            }
        }
        Ok(())
    }
}

impl ToKoopaIR for item::EqExp {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::EqExp::RelExp(rel_exp) => rel_exp.convert(ctx)?,
            item::EqExp::Comp(lhs_eq, op, rhs_rel) => {
                lhs_eq.convert(ctx)?;
                rhs_rel.convert(ctx)?;
                assert!(matches!(*op, BinaryOp::Eq | BinaryOp::NotEq));
                op.convert(ctx)?;
            }
        }
        Ok(())
    }
}

impl ToKoopaIR for item::RelExp {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::RelExp::AddExp(add_exp) => add_exp.convert(ctx)?,
            item::RelExp::Comp(lhs_rel, op, rhs_add) => {
                lhs_rel.convert(ctx)?;
                rhs_add.convert(ctx)?;
                assert!(matches!(
                    *op,
                    BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge
                ));
                op.convert(ctx)?;
            }
        }
        Ok(())
    }
}

impl ToKoopaIR for item::AddExp {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::AddExp::MulExp(mul_exp) => mul_exp.convert(ctx)?,
            item::AddExp::Comp(lhs_add, op, rhs_mul) => {
                lhs_add.convert(ctx)?;
                rhs_mul.convert(ctx)?;
                assert!(matches!(*op, BinaryOp::Sub | BinaryOp::Add));
                op.convert(ctx)?;
            }
        }
        Ok(())
    }
}

impl ToKoopaIR for item::MulExp {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::MulExp::UnaryExp(unary_exp) => unary_exp.convert(ctx)?,
            item::MulExp::Comp(lhs_mul, op, rhs_unary) => {
                lhs_mul.convert(ctx)?;
                rhs_unary.convert(ctx)?;
                assert!(matches!(*op, BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod));
                op.convert(ctx)?;
            }
        }
        Ok(())
    }
}

impl ToKoopaIR for item::UnaryExp {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::UnaryExp::PrimaryExp(exp) => exp.convert(ctx)?,
            item::UnaryExp::Unary(unary_op, unary_exp) => {
                unary_exp.convert(ctx)?;
                unary_op.convert(ctx)?;
            }
        }
        Ok(())
    }
}

impl ToKoopaIR for item::PrimaryExp {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::PrimaryExp::Exp(exp) => exp.convert(ctx)?,
            item::PrimaryExp::Number(num) => {
                let func_data = ctx.curr_func_data_mut();
                let num = func_data.dfg_mut().new_value().integer(*num);
                ctx.push_val(num);
            }
            // LVal on the right side.
            // Meaning it's not defining but using a variable.
            item::PrimaryExp::LVal(l_val) => {
                let val = match ctx.get_symbol(&l_val.ident).unwrap() {
                    // If it's a constant, because we store the value so we directly pull it out.
                    Symbol::Constant(const_val) => const_val,
                    // If it's a variable, because we store the pointer so we load it and pull out.
                    Symbol::Variable(var_ptr) => {
                        let load = ctx.new_value().load(var_ptr);
                        ctx.push_inst(load);
                        load
                    }
                };
                ctx.push_val(val);
            }
        }
        Ok(())
    }
}

impl ToKoopaIR for item::LVal {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        let symbol = ctx
            .get_symbol(&self.ident)
            .ok_or(anyhow!("Variable {} not exists.", &*self.ident))?;
        let val = match symbol {
            crate::ast_infra::Symbol::Constant(const_val) => const_val,
            crate::ast_infra::Symbol::Variable(p_val) => p_val,
        };
        // let val = ctx.new_value().integer(val);
        ctx.push_val(val);
        Ok(())
    }
}

impl ToKoopaIR for koopa::ir::BinaryOp {
    /// Assure you will call a binary operation or otherwise use crate::ast::item::UnaryOp
    ///
    /// General method to use two value to generate a value and an instruction.
    /// WARNING: Check the limitaion of binary operator before the call.
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        let rhs = ctx.pop_val().unwrap();
        let lhs = ctx.pop_val().unwrap();

        // Constant folding
        if let ValueKind::Integer(int_lhs) = ctx.curr_func_data().dfg().value(lhs).kind()
            && let ValueKind::Integer(int_rhs) = ctx.curr_func_data().dfg().value(rhs).kind()
        {
            let int_lhs = int_lhs.value();
            let int_rhs = int_rhs.value();
            let res = match self {
                BinaryOp::NotEq => (int_lhs != int_rhs) as i32,
                BinaryOp::Eq => (int_lhs == int_rhs) as i32,
                BinaryOp::Gt => (int_lhs > int_rhs) as i32,
                BinaryOp::Lt => (int_lhs < int_rhs) as i32,
                BinaryOp::Ge => (int_lhs >= int_rhs) as i32,
                BinaryOp::Le => (int_lhs <= int_rhs) as i32,
                BinaryOp::Add => int_lhs.wrapping_add(int_rhs),
                BinaryOp::Sub => int_lhs.wrapping_sub(int_rhs),
                BinaryOp::Mul => int_lhs.wrapping_mul(int_rhs),
                BinaryOp::Div => {
                    if int_rhs == 0 {
                        return Err(anyhow::anyhow!("Division by zero"));
                    } else {
                        int_lhs.wrapping_div(int_rhs)
                    }
                }
                BinaryOp::Mod => {
                    if int_rhs == 0 {
                        return Err(anyhow::anyhow!("Modulo by zero"));
                    } else {
                        int_lhs.wrapping_rem(int_rhs)
                    }
                }
                BinaryOp::And => int_lhs & int_rhs,
                BinaryOp::Or => int_lhs | int_rhs,
                BinaryOp::Xor => int_lhs ^ int_rhs,
                BinaryOp::Shl => int_lhs.wrapping_shl(int_rhs as u32),
                BinaryOp::Shr => (int_lhs as u32).wrapping_shr(int_rhs as u32) as i32,
                BinaryOp::Sar => int_lhs.wrapping_shr(int_rhs as u32),
            };

            let val = ctx.new_value().integer(res);
            ctx.push_val(val);
            return Ok(());
        }

        let func_data = ctx.curr_func_data_mut();
        let operation = func_data.dfg_mut().new_value().binary(*self, lhs, rhs);
        ctx.push_val(operation);
        ctx.push_inst(operation);
        Ok(())
    }
}

impl ToKoopaIR for item::UnaryOp {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        // if `+` is unary then it will do nothing.
        if matches!(self, item::UnaryOp::Add) {
            return Ok(());
        }

        let rhs = ctx.pop_val().unwrap();

        //Constant folding
        let rhs_val = ctx.curr_func_data().dfg().value(rhs);
        if matches!(rhs_val.kind(), ValueKind::Integer(_)) {
            let ValueKind::Integer(integer) = rhs_val.kind().clone() else {
                unreachable!()
            };
            let operation = match self {
                item::UnaryOp::Add => unreachable!(),
                item::UnaryOp::Minus => ctx.new_value().integer(-integer.value()),
                item::UnaryOp::Negation => ctx.new_value().integer((integer.value() == 0) as _),
            };
            ctx.push_val(operation);
            return Ok(());
        }

        let func_data = ctx.curr_func_data_mut();
        let zero = func_data.dfg_mut().new_value().integer(0);
        let operation = match self {
            item::UnaryOp::Add => unreachable!(),
            item::UnaryOp::Minus => {
                func_data
                    .dfg_mut()
                    .new_value()
                    .binary(BinaryOp::Sub, zero, rhs)
            }
            item::UnaryOp::Negation => {
                func_data
                    .dfg_mut()
                    .new_value()
                    .binary(BinaryOp::Eq, zero, rhs)
            }
        };
        ctx.push_val(operation);
        ctx.push_inst(operation);
        Ok(())
    }
}
