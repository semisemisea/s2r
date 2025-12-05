use crate::ast_utils::{AstGenContext, Symbol, ToKoopaIR, item};
use anyhow::{Context, Result, anyhow, bail, ensure};
use koopa::ir::{builder::EntityInfoQuerier, builder_traits::*, *};

impl ToKoopaIR for item::CompUnits {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        ctx.decl_library_functions()?;
        self.comp_units
            .iter()
            .try_for_each(|comp_unit| comp_unit.convert(ctx))
    }

    fn global_convert(&self, _ctx: &mut AstGenContext) -> Result<()> {
        unreachable!("No corresponding syntax")
    }
}

impl ToKoopaIR for item::CompUnit {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::CompUnit::FuncDef(func_def) => func_def.convert(ctx),
            item::CompUnit::Decl(decl) => decl.global_convert(ctx),
        }
    }

    fn global_convert(&self, _ctx: &mut AstGenContext) -> Result<()> {
        unreachable!("No corresponding syntax")
    }
}

impl ToKoopaIR for item::FuncDef {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        // Register the function to get handle
        let func = ctx.program.new_func(FunctionData::new(
            format!("@{}", self.ident),
            self.params.iter().map(|x| x.b_type.clone()).collect(),
            self.func_type.clone(),
        ));
        // Prologue
        // - Add function to the stack
        // - Insert the "entry" basic block and save it.
        // - Increse the scope depth.
        ctx.insert_func(self.ident.clone(), func)?;
        ctx.push_func(func);
        let entry_bb = ctx.add_entry_bb();
        ctx.set_curr_bb(entry_bb);
        // let prev_bb = ctx.set_curr_bb(entry_bb);

        // Recursive conversion.
        ctx.add_scope();
        let params = ctx.curr_func_data().params().to_vec();
        let ty_name_and_val = self
            .params
            .iter()
            .cloned()
            .zip(params.iter())
            .map(|(p, &v)| (p.b_type, p.ident, v));
        for (ty, ident, param_val) in ty_name_and_val {
            let alloc = ctx.new_local_value().alloc(ty);
            ctx.curr_func_data_mut()
                .dfg_mut()
                .set_value_name(alloc, Some(format!("%{}", &*ident)));
            let store = ctx.new_local_value().store(param_val, alloc);
            ctx.insert_var(ident, alloc)?;
            ctx.push_inst(alloc);
            ctx.push_inst(store);
        }
        self.block
            .block_items
            .iter()
            .try_for_each(|block_item| block_item.convert(ctx))?;
        ctx.del_scope();

        // Epilogue
        let ret = ctx.new_local_value().ret(None);
        let bb_node = ctx.curr_func_data().layout().bbs().back_node().unwrap();

        if !bb_node.insts().back_key().is_some_and(|&inst| {
            matches!(
                ctx.curr_func_data().dfg().value(inst).kind(),
                ValueKind::Branch(_) | ValueKind::Jump(_) | ValueKind::Return(_)
            )
        }) {
            // TODO: Should check the type of the function. Only the `void` type of function
            // can implicitly add return at the end.
            let bb_node = ctx
                .curr_func_data_mut()
                .layout_mut()
                .bbs_mut()
                .back_node_mut()
                .unwrap();
            bb_node.insts_mut().push_key_back(ret).unwrap();
        }

        ctx.pop_func();

        Ok(())
    }

    fn global_convert(&self, _ctx: &mut AstGenContext) -> Result<()> {
        unreachable!("No corresponding syntax")
    }
}

impl ToKoopaIR for item::Block {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        ctx.add_scope();
        self.block_items
            .iter()
            .try_for_each(|block_item| block_item.convert(ctx))?;
        ctx.del_scope();
        Ok(())
    }

    fn global_convert(&self, _ctx: &mut AstGenContext) -> Result<()> {
        unreachable!("No corresponding syntax")
    }
}

impl ToKoopaIR for item::BlockItem {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::BlockItem::Decl(decl) => decl.convert(ctx),
            item::BlockItem::Stmt(stmt) => stmt.convert(ctx),
        }
    }

    fn global_convert(&self, _ctx: &mut AstGenContext) -> Result<()> {
        unreachable!("No corresponding syntax")
    }
}

impl ToKoopaIR for item::Decl {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::Decl::ConstDecl(c_decl) => c_decl.convert(ctx),
            item::Decl::VarDecl(v_decl) => v_decl.convert(ctx),
        }
    }

    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::Decl::ConstDecl(c_decl) => c_decl.global_convert(ctx),
            item::Decl::VarDecl(v_decl) => v_decl.global_convert(ctx),
        }
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
            .try_for_each(|const_def| const_def.convert(ctx))
    }

    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        ensure!(
            self.btype.is_i32(),
            "Unknown type for constant declaration."
        );
        self.const_defs
            .iter()
            .try_for_each(|const_def| const_def.global_convert(ctx))
    }
}

impl ToKoopaIR for item::ConstDef {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        // Get the init val
        self.const_init_val.convert(ctx)?;
        let init_val = ctx.pop_val().unwrap();
        // Not a constant val
        if !ctx.curr_func_data().dfg().value(init_val).kind().is_const() {
            bail!("Value can't be calculated at compile time.");
        };
        ctx.insert_const(self.ident.clone(), init_val)
    }

    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.const_init_val.global_convert(ctx)?;
        let init_val = ctx.pop_val().unwrap();
        // eprintln!("{:?}", ctx.program.borrow_value(init_val).kind());
        // No more check
        ctx.insert_const(self.ident.clone(), init_val)
    }
}

impl ToKoopaIR for item::ConstInitVal {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.const_exp.convert(ctx)
    }

    #[inline]
    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.const_exp.global_convert(ctx)
    }
}

impl ToKoopaIR for item::ConstExp {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.exp.convert(ctx)
    }

    #[inline]
    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.exp.global_convert(ctx)
    }
}

impl ToKoopaIR for item::VarDecl {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        ensure!(self.btype.is_i32(), "Unknown type for variable declaration");
        ctx.set_def_type(self.btype.clone());
        self.var_defs
            .iter()
            .try_for_each(|var_def| var_def.convert(ctx))
    }

    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        ensure!(self.btype.is_i32(), "Unknown type for variable declaration");
        ctx.set_def_type(self.btype.clone());
        self.var_defs
            .iter()
            .try_for_each(|var_def| var_def.global_convert(ctx))
    }
}

impl ToKoopaIR for item::VarDef {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        let ty = ctx.curr_def_type().unwrap();
        // Allocate a target type of variable.
        let alloc_var = ctx.new_local_value().alloc(ty);
        ctx.curr_func_data_mut()
            .dfg_mut()
            .set_value_name(alloc_var, Some(format!("@{}", self.ident.clone())));
        ctx.push_inst(alloc_var);
        if let Some(ref init_val) = self.init_val {
            init_val.convert(ctx)?;
            // store the calculated value.
            let val = ctx.pop_val().unwrap();
            let store = ctx.new_local_value().store(val, alloc_var);
            ctx.push_inst(store);
        }
        ctx.insert_var(self.ident.clone(), alloc_var)
    }

    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        let ty = ctx.curr_def_type().unwrap();
        let init_val = if let Some(ref init_val) = self.init_val {
            init_val.global_convert(ctx)?;
            ctx.pop_val().unwrap()
        } else {
            ctx.new_global_value().zero_init(ty.clone())
        };
        let val = ctx.new_global_value().global_alloc(init_val);
        ctx.insert_var(self.ident.clone(), val)
    }
}

impl ToKoopaIR for item::InitVal {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.exp.convert(ctx)
    }

    #[inline]
    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.exp.global_convert(ctx)
    }
}

impl ToKoopaIR for item::Stmt {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::Stmt::Assign(assign_stmt) => assign_stmt.convert(ctx),
            item::Stmt::Return(return_stmt) => return_stmt.convert(ctx),
            item::Stmt::Block(block) => block.convert(ctx),
            item::Stmt::Single(exp) => exp.as_ref().map_or(Ok(()), |e| e.convert(ctx)),
            item::Stmt::IfStmt(if_stmt) => if_stmt.convert(ctx),
            item::Stmt::WhileStmt(while_stmt) => while_stmt.convert(ctx),
            item::Stmt::Break(break_stmt) => break_stmt.convert(ctx),
            item::Stmt::Continue(continue_stmt) => continue_stmt.convert(ctx),
        }
    }

    fn global_convert(&self, _ctx: &mut AstGenContext) -> Result<()> {
        unreachable!("No corresponding syntax")
    }
}

impl ToKoopaIR for item::Break {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        let loop_end = ctx.curr_loop().context("Use break outside of loop")?.1;
        let jump_to_loop_end = ctx.new_local_value().jump(loop_end);
        ctx.push_inst(jump_to_loop_end);
        Ok(())
    }

    fn global_convert(&self, _ctx: &mut AstGenContext) -> Result<()> {
        unreachable!("No corresponding syntax")
    }
}

impl ToKoopaIR for item::Continue {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        let loop_start = ctx.curr_loop().context("Use continue outside of loop")?.0;
        let jump_to_loop_start = ctx.new_local_value().jump(loop_start);
        ctx.push_inst(jump_to_loop_start);
        Ok(())
    }

    fn global_convert(&self, _ctx: &mut AstGenContext) -> Result<()> {
        unreachable!("No corresponding syntax")
    }
}

impl ToKoopaIR for item::WhileStmt {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        // create 3 basic blocks for while loop
        let entry = ctx.new_bb().basic_block(Some("%while_entry".into()));
        ctx.register_bb(entry);
        let body = ctx.new_bb().basic_block(Some("%while_body".into()));
        ctx.register_bb(body);
        let end = ctx.new_bb().basic_block(Some("%while_end".into()));
        ctx.register_bb(end);
        ctx.push_loop(entry, end);

        // jump into while entry block unconditionally
        let jump_to_while_entry = ctx.new_local_value().jump(entry);
        ctx.push_inst(jump_to_while_entry);

        ctx.set_curr_bb(entry);
        self.cond.convert(ctx)?;
        let cond_val = ctx.pop_val().unwrap();
        let branch = ctx.new_local_value().branch(cond_val, body, end);
        ctx.push_inst(branch);

        ctx.set_curr_bb(body);
        self.body.convert(ctx)?;
        let jump = ctx.new_local_value().jump(entry);
        ctx.push_inst(jump);

        ctx.pop_loop();
        ctx.set_curr_bb(end);
        Ok(())
    }

    fn global_convert(&self, _ctx: &mut AstGenContext) -> Result<()> {
        unreachable!("No corresponding syntax")
    }
}

impl ToKoopaIR for item::ReturnStmt {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        let v_ret = match &self.exp {
            Some(ret_exp) => {
                ret_exp.convert(ctx)?;
                ctx.pop_val()
            }
            None => None,
        };
        let ret = ctx.curr_func_data_mut().dfg_mut().new_value().ret(v_ret);
        ctx.push_inst(ret);
        Ok(())
    }

    fn global_convert(&self, _ctx: &mut AstGenContext) -> Result<()> {
        unreachable!("No corresponding syntax")
    }
}

impl ToKoopaIR for item::IfStmt {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        // Get condition exp value.
        self.cond.convert(ctx)?;
        let cond_val = ctx.pop_val().unwrap();
        let then_bb = ctx.new_bb().basic_block(Some("%then".into()));
        ctx.register_bb(then_bb);
        let else_bb = self.else_branch.as_ref().map(|_| {
            let bb = ctx.new_bb().basic_block(Some("%else".into()));
            ctx.register_bb(bb);
            bb
        });
        let end_bb = ctx.new_bb().basic_block(Some("%end".into()));
        ctx.register_bb(end_bb);
        let br = ctx
            .new_local_value()
            .branch(cond_val, then_bb, else_bb.unwrap_or(end_bb));
        ctx.push_inst(br);

        ctx.set_curr_bb(then_bb);
        self.then_branch.convert(ctx)?;
        let then_jump = ctx.new_local_value().jump(end_bb);
        ctx.push_inst(then_jump);

        if let Some(else_bb) = else_bb {
            ctx.set_curr_bb(else_bb);
            self.else_branch.as_ref().unwrap().convert(ctx)?;
            let else_jump = ctx.new_local_value().jump(end_bb);
            ctx.push_inst(else_jump);
        }

        ctx.set_curr_bb(end_bb);
        Ok(())
    }

    fn global_convert(&self, _ctx: &mut AstGenContext) -> Result<()> {
        unreachable!("No corresponding syntax")
    }
}

impl ToKoopaIR for item::AssignStmt {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        if ctx.is_constant(&self.l_val) {
            bail!("Can't modify a constant");
        }
        self.l_val.convert(ctx)?;
        let lhs_l_val = ctx.pop_val().unwrap();
        self.exp.convert(ctx)?;
        let rhs_exp = ctx.pop_val().unwrap();

        // Compile time type-check.
        let lhs_ptr_type = ctx.new_local_value().value_type(lhs_l_val);
        let rhs_exp_type = ctx.new_local_value().value_type(rhs_exp);
        ensure!(
            Type::get_pointer(rhs_exp_type.clone()) == lhs_ptr_type.clone(),
            "Type not match. {rhs_exp_type} can't store in {lhs_ptr_type}"
        );
        let store = ctx.new_local_value().store(rhs_exp, lhs_l_val);
        ctx.push_inst(store);
        Ok(())
    }

    fn global_convert(&self, _ctx: &mut AstGenContext) -> Result<()> {
        unreachable!("No corresponding syntax")
    }
}

impl ToKoopaIR for item::Exp {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.lor_exp.convert(ctx)
    }

    #[inline]
    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.lor_exp.global_convert(ctx)
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
                let zero = ctx.new_local_value().integer(0);
                let lhs_ne_0 = ctx.new_local_value().binary(BinaryOp::NotEq, lhs, zero);
                ctx.push_inst(lhs_ne_0);

                // two basic block for short circuit logic
                let rhs_bb = ctx.new_bb().basic_block(Some("%lor_rhs".into()));
                ctx.register_bb(rhs_bb);
                let merge_bb = ctx
                    .new_bb()
                    .basic_block_with_params(Some("%lor_merge".into()), vec![Type::get_i32()]);
                ctx.register_bb(merge_bb);

                // short circuit logic
                let br = ctx.new_local_value().branch_with_args(
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
                let rhs_ne_0 = ctx.new_local_value().binary(BinaryOp::NotEq, rhs, zero);
                ctx.push_inst(rhs_ne_0);

                // jump to the merge block and pass the information
                let jump = ctx
                    .new_local_value()
                    .jump_with_args(merge_bb, vec![rhs_ne_0]);
                ctx.push_inst(jump);

                ctx.set_curr_bb(merge_bb);
                let result = ctx.bb_params(merge_bb)[0];
                ctx.push_val(result);
            }
        }
        Ok(())
    }

    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::LOrExp::LAndExp(land_exp) => land_exp.global_convert(ctx)?,
            item::LOrExp::Comp(lor_exp, land_exp) => {
                lor_exp.global_convert(ctx)?;
                let lhs_val = ctx.pop_val().unwrap();
                let lhs_int = ctx.get_global_val(lhs_val).unwrap();
                land_exp.global_convert(ctx)?;
                let rhs_val = ctx.pop_val().unwrap();
                let rhs_int = ctx.get_global_val(rhs_val).unwrap();
                let or_result = ctx
                    .program
                    .new_value()
                    .integer((lhs_int != 0 || rhs_int != 0) as i32);
                ctx.push_val(or_result);
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
                let zero = ctx.new_local_value().integer(0);
                let lhs_eq_0 = ctx.new_local_value().binary(BinaryOp::Eq, lhs, zero);
                ctx.push_inst(lhs_eq_0);

                // two basic block for short circuit logic
                let rhs_bb = ctx.new_bb().basic_block(Some("%land_rhs".into()));
                ctx.register_bb(rhs_bb);
                let merge_bb = ctx
                    .new_bb()
                    .basic_block_with_params(Some("%land_merge".into()), vec![Type::get_i32()]);
                ctx.register_bb(merge_bb);

                //short circuit logic
                let br = ctx.new_local_value().branch_with_args(
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
                let rhs_ne_0 = ctx.new_local_value().binary(BinaryOp::NotEq, rhs, zero);
                ctx.push_inst(rhs_ne_0);

                // jump to merge block and pass the information
                let jump = ctx
                    .new_local_value()
                    .jump_with_args(merge_bb, vec![rhs_ne_0]);
                ctx.push_inst(jump);

                ctx.set_curr_bb(merge_bb);
                let result = ctx.bb_params(merge_bb)[0];
                ctx.push_val(result);
            }
        }
        Ok(())
    }

    #[inline]
    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::LAndExp::EqExp(eq_exp) => eq_exp.global_convert(ctx)?,
            item::LAndExp::Comp(land_exp, eq_exp) => {
                land_exp.global_convert(ctx)?;
                let lhs_val = ctx.pop_val().unwrap();
                let lhs_int = ctx.get_global_val(lhs_val).unwrap();
                eq_exp.global_convert(ctx)?;
                let rhs_val = ctx.pop_val().unwrap();
                let rhs_int = ctx.get_global_val(rhs_val).unwrap();
                let and_result = ctx
                    .program
                    .new_value()
                    .integer((lhs_int != 0 && rhs_int != 0) as i32);
                ctx.push_val(and_result);
            }
        }
        Ok(())
    }
}

impl ToKoopaIR for item::EqExp {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::EqExp::RelExp(rel_exp) => rel_exp.convert(ctx),
            item::EqExp::Comp(lhs_eq, op, rhs_rel) => {
                lhs_eq.convert(ctx)?;
                rhs_rel.convert(ctx)?;
                op.convert(ctx)
            }
        }
    }

    #[inline]
    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::EqExp::RelExp(rel_exp) => rel_exp.global_convert(ctx),
            item::EqExp::Comp(eq_exp, binary_op, rel_exp) => {
                eq_exp.global_convert(ctx)?;
                rel_exp.global_convert(ctx)?;
                binary_op.global_convert(ctx)
            }
        }
    }
}

impl ToKoopaIR for item::RelExp {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::RelExp::AddExp(add_exp) => add_exp.convert(ctx),
            item::RelExp::Comp(lhs_rel, op, rhs_add) => {
                lhs_rel.convert(ctx)?;
                rhs_add.convert(ctx)?;
                op.convert(ctx)
            }
        }
    }

    #[inline]
    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::RelExp::AddExp(add_exp) => add_exp.global_convert(ctx),
            item::RelExp::Comp(rel_exp, binary_op, add_exp) => {
                rel_exp.global_convert(ctx)?;
                add_exp.global_convert(ctx)?;
                binary_op.global_convert(ctx)
            }
        }
    }
}

impl ToKoopaIR for item::AddExp {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::AddExp::MulExp(mul_exp) => mul_exp.convert(ctx),
            item::AddExp::Comp(lhs_add, op, rhs_mul) => {
                lhs_add.convert(ctx)?;
                rhs_mul.convert(ctx)?;
                op.convert(ctx)
            }
        }
    }

    #[inline]
    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::AddExp::MulExp(mul_exp) => mul_exp.global_convert(ctx),
            item::AddExp::Comp(add_exp, binary_op, mul_exp) => {
                add_exp.global_convert(ctx)?;
                mul_exp.global_convert(ctx)?;
                binary_op.global_convert(ctx)
            }
        }
    }
}

impl ToKoopaIR for item::MulExp {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::MulExp::UnaryExp(unary_exp) => unary_exp.convert(ctx),
            item::MulExp::Comp(lhs_mul, op, rhs_unary) => {
                lhs_mul.convert(ctx)?;
                rhs_unary.convert(ctx)?;
                op.convert(ctx)
            }
        }
    }

    #[inline]
    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::MulExp::UnaryExp(unary_exp) => unary_exp.global_convert(ctx),
            item::MulExp::Comp(mul_exp, binary_op, unary_exp) => {
                mul_exp.global_convert(ctx)?;
                unary_exp.global_convert(ctx)?;
                binary_op.global_convert(ctx)
            }
        }
    }
}

impl ToKoopaIR for item::UnaryExp {
    #[inline]
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::UnaryExp::PrimaryExp(exp) => exp.convert(ctx),
            item::UnaryExp::Unary(unary_op, unary_exp) => {
                unary_exp.convert(ctx)?;
                unary_op.convert(ctx)
            }
            item::UnaryExp::FuncCall(func_call) => func_call.convert(ctx),
        }
    }

    #[inline]
    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::UnaryExp::PrimaryExp(primary_exp) => primary_exp.global_convert(ctx),
            item::UnaryExp::Unary(unary_op, unary_exp) => {
                unary_exp.global_convert(ctx)?;
                unary_op.global_convert(ctx)
            }
            item::UnaryExp::FuncCall(_) => bail!("Const function is not supported"),
        }
    }
}

impl ToKoopaIR for item::FuncCall {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        self.args
            .iter()
            .rev()
            .try_for_each(|exp| exp.convert(ctx))?;
        let args = (0..self.args.len())
            .map(|_| ctx.pop_val().unwrap())
            .rev()
            .collect::<Vec<_>>();
        let Symbol::Callable(target_func) = ctx
            .get_global(&self.ident)
            .context(format!("Can't find function {}", &*self.ident))?
        else {
            bail!("Not a function {}", &*self.ident)
        };
        let call = ctx.new_local_value().call(target_func, args);
        ctx.push_inst(call);
        if !ctx.curr_func_data().dfg().value(call).ty().is_unit() {
            ctx.push_val(call);
        }
        Ok(())
    }

    fn global_convert(&self, _ctx: &mut AstGenContext) -> Result<()> {
        unreachable!("No corresponding syntax")
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
                    Symbol::Constant(const_val) => {
                        let ValueKind::Integer(i) = ctx.get_val_kind(const_val) else {
                            bail!("Not a valid const val");
                        };
                        ctx.new_local_value().integer(i.value())
                    }
                    // If it's a variable, because we store the pointer so we load it and pull out.
                    Symbol::Variable(var_ptr) => {
                        let load = ctx.new_local_value().load(var_ptr);
                        ctx.push_inst(load);
                        load
                    }
                    Symbol::Callable(func_handle) => {
                        bail!("Cannot assign a value to a function {func_handle:?}")
                    }
                };
                ctx.push_val(val);
            }
        }
        Ok(())
    }

    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        match self {
            item::PrimaryExp::Exp(exp) => exp.global_convert(ctx)?,
            item::PrimaryExp::LVal(lval) => {
                let sym = ctx
                    .global_scope()
                    .get(&lval.ident)
                    .context(format!("{} not defined", &*lval.ident))?;
                let int = match sym {
                    Symbol::Constant(int) => {
                        let borrow_value = ctx.program.borrow_value(*int);
                        let ValueKind::Integer(int) = borrow_value.kind() else {
                            unreachable!();
                        };
                        int.value()
                    }
                    Symbol::Variable(var) => {
                        let borrow_value = ctx.program.borrow_value(*var);
                        let ValueKind::GlobalAlloc(glob_alloc) = borrow_value.kind() else {
                            unreachable!();
                        };
                        match ctx.program.borrow_value(glob_alloc.init()).kind() {
                            ValueKind::Integer(int) => int.value(),
                            ValueKind::ZeroInit(_) => 0,
                            _ => unreachable!(),
                        }
                    }
                    Symbol::Callable(_) => unreachable!(),
                };
                let val = ctx.new_global_value().integer(int);
                ctx.push_val(val);
            }
            item::PrimaryExp::Number(num) => {
                let num_lit = ctx.new_global_value().integer(*num);
                ctx.push_val(num_lit);
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
            Symbol::Constant(const_val) => const_val,
            Symbol::Variable(p_val) => p_val,
            Symbol::Callable(func_handle) => {
                bail!("Cannot assign a value to a function {func_handle:?}")
            }
        };
        ctx.push_val(val);
        Ok(())
    }

    fn global_convert(&self, _ctx: &mut AstGenContext) -> Result<()> {
        panic!("No corresponding syntax")
    }
}

impl ToKoopaIR for koopa::ir::BinaryOp {
    fn convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        let rhs = ctx.pop_val().unwrap();
        let lhs = ctx.pop_val().unwrap();

        // Constant folding
        if let ValueKind::Integer(int_lhs) = ctx.get_val_kind(lhs)
            && let ValueKind::Integer(int_rhs) = ctx.get_val_kind(rhs)
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
                        bail!("Division by zero");
                    } else {
                        int_lhs.wrapping_div(int_rhs)
                    }
                }
                BinaryOp::Mod => {
                    if int_rhs == 0 {
                        bail!("Modulo by zero");
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

            let val = ctx.new_local_value().integer(res);
            ctx.push_val(val);
            return Ok(());
        }

        let operation = ctx.new_local_value().binary(*self, lhs, rhs);
        ctx.push_val(operation);
        ctx.push_inst(operation);
        Ok(())
    }

    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        let rhs = ctx.pop_val().unwrap();
        let lhs = ctx.pop_val().unwrap();
        let res = if let ValueKind::Integer(lhs) = ctx.program.borrow_value(lhs).kind()
            && let ValueKind::Integer(rhs) = ctx.program.borrow_value(rhs).kind()
        {
            // let ValueKind::Integer(lhs) = ctx.program.borrow_value(lhs).clone().kind() else {
            //     unreachable!()
            // };
            // let ValueKind::Integer(rhs) = ctx.program.borrow_value(rhs).clone().kind() else {
            //     unreachable!()
            // };
            let int_lhs = lhs.value();
            let int_rhs = rhs.value();
            match self {
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
                        bail!("Division by zero");
                    } else {
                        int_lhs.wrapping_div(int_rhs)
                    }
                }
                BinaryOp::Mod => {
                    if int_rhs == 0 {
                        bail!("Modulo by zero");
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
            }
        } else {
            unreachable!()
        };
        let val = ctx.new_global_value().integer(res);
        ctx.push_val(val);
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
        if let ValueKind::Integer(integer) = rhs_val.kind().clone() {
            let operation = match self {
                item::UnaryOp::Add => unreachable!(),
                item::UnaryOp::Minus => ctx.new_local_value().integer(-integer.value()),
                item::UnaryOp::Negation => {
                    ctx.new_local_value().integer((integer.value() == 0) as _)
                }
            };
            ctx.push_val(operation);
            return Ok(());
        }

        let zero = ctx.new_local_value().integer(0);
        let operation = match self {
            item::UnaryOp::Add => unreachable!(),
            item::UnaryOp::Minus => ctx.new_local_value().binary(BinaryOp::Sub, zero, rhs),
            item::UnaryOp::Negation => ctx.new_local_value().binary(BinaryOp::Eq, zero, rhs),
        };
        ctx.push_val(operation);
        ctx.push_inst(operation);
        Ok(())
    }

    fn global_convert(&self, ctx: &mut AstGenContext) -> Result<()> {
        if matches!(self, item::UnaryOp::Add) {
            return Ok(());
        }
        let rhs = ctx.pop_val().unwrap();
        let res = if let ValueKind::Integer(int) = ctx.program.borrow_value(rhs).kind() {
            match self {
                item::UnaryOp::Add => unreachable!(),
                item::UnaryOp::Minus => -int.value(),
                item::UnaryOp::Negation => (int.value() == 0) as i32,
            }
        } else {
            unreachable!()
        };
        let val = ctx.new_global_value().integer(res);
        ctx.push_val(val);
        Ok(())
    }
}
