pub mod item {
    use koopa::ir::BinaryOp;

    #[derive(Debug)]
    pub struct CompUnit {
        pub func_def: FuncDef,
    }

    #[derive(Debug)]
    pub struct FuncDef {
        pub func_type: FuncType,
        pub ident: String,
        pub block: Block,
    }

    #[derive(Debug)]
    pub enum FuncType {
        Int,
    }

    #[derive(Debug)]
    pub struct Block {
        pub stmt: Stmt,
    }

    #[derive(Debug)]
    pub struct Stmt {
        pub exp: Exp,
    }

    #[derive(Debug)]
    pub struct Exp {
        pub lor_exp: LOrExp,
    }

    #[derive(Debug)]
    pub enum UnaryExp {
        PrimaryExp(Box<PrimaryExp>),
        Unary(UnaryOp, Box<UnaryExp>),
    }

    #[derive(Debug)]
    pub enum UnaryOp {
        Add,
        Minus,
        Negation,
    }

    #[derive(Debug)]
    pub enum PrimaryExp {
        Exp(Exp),
        Number(Number),
    }

    #[derive(Debug)]
    pub enum AddExp {
        MulExp(MulExp),
        Comp(Box<AddExp>, BinaryOp, MulExp),
    }

    #[derive(Debug)]
    pub enum MulExp {
        UnaryExp(UnaryExp),
        Comp(Box<MulExp>, BinaryOp, UnaryExp),
    }

    #[derive(Debug)]
    pub enum LOrExp {
        LAndExp(LAndExp),
        Comp(Box<LOrExp>, LAndExp),
    }

    #[derive(Debug)]
    pub enum LAndExp {
        EqExp(EqExp),
        Comp(Box<LAndExp>, EqExp),
    }

    #[derive(Debug)]
    pub enum EqExp {
        RelExp(RelExp),
        Comp(Box<EqExp>, BinaryOp, RelExp),
    }

    #[derive(Debug)]
    pub enum RelExp {
        AddExp(AddExp),
        Comp(Box<RelExp>, BinaryOp, AddExp),
    }

    pub type Number = i32;
}

use koopa::ir::{
    builder::{BlockBuilder, LocalBuilder},
    builder_traits::*,
    *,
};

impl item::FuncType {
    fn get_type(&self) -> Type {
        match self {
            item::FuncType::Int => Type::get_i32(),
        }
    }
}

pub struct AstGenContext {
    program: Program,
    func_stack: Vec<Function>,
    val_stack: Vec<Value>,
    curr_bb: Option<BasicBlock>,
}

pub trait Convert2Koopa {
    fn convert(&self, ctx: &mut AstGenContext);
}

impl AstGenContext {
    pub fn new() -> AstGenContext {
        AstGenContext {
            program: Program::new(),
            func_stack: Vec::new(),
            val_stack: Vec::new(),
            curr_bb: None,
        }
    }

    #[inline]
    pub fn end(self) -> Program {
        self.program
    }

    #[inline]
    fn curr_func_data_mut(&mut self) -> &mut FunctionData {
        self.program.func_mut(*self.func_stack.last().unwrap())
    }

    #[inline]
    fn curr_func_data(&self) -> &FunctionData {
        self.program.func(*self.func_stack.last().unwrap())
    }

    fn push_inst(&mut self, val: Value) {
        let curr_basic_block = self.curr_bb.unwrap();
        self.curr_func_data_mut()
            .layout_mut()
            .bb_mut(curr_basic_block)
            .insts_mut()
            .push_key_back(val)
            .unwrap();
    }

    #[inline]
    fn push_val(&mut self, val: Value) {
        self.val_stack.push(val);
    }

    #[inline]
    fn pop_val(&mut self) -> Option<Value> {
        self.val_stack.pop()
    }

    #[inline]
    fn peek_val(&self) -> Option<&Value> {
        self.val_stack.last()
    }

    #[inline]
    fn new_bb(&mut self) -> BlockBuilder<'_> {
        self.curr_func_data_mut().dfg_mut().new_bb()
    }

    fn register_bb(&mut self, bb: BasicBlock) {
        self.curr_func_data_mut()
            .layout_mut()
            .bbs_mut()
            .push_key_back(bb)
            .unwrap()
    }

    #[inline]
    fn new_value(&mut self) -> LocalBuilder<'_> {
        self.curr_func_data_mut().dfg_mut().new_value()
    }

    #[inline]
    fn set_curr_bb(&mut self, bb: BasicBlock) -> Option<BasicBlock> {
        self.curr_bb.replace(bb)
    }

    #[inline]
    fn reset_bb(&mut self, bb: Option<BasicBlock>) {
        self.curr_bb = bb
    }

    #[inline]
    fn bb_params(&mut self, bb: BasicBlock) -> &[Value] {
        self.curr_func_data_mut().dfg().bb(bb).params()
    }
}

impl Convert2Koopa for item::CompUnit {
    fn convert(&self, ctx: &mut AstGenContext) {
        self.func_def.convert(ctx);
    }
}

impl Convert2Koopa for item::FuncDef {
    fn convert(&self, ctx: &mut AstGenContext) {
        let func = ctx.program.new_func(FunctionData::new(
            format!("@{}", self.ident),
            vec![],
            self.func_type.get_type(),
        ));
        ctx.func_stack.push(func);
        let func_data = ctx.curr_func_data_mut();
        let bb = func_data
            .dfg_mut()
            .new_bb()
            .basic_block(Some("%entry".into()));
        func_data.layout_mut().bbs_mut().push_key_back(bb).unwrap();
        let prev_bb = ctx.curr_bb.replace(bb);
        self.block.convert(ctx);
        ctx.func_stack.pop();
        ctx.curr_bb = prev_bb;
    }
}

impl Convert2Koopa for item::Block {
    fn convert(&self, ctx: &mut AstGenContext) {
        self.stmt.convert(ctx);
    }
}

impl Convert2Koopa for item::Stmt {
    fn convert(&self, ctx: &mut AstGenContext) {
        // let func_data = ctx.program.func_mut(*ctx.func_stack.last().unwrap());
        self.exp.convert(ctx);
        let v_ret = ctx.pop_val();
        let func_data = ctx.curr_func_data_mut();
        let ret = func_data.dfg_mut().new_value().ret(v_ret);
        ctx.push_inst(ret);
    }
}

impl Convert2Koopa for item::Exp {
    fn convert(&self, ctx: &mut AstGenContext) {
        self.lor_exp.convert(ctx);
    }
}

impl Convert2Koopa for item::LOrExp {
    fn convert(&self, ctx: &mut AstGenContext) {
        match self {
            item::LOrExp::LAndExp(land_exp) => land_exp.convert(ctx),
            item::LOrExp::Comp(lor_exp, land_exp) => {
                // handle lhs
                lor_exp.convert(ctx);
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
                ctx.set_curr_bb(rhs_bb);
                land_exp.convert(ctx);
                let rhs = ctx.pop_val().unwrap();
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
    }
}

impl Convert2Koopa for item::LAndExp {
    fn convert(&self, ctx: &mut AstGenContext) {
        match self {
            item::LAndExp::EqExp(eq_exp) => eq_exp.convert(ctx),
            item::LAndExp::Comp(land_exp, eq_exp) => {
                // handle lhs
                land_exp.convert(ctx);
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
                ctx.set_curr_bb(rhs_bb);
                eq_exp.convert(ctx);
                let rhs = ctx.pop_val().unwrap();
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
    }
}

impl Convert2Koopa for item::EqExp {
    fn convert(&self, ctx: &mut AstGenContext) {
        match self {
            item::EqExp::RelExp(rel_exp) => rel_exp.convert(ctx),
            item::EqExp::Comp(lhs_eq, op, rhs_rel) => {
                lhs_eq.convert(ctx);
                rhs_rel.convert(ctx);
                assert!(matches!(*op, BinaryOp::Eq | BinaryOp::NotEq));
                op.convert(ctx);
            }
        }
    }
}

impl Convert2Koopa for item::RelExp {
    fn convert(&self, ctx: &mut AstGenContext) {
        match self {
            item::RelExp::AddExp(add_exp) => add_exp.convert(ctx),
            item::RelExp::Comp(lhs_rel, op, rhs_add) => {
                lhs_rel.convert(ctx);
                rhs_add.convert(ctx);
                assert!(matches!(
                    *op,
                    BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge
                ));
                op.convert(ctx);
            }
        }
    }
}

impl Convert2Koopa for item::AddExp {
    fn convert(&self, ctx: &mut AstGenContext) {
        match self {
            item::AddExp::MulExp(mul_exp) => mul_exp.convert(ctx),
            item::AddExp::Comp(lhs_add, op, rhs_mul) => {
                lhs_add.convert(ctx);
                rhs_mul.convert(ctx);
                assert!(matches!(*op, BinaryOp::Sub | BinaryOp::Add));
                op.convert(ctx);
            }
        }
    }
}

impl Convert2Koopa for item::MulExp {
    fn convert(&self, ctx: &mut AstGenContext) {
        match self {
            item::MulExp::UnaryExp(unary_exp) => unary_exp.convert(ctx),
            item::MulExp::Comp(lhs_mul, op, rhs_unary) => {
                lhs_mul.convert(ctx);
                rhs_unary.convert(ctx);
                assert!(matches!(*op, BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod));
                op.convert(ctx);
            }
        }
    }
}

impl Convert2Koopa for item::UnaryExp {
    fn convert(&self, ctx: &mut AstGenContext) {
        match self {
            item::UnaryExp::PrimaryExp(exp) => exp.convert(ctx),
            item::UnaryExp::Unary(unary_op, unary_exp) => {
                unary_exp.convert(ctx);
                unary_op.convert(ctx);
            }
        }
    }
}

impl Convert2Koopa for item::PrimaryExp {
    /// Grammar:
    /// PrimaryExp ::= "(" Exp ")" | Number;
    fn convert(&self, ctx: &mut AstGenContext) {
        match self {
            item::PrimaryExp::Exp(exp) => exp.convert(ctx),
            item::PrimaryExp::Number(num) => {
                let func_data = ctx.curr_func_data_mut();
                let num = func_data.dfg_mut().new_value().integer(*num);
                ctx.val_stack.push(num);
            }
        }
    }
}

impl Convert2Koopa for koopa::ir::BinaryOp {
    /// Assure you will call a binary operation or otherwise use crate::ast::item::UnaryOp
    ///
    /// General method to use two value to generate a value and an instruction.
    /// WARNING: Check the limitaion of binary operator before the call.
    /// Example:
    ///
    ///```
    /// impl Convert2Koopa for item::MulExp {
    ///     fn convert(&self, ctx: &mut AstGenContext) {
    ///         match self {
    ///             item::MulExp::UnaryExp(unary_exp) => unary_exp.convert(ctx),
    ///             item::MulExp::Comp(lhs_mul, op, rhs_unary) => {
    ///                 lhs_mul.convert(ctx);
    ///                 rhs_unary.convert(ctx);
    ///                 // assertion
    ///                 assert!(matches!(*op, BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod));
    ///                 op.convert(ctx);
    ///             }
    ///         }
    ///     }
    /// }
    /// ```
    fn convert(&self, ctx: &mut AstGenContext) {
        let rhs = ctx.pop_val().unwrap();
        let lhs = ctx.pop_val().unwrap();

        // Constant folding
        if let ValueKind::Integer(int_lhs) = ctx.curr_func_data().dfg().value(lhs).kind()
            && let ValueKind::Integer(int_rhs) = ctx.curr_func_data().dfg().value(rhs).kind()
        {
            let int_lhs = int_lhs.value();
            let int_rhs = int_rhs.value();
            let result = match self {
                BinaryOp::NotEq => Some((int_lhs != int_rhs) as i32),
                BinaryOp::Eq => Some((int_lhs == int_rhs) as i32),
                BinaryOp::Gt => Some((int_lhs > int_rhs) as i32),
                BinaryOp::Lt => Some((int_lhs < int_rhs) as i32),
                BinaryOp::Ge => Some((int_lhs >= int_rhs) as i32),
                BinaryOp::Le => Some((int_lhs <= int_rhs) as i32),
                BinaryOp::Add => Some(int_lhs.wrapping_add(int_rhs)),
                BinaryOp::Sub => Some(int_lhs.wrapping_sub(int_rhs)),
                BinaryOp::Mul => Some(int_lhs.wrapping_mul(int_rhs)),
                BinaryOp::Div => {
                    if int_rhs == 0 {
                        None
                    } else {
                        Some(int_lhs.wrapping_div(int_rhs))
                    }
                }
                BinaryOp::Mod => {
                    if int_rhs == 0 {
                        None
                    } else {
                        Some(int_lhs.wrapping_rem(int_rhs))
                    }
                }
                BinaryOp::And => Some(int_lhs & int_rhs),
                BinaryOp::Or => Some(int_lhs | int_rhs),
                BinaryOp::Xor => Some(int_lhs ^ int_rhs),
                BinaryOp::Shl => Some(int_lhs.wrapping_shl(int_rhs as u32)),
                BinaryOp::Shr => Some((int_lhs as u32).wrapping_shr(int_rhs as u32) as i32),
                BinaryOp::Sar => Some(int_lhs.wrapping_shr(int_rhs as u32)),
            };

            if let Some(res) = result {
                let val = ctx.new_value().integer(res);
                ctx.push_val(val);
                return;
            }
        }

        let func_data = ctx.curr_func_data_mut();
        let operation = func_data.dfg_mut().new_value().binary(*self, lhs, rhs);
        ctx.push_val(operation);
        ctx.push_inst(operation);
    }
}

impl Convert2Koopa for item::UnaryOp {
    fn convert(&self, ctx: &mut AstGenContext) {
        // if `+` is unary then it will do nothing.
        if matches!(self, item::UnaryOp::Add) {
            return;
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
            return;
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
    }
}

// pub fn convert() {
//     let mut program = Program::new();
//
//     let main = program.new_func(FunctionData::new("@main".into(), vec![], Type::get_i32()));
//     let main_data = program.func_mut(main);
//
//     let bb = main_data.dfg_mut().new_bb().basic_block(None);
//     main_data.layout_mut().bbs_mut().push_key_back(bb).unwrap();
//
//     let lhs = main_data.dfg_mut().new_value().integer(31);
//     let rhs = main_data.dfg_mut().new_value().integer(11);
//     let add = main_data
//         .dfg_mut()
//         .new_value()
//         .binary(BinaryOp::Add, lhs, rhs);
//     let ret = main_data.dfg_mut().new_value().ret(Some(add));
//     main_data
//         .layout_mut()
//         .bb_mut(bb)
//         .insts_mut()
//         .extend([add, ret]);
//
//     let mut g = KoopaGenerator::new(Vec::new());
//     g.generate_on(&program).unwrap();
//     let text_from_ir = std::str::from_utf8(&g.writer()).unwrap().to_string();
//     println!("{text_from_ir}");
// }
