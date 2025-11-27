#[allow(unused)]
pub mod item {
    use super::Ident;
    use koopa::ir::BinaryOp;

    /// CompUnit ::= FuncDef;
    ///
    /// The root of the AST, representing a complete compilation unit.
    #[derive(Debug)]
    pub struct CompUnit {
        pub func_def: FuncDef,
    }

    /// FuncDef ::= FuncType IDENT "(" ")" Block;
    ///
    /// A function definition with return type, name, and body.
    #[derive(Debug)]
    pub struct FuncDef {
        pub func_type: FuncType,
        pub ident: Ident,
        pub block: Block,
    }

    /// FuncType ::= "int";
    ///
    /// The return type of a function.
    #[derive(Debug)]
    pub enum FuncType {
        Int,
    }

    /// Block ::= "{" {BlockItem} "}";
    ///
    /// A block containing zero or more block items.
    #[derive(Debug)]
    pub struct Block {
        pub block_items: Vec<BlockItem>,
    }

    /// BlockItem ::= Decl | Stmt;
    ///
    /// An item within a block, either a declaration or a statement.
    #[derive(Debug)]
    pub enum BlockItem {
        Decl(Decl),
        Stmt(Stmt),
    }

    /// Decl ::= ConstDecl | VarDecl;
    ///
    /// A declaration, either constant or variable.
    #[derive(Debug)]
    pub enum Decl {
        ConstDecl(ConstDecl),
        VarDecl(VarDecl),
    }

    /// ConstDecl ::= "const" BType ConstDef {"," ConstDef} ";";
    ///
    /// A constant declaration with base type and one or more constant definitions.
    #[derive(Debug)]
    pub struct ConstDecl {
        pub btype: BType,
        pub const_defs: Vec<ConstDef>,
    }

    /// BType ::= "int";
    ///
    /// The base type for variables and constants.
    #[derive(Debug)]
    pub enum BType {
        Int,
    }

    /// ConstDef ::= IDENT "=" ConstInitVal;
    ///
    /// A constant definition with identifier and initial value.
    #[derive(Debug)]
    pub struct ConstDef {
        pub ident: Ident,
        pub const_init_val: ConstInitVal,
    }

    /// ConstInitVal ::= ConstExp;
    ///
    /// The initial value of a constant.
    #[derive(Debug)]
    pub struct ConstInitVal {
        pub const_exp: ConstExp,
    }

    /// VarDecl ::= BType VarDef {"," VarDef} ";";
    ///
    /// A variable declaration with base type and one or more variable definitions.
    #[derive(Debug)]
    pub struct VarDecl {
        pub btype: BType,
        pub var_defs: Vec<VarDef>,
    }

    /// VarDef ::= IDENT | IDENT "=" InitVal;
    ///
    /// A variable definition with identifier and optional initial value.
    #[derive(Debug)]
    pub struct VarDef {
        pub ident: Ident,
        pub init_val: Option<InitVal>,
    }

    /// InitVal ::= Exp;
    ///
    /// The initial value of a variable.
    #[derive(Debug)]
    pub struct InitVal {
        pub exp: Exp,
    }

    /// Stmt ::= LVal "=" Exp ";" | "return" Exp ";";
    ///
    /// A statement, either an assignment or a return statement.
    #[derive(Debug)]
    pub enum Stmt {
        Assign(LVal, Exp),
        Return(Exp),
    }

    /// Exp ::= LOrExp;
    ///
    /// An expression, starting from logical OR expressions.
    #[derive(Debug)]
    pub struct Exp {
        pub lor_exp: LOrExp,
    }

    /// LVal ::= IDENT;
    ///
    /// A left-value, representing a variable that can be assigned to.
    #[derive(Debug)]
    pub struct LVal {
        pub ident: Ident,
    }

    /// ConstExp ::= Exp;
    ///
    /// A constant expression, must be evaluable at compile time.
    #[derive(Debug)]
    pub struct ConstExp {
        pub exp: Exp,
    }

    /// UnaryExp ::= PrimaryExp | UnaryOp UnaryExp;
    ///
    /// A unary expression, either a primary expression or a unary operation applied to another unary expression.
    #[derive(Debug)]
    pub enum UnaryExp {
        PrimaryExp(Box<PrimaryExp>),
        Unary(UnaryOp, Box<UnaryExp>),
    }

    /// UnaryOp ::= "+" | "-" | "!";
    ///
    /// A unary operator: positive, negative, or logical negation.
    #[derive(Debug)]
    pub enum UnaryOp {
        Add,
        Minus,
        Negation,
    }

    /// PrimaryExp ::= "(" Exp ")" | LVal | Number;
    ///
    /// A primary expression: parenthesized expression, left-value, or number literal.
    #[derive(Debug)]
    pub enum PrimaryExp {
        Exp(Exp),
        LVal(LVal),
        Number(Number),
    }

    /// AddExp ::= MulExp | AddExp ("+" | "-") MulExp;
    ///
    /// An additive expression with addition or subtraction.
    #[derive(Debug)]
    pub enum AddExp {
        MulExp(MulExp),
        Comp(Box<AddExp>, BinaryOp, MulExp),
    }

    /// MulExp ::= UnaryExp | MulExp ("*" | "/" | "%") UnaryExp;
    ///
    /// A multiplicative expression with multiplication, division, or modulo.
    #[derive(Debug)]
    pub enum MulExp {
        UnaryExp(UnaryExp),
        Comp(Box<MulExp>, BinaryOp, UnaryExp),
    }

    /// LOrExp ::= LAndExp | LOrExp "||" LAndExp;
    ///
    /// A logical OR expression with short-circuit evaluation.
    #[derive(Debug)]
    pub enum LOrExp {
        LAndExp(LAndExp),
        Comp(Box<LOrExp>, LAndExp),
    }

    /// LAndExp ::= EqExp | LAndExp "&&" EqExp;
    ///
    /// A logical AND expression with short-circuit evaluation.
    #[derive(Debug)]
    pub enum LAndExp {
        EqExp(EqExp),
        Comp(Box<LAndExp>, EqExp),
    }

    /// EqExp ::= RelExp | EqExp ("==" | "!=") RelExp;
    ///
    /// An equality expression with equal or not-equal comparison.
    #[derive(Debug)]
    pub enum EqExp {
        RelExp(RelExp),
        Comp(Box<EqExp>, BinaryOp, RelExp),
    }

    /// RelExp ::= AddExp | RelExp ("<" | ">" | "<=" | ">=") AddExp;
    ///
    /// A relational expression with comparison operators.
    #[derive(Debug)]
    pub enum RelExp {
        AddExp(AddExp),
        Comp(Box<RelExp>, BinaryOp, AddExp),
    }

    /// Number ::= INT_CONST;
    ///
    /// An integer constant literal.
    pub type Number = i32;
}

use koopa::ir::{builder::*, *};
use std::collections::{
    HashMap,
    hash_map::Entry::{Occupied, Vacant},
};

pub type Ident = std::rc::Rc<str>;
pub type ConstantType = i32;
pub type VariableType = Value;

pub enum Symbol {
    Constant(ConstantType),
    Variable(Value),
}

pub struct AstGenContext {
    pub program: Program,
    func_stack: Vec<Function>,
    val_stack: Vec<Value>,
    curr_bb: Option<BasicBlock>,
    symbol_table: HashMap<Ident, Symbol>,
}

impl AstGenContext {
    pub fn new() -> AstGenContext {
        AstGenContext {
            program: Program::new(),
            func_stack: Vec::new(),
            val_stack: Vec::new(),
            curr_bb: None,
            symbol_table: HashMap::new(),
        }
    }

    /// Insert a identifier-value pair to a table.
    ///
    /// Panic: when redefine a variable.
    #[inline]
    pub fn insert_const(&mut self, ident: Ident, val: i32) -> Result<(), ()> {
        match self.symbol_table.entry(ident) {
            Occupied(_) => Err(()),
            Vacant(e) => {
                e.insert(Symbol::Constant(val));
                Ok(())
            }
        }
    }

    pub fn get_const(&self, ident: &Ident) -> Option<ConstantType> {
        match self.symbol_table.get(ident) {
            Some(Symbol::Constant(ret)) => Some(*ret),
            _ => None,
        }
    }

    #[inline]
    pub fn push_func(&mut self, func: Function) {
        self.func_stack.push(func);
    }

    #[inline]
    pub fn pop_func(&mut self) -> Option<Function> {
        self.func_stack.pop()
    }

    #[inline]
    pub fn end(self) -> Program {
        self.program
    }

    #[inline]
    pub fn curr_func_data_mut(&mut self) -> &mut FunctionData {
        self.program.func_mut(*self.func_stack.last().unwrap())
    }

    #[inline]
    pub fn curr_func_data(&self) -> &FunctionData {
        self.program.func(*self.func_stack.last().unwrap())
    }

    #[inline]
    pub fn push_inst(&mut self, val: Value) {
        let curr_basic_block = self.curr_bb.unwrap();
        self.curr_func_data_mut()
            .layout_mut()
            .bb_mut(curr_basic_block)
            .insts_mut()
            .push_key_back(val)
            .unwrap();
    }

    pub fn remove_inst(&mut self, val: Value) -> Option<(Value, layout::InstNode)> {
        let curr_basic_blcok = self.curr_bb.unwrap();
        self.curr_func_data_mut()
            .layout_mut()
            .bb_mut(curr_basic_blcok)
            .insts_mut()
            .remove(&val)
    }

    #[inline]
    pub fn push_val(&mut self, val: Value) {
        self.val_stack.push(val);
    }

    #[inline]
    pub fn pop_val(&mut self) -> Option<Value> {
        self.val_stack.pop()
    }

    // #[inline]
    // fn peek_val(&self) -> Option<&Value> {
    //     self.val_stack.last()
    // }

    #[must_use]
    #[inline]
    pub fn new_bb(&mut self) -> BlockBuilder<'_> {
        self.curr_func_data_mut().dfg_mut().new_bb()
    }

    pub fn register_bb(&mut self, bb: BasicBlock) {
        self.curr_func_data_mut()
            .layout_mut()
            .bbs_mut()
            .push_key_back(bb)
            .unwrap()
    }

    pub fn remove_bb(&mut self, bb: BasicBlock) -> Option<(BasicBlock, layout::BasicBlockNode)> {
        self.curr_func_data_mut().layout_mut().bbs_mut().remove(&bb)
    }

    #[must_use]
    #[inline]
    pub fn new_value(&mut self) -> LocalBuilder<'_> {
        self.curr_func_data_mut().dfg_mut().new_value()
    }

    #[inline]
    pub fn set_curr_bb(&mut self, bb: BasicBlock) -> Option<BasicBlock> {
        self.curr_bb.replace(bb)
    }

    #[inline]
    pub fn reset_bb(&mut self, bb: Option<BasicBlock>) {
        self.curr_bb = bb
    }

    #[inline]
    pub fn bb_params(&mut self, bb: BasicBlock) -> &[Value] {
        self.curr_func_data_mut().dfg().bb(bb).params()
    }
}
