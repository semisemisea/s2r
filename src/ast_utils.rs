#[allow(unused)]
pub mod item {
    use super::Ident;
    use koopa::ir::{BinaryOp, Type};

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
    pub type FuncType = Type;

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
    pub type BType = Type;

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
        Assign(AssignStmt),
        Block(Block),
        Single(Option<Exp>),
        Return(ReturnStmt),
        IfStmt(IfStmt),
        WhileStmt(WhileStmt),
        Break(Break),
        Continue(Continue),
    }

    #[derive(Debug)]
    pub struct Break;

    #[derive(Debug)]
    pub struct Continue;

    #[derive(Debug)]
    pub struct ReturnStmt {
        pub exp: Option<Exp>,
    }

    #[derive(Debug)]
    pub struct AssignStmt {
        pub l_val: LVal,
        pub exp: Exp,
    }

    #[derive(Debug)]
    pub struct IfStmt {
        pub cond: Exp,
        pub then_branch: Box<Stmt>,
        pub else_branch: Option<Box<Stmt>>,
    }

    #[derive(Debug)]
    pub struct WhileStmt {
        pub cond: Exp,
        pub body: Box<Stmt>,
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

use anyhow::{Result, anyhow};
use item::*;
use koopa::ir::{builder::*, *};
use std::collections::{
    HashMap,
    hash_map::Entry::{Occupied, Vacant},
};

pub type Ident = std::rc::Rc<str>;

#[derive(Debug, Clone, Copy)]
pub enum Symbol {
    Constant(Value),
    Variable(Value),
}

pub type SymbolTable = HashMap<Ident, Symbol>;

pub struct AstGenContext {
    pub program: Program,
    func_stack: Vec<Function>,
    val_stack: Vec<Value>,
    curr_bb: Option<BasicBlock>,
    symbol_table: Vec<SymbolTable>,
    def_type: Option<Type>,
    loop_stack: Vec<(BasicBlock, BasicBlock)>,
}

impl AstGenContext {
    pub fn new() -> AstGenContext {
        AstGenContext {
            program: Program::new(),
            func_stack: Vec::new(),
            val_stack: Vec::new(),
            curr_bb: None,
            symbol_table: Vec::new(),
            def_type: None,
            loop_stack: Vec::new(),
        }
    }

    pub fn push_loop(&mut self, entry_bb: BasicBlock, end_bb: BasicBlock) {
        self.loop_stack.push((entry_bb, end_bb));
    }

    pub fn pop_loop(&mut self) {
        self.loop_stack.pop();
    }

    pub fn curr_loop(&self) -> Option<(BasicBlock, BasicBlock)> {
        self.loop_stack.last().copied()
    }

    pub fn add_entry_bb(&mut self) -> BasicBlock {
        let func_data = self.curr_func_data_mut();
        let entry_bb = func_data
            .dfg_mut()
            .new_bb()
            .basic_block(Some("%entry".into()));
        func_data
            .layout_mut()
            .bbs_mut()
            .push_key_back(entry_bb)
            .unwrap();
        entry_bb
    }

    pub fn add_scope(&mut self) {
        self.symbol_table.push(HashMap::new());
    }

    pub fn del_scope(&mut self) {
        self.symbol_table.pop();
    }

    pub fn curr_scope(&self) -> &SymbolTable {
        self.symbol_table.last().unwrap()
    }

    pub fn curr_scope_mut(&mut self) -> &mut SymbolTable {
        self.symbol_table.last_mut().unwrap()
    }

    #[inline]
    pub fn insert_const(&mut self, ident: Ident, val: Value) -> Result<()> {
        match self.curr_scope_mut().entry(ident.clone()) {
            Occupied(_) => Err(anyhow!("Redefine the constant {}", &*ident)),
            Vacant(e) => {
                e.insert(Symbol::Constant(val));
                Ok(())
            }
        }
    }

    #[inline]
    pub fn insert_var(&mut self, ident: Ident, val: Value) -> Result<()> {
        match self.curr_scope_mut().entry(ident.clone()) {
            Occupied(_) => Err(anyhow!("Redefine the variable {}", &*ident)),
            Vacant(e) => {
                e.insert(Symbol::Variable(val));
                Ok(())
            }
        }
    }

    #[inline]
    pub fn get_symbol(&self, ident: &Ident) -> Option<Symbol> {
        // self.curr_scope().get(ident).copied()
        self.symbol_table
            .iter()
            .rev()
            .find_map(|symbol_table| symbol_table.get(ident).copied())
    }

    // pub fn get_const(&self, ident: &Ident) -> Option<Value> {
    //     match self.symbol_table.get(ident) {
    //         Some(Symbol::Constant(ret)) => Some(*ret),
    //         _ => None,
    //     }
    // }

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
    /// A completed basic block means it has end with one of the instruction below.
    /// `br`, `jump`, `ret`
    pub fn is_complete_bb(&mut self) -> bool {
        let curr_bb = self.curr_bb.unwrap();
        self.curr_func_data()
            .layout()
            .bbs()
            .node(&curr_bb)
            .unwrap()
            .insts()
            .back_key()
            .is_some_and(|&inst| {
                matches!(
                    self.curr_func_data().dfg().value(inst).kind(),
                    ValueKind::Branch(_) | ValueKind::Jump(_) | ValueKind::Return(_)
                )
            })
    }

    #[inline]
    /// No effect when a basic block is completed (a.k.a have `br`, `jump` or `ret` at the end)
    pub fn push_inst(&mut self, val: Value) {
        let curr_bb = self.curr_bb.unwrap();
        if !self.is_complete_bb() {
            self.curr_func_data_mut()
                .layout_mut()
                .bb_mut(curr_bb)
                .insts_mut()
                .push_key_back(val)
                .unwrap();
        }
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
    /// Return the original basic_block handle
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

    #[inline]
    pub fn set_def_type(&mut self, ty: Type) -> Option<Type> {
        self.def_type.replace(ty)
    }

    // #[inline]
    // pub fn reset_def_type(&mut self, ty: Option<Type>) {
    //     self.def_type = ty
    // }

    #[inline]
    pub fn curr_def_type(&self) -> Option<Type> {
        self.def_type.clone()
    }

    #[inline]
    pub fn is_constant(&self, l_val: &LVal) -> bool {
        matches!(
            self.curr_scope().get(&l_val.ident),
            Some(Symbol::Constant(_))
        )
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn should_p() {
        todo!();
    }
}
