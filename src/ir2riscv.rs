use crate::riscv_infra::{Register, RiscvInst};
use std::collections::HashMap;

use koopa::ir::{FunctionData, Value, ValueKind};

pub struct AsmGenContext {
    buf: String,
    indent_level: usize,
    reg_map: HashMap<Value, Register>,
    reg_cnt: usize,
}

pub trait GenerateAsm {
    fn generate(&self, ctx: &mut AsmGenContext);
}

fn inst() {}

impl AsmGenContext {
    pub fn new() -> AsmGenContext {
        AsmGenContext {
            buf: String::new(),
            indent_level: 0,
            reg_map: HashMap::new(),
            reg_cnt: 0,
        }
    }

    pub fn end(self) -> String {
        self.buf
    }
    fn writeln(&mut self, string: &str) {
        for _ in 0..self.indent_level {
            self.buf.push_str("  ");
        }
        self.buf.push_str(string);
        self.buf.push('\n');
    }

    fn incr_indent(&mut self) {
        self.indent_level += 1;
    }

    fn decr_indent(&mut self) {
        self.indent_level -= 1;
    }
}

impl GenerateAsm for koopa::ir::Program {
    fn generate(&self, ctx: &mut AsmGenContext) {
        ctx.incr_indent();
        ctx.writeln(".text");
        ctx.writeln(".globl main");
        ctx.decr_indent();
        for &func in self.func_layout() {
            let func_data = self.func(func);
            func_data.generate(ctx);
        }
    }
}

impl GenerateAsm for koopa::ir::FunctionData {
    fn generate(&self, ctx: &mut AsmGenContext) {
        ctx.writeln(&format!("{}:", self.name().strip_prefix("@").unwrap()));
        ctx.incr_indent();
        for (&_bb, node) in self.layout().bbs() {
            for &inst in node.insts().keys() {
                value_repr(inst, self, ctx);
            }
        }
        ctx.decr_indent();
    }
}

fn value_repr(val: Value, func_data: &FunctionData, ctx: &mut AsmGenContext) {
    let value_data = func_data.dfg().value(val);
    match value_data.kind() {
        ValueKind::Integer(int) => {
            ctx.writeln(&format!("li a0, {}", int.value()));
        }
        ValueKind::Return(ret) => {
            let ret_val = ret.value().unwrap();
            value_repr(ret_val, func_data, ctx);
            ctx.writeln("ret");
        }
        _ => todo!(),
    }
}
