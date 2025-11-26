use std::collections::HashMap;

use koopa::ir::{FunctionData, Value, ValueKind};
use num_enum::{IntoPrimitive, TryFromPrimitive};

#[allow(non_camel_case_types)]
#[allow(unused)]
#[derive(Debug, Eq, PartialEq, TryFromPrimitive, IntoPrimitive)]
#[repr(u8)]
pub enum Register {
    zero,
    ra,
    sp,
    gp,
    tp,
    t0,
    t1,
    t2,
    s0,
    s1,
    a0,
    a1,
    a2,
    a3,
    a4,
    a5,
    a6,
    a7,
    s2,
    s3,
    s4,
    s5,
    s6,
    s7,
    s8,
    s9,
    s10,
    s11,
    t3,
    t4,
    t5,
    t6,
}

#[allow(non_camel_case_types)]
#[allow(unused)]
pub enum RiscvInst {
    // li(Register, i32),
    li {
        rd: Register,
        imm: i32,
    },
    add {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    addi {
        rd: Register,
        rs1: Register,
        imm12: i32,
    },
    sub {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    slt {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    sgt {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    seqz {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    snez {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    xor {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    xori {
        rd: Register,
        rs1: Register,
        imm12: i32,
    },
    or {
        rd: Register,

        rs1: Register,
        rs2: Register,
    },
    ori {
        rd: Register,
        rs1: Register,
        imm12: i32,
    },
    and {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    andi {
        rd: Register,
        rs1: Register,
        imm12: i32,
    },
    mul {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    div {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    rem {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    mv {
        rd: Register,
        rs: Register,
    },
    ret,
}

impl std::fmt::Display for RiscvInst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RiscvInst::li { rd, imm } => write!(f, "li {}, {}", rd, imm),
            RiscvInst::add { rd, rs1, rs2 } => write!(f, "add {}, {}, {}", rd, rs1, rs2),
            RiscvInst::addi { rd, rs1, imm12 } => write!(f, "addi {}, {}, {}", rd, rs1, imm12),
            RiscvInst::sub { rd, rs1, rs2 } => write!(f, "sub {}, {}, {}", rd, rs1, rs2),
            RiscvInst::slt { rd, rs1, rs2 } => write!(f, "slt {}, {}, {}", rd, rs1, rs2),
            RiscvInst::sgt { rd, rs1, rs2 } => write!(f, "sgt {}, {}, {}", rd, rs1, rs2),
            RiscvInst::seqz { rd, rs1, rs2 } => write!(f, "seqz {}, {}, {}", rd, rs1, rs2),
            RiscvInst::snez { rd, rs1, rs2 } => write!(f, "snez {}, {}, {}", rd, rs1, rs2),
            RiscvInst::xor { rd, rs1, rs2 } => write!(f, "xor {}, {}, {}", rd, rs1, rs2),
            RiscvInst::xori { rd, rs1, imm12 } => write!(f, "xori {}, {}, {}", rd, rs1, imm12),
            RiscvInst::or { rd, rs1, rs2 } => write!(f, "or {}, {}, {}", rd, rs1, rs2),
            RiscvInst::ori { rd, rs1, imm12 } => write!(f, "ori {}, {}, {}", rd, rs1, imm12),
            RiscvInst::and { rd, rs1, rs2 } => write!(f, "and {}, {}, {}", rd, rs1, rs2),
            RiscvInst::andi { rd, rs1, imm12 } => write!(f, "andi {}, {}, {}", rd, rs1, imm12),
            RiscvInst::mul { rd, rs1, rs2 } => write!(f, "mul {}, {}, {}", rd, rs1, rs2),
            RiscvInst::div { rd, rs1, rs2 } => write!(f, "div {}, {}, {}", rd, rs1, rs2),
            RiscvInst::rem { rd, rs1, rs2 } => write!(f, "rem {}, {}, {}", rd, rs1, rs2),
            RiscvInst::mv { rd, rs } => write!(f, "mv {}, {}", rd, rs),
            RiscvInst::ret => write!(f, "ret"),
        }
    }
}

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

pub struct AsmGenContext {
    buf: String,
    indent_level: usize,
    reg_map: HashMap<Value, Register>,
    reg_cnt: usize,
}

pub trait GenerateAsm {
    fn generate(&self, ctx: &mut AsmGenContext);
}

fn inst() {
    use Register::*;
}

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
