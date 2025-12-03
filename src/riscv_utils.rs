use std::collections::HashMap;

use koopa::ir::{BasicBlock, BinaryOp, Function, FunctionData, Program, Value, ValueKind};
use num_enum::{IntoPrimitive, TryFromPrimitive};

#[allow(non_camel_case_types)]
#[allow(unused)]
#[derive(Debug, Eq, PartialEq, TryFromPrimitive, IntoPrimitive, Clone, Copy)]
#[repr(u8)]
/// Enum representing RISC-V registers.
/// Each variant corresponds to a physical register in the RISC-V architecture.
/// The names follow the RISC-V calling convention and register usage:
/// - zero: Constant zero
/// - ra: Return address
/// - sp: Stack pointer
/// - gp: Global pointer
/// - tp: Thread pointer
/// - t0-t6: Temporaries
/// - s0-s11: Saved registers
/// - a0-a7: Function arguments / return values
pub enum Register {
    zero, // 0
    ra,   // 1
    sp,   // 2
    gp,   // 3
    tp,   // 4
    t0,   // 5
    t1,
    t2,
    t3,
    t4,
    t5,
    t6,
    s0, // 12
    s1,
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
    a0, // 24
    a1,
    a2,
    a3,
    a4,
    a5,
    a6,
    a7,
}

#[allow(non_camel_case_types)]
#[allow(unused)]
/// Enum representing RISC-V instructions.
/// Each variant corresponds to a RISC-V instruction, with fields for operands.
/// Documentation for each variant describes its semantics and operand usage.
pub enum RiscvInst {
    /// Load immediate: `li rd, imm`
    /// Loads a 32-bit immediate value into register `rd`.
    li { rd: Register, imm: i32 },
    /// Add: `add rd, rs1, rs2`
    /// Adds `rs1` and `rs2`, stores result in `rd`.
    add {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    /// Add immediate: `addi rd, rs1, imm12`
    /// Adds `rs1` and 12-bit immediate, stores result in `rd`.
    addi {
        rd: Register,
        rs: Register,
        imm12: i32,
    },
    /// Subtract: `sub rd, rs1, rs2`
    /// Subtracts `rs2` from `rs1`, stores result in `rd`.
    sub {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    /// Set less than: `slt rd, rs1, rs2`
    /// Sets `rd` to 1 if `rs1` < `rs2`, else 0.
    slt {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    /// Set greater than: `sgt rd, rs1, rs2`
    /// Sets `rd` to 1 if `rs1` > `rs2`, else 0.
    sgt {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    /// Set equal to zero: `seqz rd, rs`
    /// Sets `rd` to 1 if `rs` == 0, else 0.
    seqz { rd: Register, rs: Register },
    /// Set not equal to zero: `snez rd, rs`
    /// Sets `rd` to 1 if `rs` != 0, else 0.
    snez { rd: Register, rs: Register },
    /// Exclusive OR: `xor rd, rs1, rs2`
    /// Bitwise XOR of `rs1` and `rs2`, stores result in `rd`.
    xor {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    /// Exclusive OR immediate: `xori rd, rs1, imm12`
    /// Bitwise XOR of `rs1` and 12-bit immediate, stores result in `rd`.
    xori {
        rd: Register,
        rs1: Register,
        imm12: i32,
    },
    /// Bitwise OR: `or rd, rs1, rs2`
    /// Bitwise OR of `rs1` and `rs2`, stores result in `rd`.
    or {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    /// Bitwise OR immediate: `ori rd, rs1, imm12`
    /// Bitwise OR of `rs1` and 12-bit immediate, stores result in `rd`.
    ori {
        rd: Register,
        rs1: Register,
        imm12: i32,
    },
    /// Bitwise AND: `and rd, rs1, rs2`
    /// Bitwise AND of `rs1` and `rs2`, stores result in `rd`.
    and {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    /// Bitwise AND immediate: `andi rd, rs1, imm12`
    /// Bitwise AND of `rs1` and 12-bit immediate, stores result in `rd`.
    andi {
        rd: Register,
        rs1: Register,
        imm12: i32,
    },
    /// Multiply: `mul rd, rs1, rs2`
    /// Multiplies `rs1` and `rs2`, stores result in `rd`.
    mul {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    /// Divide: `div rd, rs1, rs2`
    /// Divides `rs1` by `rs2`, stores result in `rd`.
    div {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    /// Remainder: `rem rd, rs1, rs2`
    /// Computes remainder of `rs1` / `rs2`, stores result in `rd`.
    rem {
        rd: Register,
        rs1: Register,
        rs2: Register,
    },
    /// Move: `mv rd, rs`
    /// Copies value from `rs` to `rd`.
    mv { rd: Register, rs: Register },
    /// Load word: `lw rd, imm12(rs)`
    /// Loads 32-bit value from address `rs + imm12` into `rd`.
    lw {
        rd: Register,
        imm12: i32,
        rs: Register,
    },
    /// Store word: `sw rs2, imm12(rs1)`
    /// Stores 32-bit value from `rs2` into address `rs1 + imm12`.
    sw {
        rs2: Register,
        imm12: i32,
        rs1: Register,
    },
    /// Jump and link: `jal rd, offset`
    /// Jumps to address `PC + offset`, stores return address in `rd`.
    jal { rd: Register, offset: i32 },
    /// Jump and link register: `jalr rd, rs1, offset`
    /// Jumps to address `rs1 + offset`, stores return address in `rd`.
    jalr {
        rd: Register,
        rs: Register,
        offset: i32,
    },
    /// Branch if equal: `beq rs1, rs2, offset`
    /// Branches to `PC + offset` if `rs1 == rs2`.
    beq {
        rs1: Register,
        rs2: Register,
        offset: i32,
    },
    /// Branch if not equal: `bne rs1, rs2, offset`
    /// Branches to `PC + offset` if `rs1 != rs2`.
    bne {
        rs1: Register,
        rs2: Register,
        offset: i32,
    },
    /// Branch if less than: `blt rs1, rs2, offset`
    /// Branches to `PC + offset` if `rs1 < rs2`.
    blt {
        rs1: Register,
        rs2: Register,
        offset: i32,
    },
    /// Branch if greater or equal: `bge rs1, rs2, offset`
    /// Branches to `PC + offset` if `rs1 >= rs2`.
    bge {
        rs1: Register,
        rs2: Register,
        offset: i32,
    },
    /// Branch if less than unsigned: `bltu rs1, rs2, offset`
    /// Branches to `PC + offset` if `rs1 < rs2` (unsigned).
    bltu {
        rs1: Register,
        rs2: Register,
        offset: i32,
    },
    /// Branch if greater or equal unsigned: `bgeu rs1, rs2, offset`
    /// Branches to `PC + offset` if `rs1 >= rs2` (unsigned).
    bgeu {
        rs1: Register,
        rs2: Register,
        offset: i32,
    },
    /// Return from function: `ret`
    /// Returns from current function.
    ret,
    /// Jump to label: `j label`
    /// Jump to a label unconditionally.
    j { label: String },
    /// Branch if equal to zero: `beqz rs, label`
    /// Branches to label if `rs == 0`
    beqz { rs: Register, label: String },
    /// Branch if not equal to zero: `bnez rs, label`
    /// Branches to label if `rs != 0`
    bnez { rs: Register, label: String },
}

impl std::fmt::Display for RiscvInst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RiscvInst::li { rd, imm } => write!(f, "li    {}, {}", rd, imm),
            RiscvInst::add { rd, rs1, rs2 } => write!(f, "add   {}, {}, {}", rd, rs1, rs2),
            RiscvInst::addi { rd, rs, imm12 } => write!(f, "addi  {}, {}, {}", rd, rs, imm12),
            RiscvInst::sub { rd, rs1, rs2 } => write!(f, "sub   {}, {}, {}", rd, rs1, rs2),
            RiscvInst::slt { rd, rs1, rs2 } => write!(f, "slt   {}, {}, {}", rd, rs1, rs2),
            RiscvInst::sgt { rd, rs1, rs2 } => write!(f, "sgt   {}, {}, {}", rd, rs1, rs2),
            RiscvInst::seqz { rd, rs } => write!(f, "seqz  {}, {}", rd, rs),
            RiscvInst::snez { rd, rs } => write!(f, "snez  {}, {}", rd, rs),
            RiscvInst::xor { rd, rs1, rs2 } => write!(f, "xor   {}, {}, {}", rd, rs1, rs2),
            RiscvInst::xori { rd, rs1, imm12 } => write!(f, "xori  {}, {}, {}", rd, rs1, imm12),
            RiscvInst::or { rd, rs1, rs2 } => write!(f, "or    {}, {}, {}", rd, rs1, rs2),
            RiscvInst::ori { rd, rs1, imm12 } => write!(f, "ori   {}, {}, {}", rd, rs1, imm12),
            RiscvInst::and { rd, rs1, rs2 } => write!(f, "and   {}, {}, {}", rd, rs1, rs2),
            RiscvInst::andi { rd, rs1, imm12 } => write!(f, "andi  {}, {}, {}", rd, rs1, imm12),
            RiscvInst::mul { rd, rs1, rs2 } => write!(f, "mul   {}, {}, {}", rd, rs1, rs2),
            RiscvInst::div { rd, rs1, rs2 } => write!(f, "div   {}, {}, {}", rd, rs1, rs2),
            RiscvInst::rem { rd, rs1, rs2 } => write!(f, "rem   {}, {}, {}", rd, rs1, rs2),
            RiscvInst::mv { rd, rs } => write!(f, "mv    {}, {}", rd, rs),
            RiscvInst::lw { rd, imm12, rs } => write!(f, "lw    {}, {}({})", rd, imm12, rs),
            RiscvInst::sw { rs2, imm12, rs1 } => write!(f, "sw    {}, {}({})", rs2, imm12, rs1),
            RiscvInst::jal { rd, offset } => write!(f, "jal   {}, {}", rd, offset),
            RiscvInst::jalr { rd, rs, offset } => write!(f, "jalr  {}, {}, {}", rd, rs, offset),
            RiscvInst::beq { rs1, rs2, offset } => write!(f, "beq   {}, {}, {}", rs1, rs2, offset),
            RiscvInst::bne { rs1, rs2, offset } => write!(f, "bne   {}, {}, {}", rs1, rs2, offset),
            RiscvInst::blt { rs1, rs2, offset } => write!(f, "blt   {}, {}, {}", rs1, rs2, offset),
            RiscvInst::bge { rs1, rs2, offset } => write!(f, "bge   {}, {}, {}", rs1, rs2, offset),
            RiscvInst::bltu { rs1, rs2, offset } => write!(f, "bltu  {}, {}, {}", rs1, rs2, offset),
            RiscvInst::bgeu { rs1, rs2, offset } => write!(f, "bgeu  {}, {}, {}", rs1, rs2, offset),
            RiscvInst::ret => write!(f, "ret"),
            RiscvInst::j { label } => write!(f, "j     {}", label),
            RiscvInst::beqz { rs, label } => write!(f, "beqz  {}, {}", rs, label),
            RiscvInst::bnez { rs, label } => write!(f, "bnez  {}, {}", rs, label),
        }
    }
}

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

macro_rules! import {
    () => {
        #[allow(unused)]
        use Register::*;
        use RiscvInst::*;
    };
}
const SHIFT_WIDTH: usize = 2;
const TEMP_BASE_U8_REPR: u8 = 5;

pub struct RegisterManager {
    usage: u8,
}

impl RegisterManager {
    fn new() -> RegisterManager {
        RegisterManager { usage: 0 }
    }

    #[inline]
    fn alloc(&mut self) -> Register {
        let ret = (TEMP_BASE_U8_REPR + self.usage).try_into().unwrap();
        self.incr();
        ret
    }

    #[inline]
    fn incr(&mut self) {
        debug_assert!(self.usage < 7, "run out of tempoprary register");
        self.usage += 1;
    }

    #[inline]
    fn decr(&mut self) {
        self.usage -= 1;
    }

    fn take(&mut self) -> Register {
        self.decr();
        (TEMP_BASE_U8_REPR + self.usage).try_into().unwrap()
    }
}

pub struct AsmGenContext {
    // buffer: asm text.
    buf: String,
    indent_level: usize,
    func_stack: Vec<Function>,
    stack_slots: HashMap<Value, usize>,
    reg_pool: RegisterManager,
    curr_inst: Option<Value>,
    epilogue_stack: Vec<Epilogue>,
}

pub trait GenerateAsm {
    fn generate(&self, program: &Program, ctx: &mut AsmGenContext) -> anyhow::Result<()>;
}

impl AsmGenContext {
    pub fn new() -> AsmGenContext {
        AsmGenContext {
            buf: String::new(),
            indent_level: 0,
            func_stack: Vec::new(),
            stack_slots: HashMap::new(),
            reg_pool: RegisterManager::new(),
            curr_inst: None,
            epilogue_stack: Vec::new(),
        }
    }

    pub fn bb_params<'a>(&self, bb: BasicBlock, program: &'a Program) -> &'a [Value] {
        self.curr_func_data(program).dfg().bb(bb).params()
    }

    pub fn get_bb_name(&self, bb: BasicBlock, program: &Program) -> String {
        let curr_func = self.curr_func_data(program);
        let func_name = curr_func.name().strip_prefix("@").unwrap();
        let bb_name = curr_func
            .dfg()
            .bb(bb)
            .name()
            .as_ref()
            .unwrap()
            .strip_prefix("%")
            .unwrap();
        format!(".L_{}_{}", func_name, bb_name)
    }

    pub fn insert_inst(&mut self, val: Value, offset: usize) {
        self.stack_slots.insert(val, offset);
    }

    pub fn get_inst_offset(&self, val: Value) -> Option<usize> {
        self.stack_slots.get(&val).copied()
    }

    pub fn generate(&mut self, program: &Program) -> anyhow::Result<()> {
        self.incr_indent();
        self.writeln(".text");
        self.writeln(".globl main");
        self.decr_indent();

        for &func in program.func_layout().iter() {
            self.push_func(func);
            let func_data = program.func(func);
            func_data.generate(program, self)?;
            self.pop_func();
        }
        Ok(())
    }

    #[inline]
    pub fn push_func(&mut self, func: Function) {
        self.func_stack.push(func);
    }

    #[inline]
    pub fn end(self) -> String {
        self.buf
    }

    pub fn writeln(&mut self, string: &str) {
        for _ in 0..self.indent_level * SHIFT_WIDTH {
            self.buf.push(' ');
        }
        self.buf.push_str(string);
        self.buf.push('\n');
    }

    pub fn write_inst(&mut self, inst: RiscvInst) {
        for _ in 0..self.indent_level * SHIFT_WIDTH {
            self.buf.push(' ');
        }
        self.buf += format!("{}\n", inst).as_str();
    }

    pub fn prologue(&mut self, offset: usize) {
        import!();
        // According to RISC-V, sp_offset should be aligned with 16.
        let offset = if (offset & 0x0F) != 0 {
            (offset + 0x0F) >> 4 << 4
        } else {
            offset
        } as i32;

        // if offset can't represent in imm12, we should use a temporary register.
        if (offset >> 12) != 0 {
            self.write_inst(li {
                rd: t0,
                imm: -offset,
            });
            self.write_inst(add {
                rd: sp,
                rs1: sp,
                rs2: t0,
            });
        } else {
            self.write_inst(addi {
                rd: sp,
                rs: sp,
                imm12: -offset,
            });
        }
        self.epilogue_stack.push(Epilogue {
            offset,
            done: false,
        })
    }

    #[inline]
    pub fn incr_indent(&mut self) {
        self.indent_level += 1;
    }

    #[inline]
    pub fn decr_indent(&mut self) {
        self.indent_level -= 1;
    }

    pub fn pop_func(&mut self) -> Option<Function> {
        self.func_stack.pop()
    }

    pub fn curr_func_hanlde(&self) -> &Function {
        self.func_stack.last().unwrap()
    }

    pub fn curr_func_data<'a>(&self, program: &'a Program) -> &'a FunctionData {
        program.func(*self.curr_func_hanlde())
    }

    pub fn load_to_register(&mut self, program: &Program, val: Value) {
        let data = self.curr_func_data(program).dfg().value(val);
        if let ValueKind::Integer(int) = data.kind() {
            self.load_imm(int.value());
            return;
        }
        if !data.ty().is_unit() {
            let offset = self.get_inst_offset(val).unwrap() as i32;
            self.load_word(offset);
        }
    }

    pub fn save_word_at_curr_inst(&mut self) {
        import!();
        let curr_inst = self.curr_inst.unwrap();
        let offset = self.get_inst_offset(curr_inst).unwrap() as i32;
        let source = self.reg_pool.take();
        self.write_inst(sw {
            rs2: source,
            imm12: offset,
            rs1: sp,
        });
    }

    pub fn curr_inst_mut(&mut self) -> &mut Option<Value> {
        &mut self.curr_inst
    }
}

#[derive(Clone)]
pub struct Epilogue {
    offset: i32,
    done: bool,
}

impl Epilogue {
    pub fn finish(&mut self, ctx: &mut AsmGenContext) {
        import!();
        self.done = true;
        if (self.offset >> 12) != 0 {
            let temp_reg = ctx.reg_pool.alloc();
            ctx.write_inst(li {
                rd: temp_reg,
                imm: self.offset,
            });
            ctx.write_inst(add {
                rd: sp,
                rs1: sp,
                rs2: temp_reg,
            });
        } else {
            ctx.write_inst(addi {
                rd: sp,
                rs: sp,
                imm12: self.offset,
            });
        }
        ctx.write_inst(ret);
    }
}

impl Drop for Epilogue {
    fn drop(&mut self) {
        if !self.done {
            eprintln!("Epilogue must be done before droped.");
        }
    }
}

//Specific instruction implementation
impl AsmGenContext {
    #[inline]
    pub fn load_imm(&mut self, imm: i32) {
        import!();
        let temp_reg = self.reg_pool.alloc();
        self.write_inst(li { rd: temp_reg, imm });
    }

    pub fn save_word_at_inst(&mut self, val: Value) {
        let offset = self.get_inst_offset(val).unwrap() as i32;
        self.save_word_with_offset(offset);
    }

    #[inline]
    pub fn save_word_with_offset(&mut self, offset: i32) {
        import!();
        let temp_reg = self.reg_pool.take();
        self.write_inst(sw {
            rs2: temp_reg,
            imm12: offset,
            rs1: sp,
        });
    }

    #[inline]
    pub fn load_word(&mut self, offset: i32) {
        import!();
        let temp_reg = self.reg_pool.alloc();
        self.write_inst(lw {
            rd: temp_reg,
            imm12: offset,
            rs: sp,
        });
    }

    pub fn binary_op(&mut self, op: BinaryOp) {
        import!();
        let rhs = self.reg_pool.take();
        let lhs = self.reg_pool.take();
        let res = self.reg_pool.alloc();
        match op {
            BinaryOp::NotEq => {
                self.write_inst(sub {
                    rd: res,
                    rs1: lhs,
                    rs2: rhs,
                });
                self.write_inst(snez { rd: res, rs: res });
            }
            BinaryOp::Eq => {
                self.write_inst(sub {
                    rd: res,
                    rs1: lhs,
                    rs2: rhs,
                });
                self.write_inst(seqz { rd: res, rs: res });
            }
            BinaryOp::Gt => self.write_inst(sgt {
                rd: res,
                rs1: lhs,
                rs2: rhs,
            }),
            BinaryOp::Lt => self.write_inst(slt {
                rd: res,
                rs1: lhs,
                rs2: rhs,
            }),
            BinaryOp::Ge => {
                self.write_inst(slt {
                    rd: res,
                    rs1: lhs,
                    rs2: rhs,
                });
                self.write_inst(seqz { rd: res, rs: res });
            }
            BinaryOp::Le => {
                self.write_inst(sgt {
                    rd: res,
                    rs1: lhs,
                    rs2: rhs,
                });
                self.write_inst(seqz { rd: res, rs: res });
            }
            BinaryOp::Add => self.write_inst(add {
                rd: res,
                rs1: lhs,
                rs2: rhs,
            }),

            BinaryOp::Sub => self.write_inst(sub {
                rd: res,
                rs1: lhs,
                rs2: rhs,
            }),
            BinaryOp::Mul => self.write_inst(mul {
                rd: res,
                rs1: lhs,
                rs2: rhs,
            }),
            BinaryOp::Div => self.write_inst(div {
                rd: res,
                rs1: lhs,
                rs2: rhs,
            }),
            BinaryOp::Mod => self.write_inst(rem {
                rd: res,
                rs1: lhs,
                rs2: rhs,
            }),
            BinaryOp::And => todo!(),
            BinaryOp::Or => todo!(),
            BinaryOp::Xor => todo!(),
            BinaryOp::Shl => todo!(),
            BinaryOp::Shr => todo!(),
            BinaryOp::Sar => todo!(),
        }
    }

    pub fn ret(&mut self) {
        import!();
        let source = self.reg_pool.take();
        self.write_inst(mv { rd: a0, rs: source });
        self.epilogue_stack.last().unwrap().clone().finish(self);
    }

    pub fn jump(&mut self, bb: BasicBlock, program: &Program) {
        import!();
        self.write_inst(j {
            label: self.get_bb_name(bb, program),
        });
    }

    pub fn if_jump(&mut self, true_bb: BasicBlock, false_bb: BasicBlock, program: &Program) {
        import!();
        let cond_reg = self.reg_pool.take();
        self.write_inst(bnez {
            rs: cond_reg,
            label: self.get_bb_name(true_bb, program),
        });
        self.write_inst(beqz {
            rs: cond_reg,
            label: self.get_bb_name(false_bb, program),
        });
    }
}
