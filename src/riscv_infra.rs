use num_enum::{IntoPrimitive, TryFromPrimitive};

#[allow(non_camel_case_types)]
#[allow(unused)]
#[derive(Debug, Eq, PartialEq, TryFromPrimitive, IntoPrimitive)]
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
}

impl std::fmt::Display for RiscvInst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RiscvInst::li { rd, imm } => write!(f, "li {}, {}", rd, imm),
            RiscvInst::add { rd, rs1, rs2 } => write!(f, "add {}, {}, {}", rd, rs1, rs2),
            RiscvInst::addi { rd, rs, imm12 } => write!(f, "addi {}, {}, {}", rd, rs, imm12),
            RiscvInst::sub { rd, rs1, rs2 } => write!(f, "sub {}, {}, {}", rd, rs1, rs2),
            RiscvInst::slt { rd, rs1, rs2 } => write!(f, "slt {}, {}, {}", rd, rs1, rs2),
            RiscvInst::sgt { rd, rs1, rs2 } => write!(f, "sgt {}, {}, {}", rd, rs1, rs2),
            RiscvInst::seqz { rd, rs } => write!(f, "seqz {}, {}", rd, rs),
            RiscvInst::snez { rd, rs } => write!(f, "snez {}, {}", rd, rs),
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
            RiscvInst::lw { rd, imm12, rs } => write!(f, "lw {}, {}({})", rd, imm12, rs),
            RiscvInst::sw { rs2, imm12, rs1 } => write!(f, "sw {}, {}({})", rs2, imm12, rs1),
            RiscvInst::jal { rd, offset } => write!(f, "jal {}, {}", rd, offset),
            RiscvInst::jalr { rd, rs, offset } => write!(f, "jalr {}, {}, {}", rd, rs, offset),
            RiscvInst::beq { rs1, rs2, offset } => write!(f, "beq {}, {}, {}", rs1, rs2, offset),
            RiscvInst::bne { rs1, rs2, offset } => write!(f, "bne {}, {}, {}", rs1, rs2, offset),
            RiscvInst::blt { rs1, rs2, offset } => write!(f, "blt {}, {}, {}", rs1, rs2, offset),
            RiscvInst::bge { rs1, rs2, offset } => write!(f, "bge {}, {}, {}", rs1, rs2, offset),
            RiscvInst::bltu { rs1, rs2, offset } => write!(f, "bltu {}, {}, {}", rs1, rs2, offset),
            RiscvInst::bgeu { rs1, rs2, offset } => write!(f, "bgeu {}, {}, {}", rs1, rs2, offset),
            RiscvInst::ret => write!(f, "ret"),
        }
    }
}

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
