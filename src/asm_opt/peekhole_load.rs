use itertools::Itertools;

use crate::{
    asm_pass_utils::AsmPass,
    riscv_utils::{List, RiscvInst},
};

pub struct PeekholeLoadElimination;

impl AsmPass for PeekholeLoadElimination {
    fn run_on(&self, insts: &mut List) {
        let mut remove_list = Vec::new();
        for (a, b) in insts.iter().tuple_windows() {
            let prev = a.1.value();
            let curr = b.1.value();
            if let RiscvInst::sw {
                rs2: s_rs2,
                imm12: s_imm12,
                rs1: s_rs1,
            } = prev
                && let RiscvInst::lw {
                    rd: l_rd,
                    imm12: l_imm12,
                    rs: l_rs,
                } = curr
                && s_rs2 == l_rd
                && s_imm12 == l_imm12
                && s_rs1 == l_rs
            {
                remove_list.push(*b.0);
            }
        }
        for item in remove_list {
            insts.remove(&item);
        }
    }
}
