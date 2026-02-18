use crate::{asm_pass_utils::AsmPass, riscv_utils::RiscvInst};

pub struct IdenticalMoveElimination;

impl AsmPass for IdenticalMoveElimination {
    fn run_on(&self, insts: &mut crate::riscv_utils::List) {
        let mut remove_list = Vec::new();
        for (index, node) in insts.iter() {
            if let RiscvInst::mv { rd, rs } = node.value()
                && rd == rs
            {
                remove_list.push(*index)
            }
        }
        for index in remove_list {
            insts.remove(&index);
        }
    }
}
