use koopa::{
    ir::{
        BinaryOp, FunctionData, ValueKind,
        builder::{LocalInstBuilder, ValueBuilder},
    },
    opt::FunctionPass,
};

pub struct StrengthReduction;

impl FunctionPass for StrengthReduction {
    fn run_on(&mut self, func: koopa::ir::Function, data: &mut koopa::ir::FunctionData) {
        self.local_reduction(data);
    }
}

impl StrengthReduction {
    fn local_reduction(&self, data: &mut FunctionData) {
        let to_change = data
            .layout()
            .bbs()
            .iter()
            .flat_map(|(_, node)| node.insts().iter().map(|(&val, _)| val))
            .filter(|&val| matches!(data.dfg().value(val).kind(), ValueKind::Binary(_)))
            .collect::<Vec<_>>();

        for val in to_change {
            let ValueKind::Binary(binary) = data.dfg().value(val).kind() else {
                unreachable!()
            };
            match binary.op() {
                BinaryOp::Mul => {
                    if let ValueKind::Integer(int) = data.dfg().value(binary.lhs()).kind()
                        && int.value().is_positive()
                        && (int.value() as u32).is_power_of_two()
                    {
                        let po2 = int.value() as u32;
                        let shl_base = binary.lhs();
                        let shl_offset = data
                            .dfg_mut()
                            .new_value()
                            .integer(po2.trailing_zeros() as i32);
                        data.dfg_mut().replace_value_with(val).binary(
                            BinaryOp::Shl,
                            shl_base,
                            shl_offset,
                        );
                    } else if let ValueKind::Integer(int) = data.dfg().value(binary.rhs()).kind()
                        && int.value().is_positive()
                        && (int.value() as u32).is_power_of_two()
                    {
                        let po2 = int.value() as u32;
                        let shl_base = binary.lhs();
                        let shl_offset = data
                            .dfg_mut()
                            .new_value()
                            .integer(po2.trailing_zeros() as i32);
                        data.dfg_mut().replace_value_with(val).binary(
                            BinaryOp::Shl,
                            shl_base,
                            shl_offset,
                        );
                    }
                }
                BinaryOp::Div => {
                    if let ValueKind::Integer(int) = data.dfg().value(binary.rhs()).kind()
                        && int.value().is_positive()
                        && (int.value() as u32).is_power_of_two()
                    {
                        let po2 = int.value() as u32;
                        let shl_base = binary.lhs();
                        let shl_offset = data
                            .dfg_mut()
                            .new_value()
                            .integer(po2.trailing_zeros() as i32);
                        data.dfg_mut().replace_value_with(val).binary(
                            BinaryOp::Sar,
                            shl_base,
                            shl_offset,
                        );
                    }
                }
                _ => {}
            }
        }
    }
}
