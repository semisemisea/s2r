use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashMap, VecDeque},
    fmt::Debug,
    ops::RangeInclusive,
};

use itertools::Itertools;
use koopa::ir::{Function, FunctionData, Program, Value, ValueKind};

use crate::{
    ir2riscv::inst_size,
    opt::utils::{self, IDAllocator, VIDAlloc},
    riscv_utils::{A0_BASE, Register},
};

type VRegister = Reverse<Register>;

#[derive(Debug)]
struct VirtualRegister {
    container: BinaryHeap<VRegister>,
    rules: HashMap<VRegister, Vec<RangeInclusive<usize>>>,
}

fn is_ranges_intersect(lhs: &RangeInclusive<usize>, rhs: &RangeInclusive<usize>) -> bool {
    !(lhs.end() < rhs.start() || lhs.start() > rhs.end())
}

impl VirtualRegister {
    fn alloc(&mut self, for_range: &RangeInclusive<usize>) -> Option<VRegister> {
        let mut not_usable = Vec::new();
        while let Some(virtual_reg) = self.container.pop() {
            if self.check(virtual_reg, for_range) {
                return Some(virtual_reg);
            }
            not_usable.push(virtual_reg);
        }
        self.container.extend(not_usable);
        None
    }

    #[inline]
    fn free(&mut self, reg: VRegister) {
        self.container.push(reg);
    }

    #[inline]
    fn check(&mut self, virtual_reg: VRegister, for_range: &RangeInclusive<usize>) -> bool {
        match self.rules.get(&virtual_reg) {
            Some(ranges) => ranges
                .iter()
                .all(|range| !is_ranges_intersect(range, for_range)),
            None => true,
        }
    }

    #[inline]
    fn add_rule(&mut self, virtual_reg: VRegister, ranges: RangeInclusive<usize>) {
        self.rules.entry(virtual_reg).or_default().push(ranges);
    }

    #[inline]
    fn new(max_size: usize) -> VirtualRegister {
        Self {
            container: BinaryHeap::from_iter(
                (0..max_size as u8).map(|x| Reverse(x.try_into().unwrap())),
            ),
            rules: HashMap::new(),
        }
    }
}

#[derive(Debug)]
pub enum AllocationState {
    Register(Register),
    Stack(usize),
}

pub struct RegisterAllocationResult {
    pub allocation: RegisterAllocation,
    pub insts_size: usize,
    pub call_ra: bool,
    pub extra_args: usize,
}

// pub fn program_liveness_analysis(
//     program: &mut Program,
// ) -> HashMap<Function, HashMap<Value, AllocationState>> {
//     let mut program_allocation = HashMap::new();
//     for (&func, data) in program.funcs_mut() {
//         if data.layout().entry_bb().is_none() {
//             continue;
//         }
//         let register_allocation = loop {
//             if let Some(reg_alloc) = liveness_analysis(data) {
//                 break reg_alloc;
//             }
//         };
//         program_allocation.insert(func, register_allocation);
//     }
//     program_allocation
// }

type RegisterAllocation = HashMap<Value, AllocationState>;

const REGISTER_COUNT: usize = 15;

pub fn liveness_analysis(data: &FunctionData) -> RegisterAllocationResult {
    let mut bb_alloc = IDAllocator::new(1);
    let mut val_alloc: VIDAlloc = IDAllocator::new(4);
    let graph = utils::build_cfg_forward(data, &mut bb_alloc);
    let rpo_path = utils::rpo_path(&graph);
    let mut register_manager = VirtualRegister::new(REGISTER_COUNT);

    let mut call_ra = false;
    let mut extra_args = 0usize;

    for &fparam in data.params() {
        val_alloc.check_or_alloc(fparam);
    }
    for &bb_id in rpo_path.iter() {
        let bb = bb_alloc.search_id(bb_id);
        let node = data.layout().bbs().node(&bb).unwrap();
        let iter = data
            .dfg()
            .bb(bb)
            .params()
            .iter()
            .chain(node.insts().iter().map(|(val, _)| val));
        for &inst in iter {
            let id = val_alloc.check_or_alloc(inst);

            if let ValueKind::Call(call) = data.dfg().value(inst).kind() {
                call_ra = true;
                extra_args = 8.max(call.args().len()) - 8;
                for index in 0..8.min(call.args().len()) {
                    register_manager.add_rule(Reverse(Register::arguments(index)), id..=id);
                }
                for index in 0..7 {
                    register_manager.add_rule(Reverse(Register::temporary(index)), id..=id);
                }
            }
        }
    }

    let mut liveness_ranges = HashMap::new();

    macro_rules! insert_range {
        ($inst:expr) => {
            if let Some(max_id) = data
                .dfg()
                .value($inst)
                .used_by()
                .iter()
                .filter_map(|&val| val_alloc.get_id_safe(val))
                .max()
            {
                liveness_ranges.insert($inst, val_alloc.get_id($inst)..=*max_id);
            }
        };
    }

    for &fparam in data.params() {
        insert_range!(fparam);
    }
    for (&bb, node) in data.layout().bbs() {
        let iter = data
            .dfg()
            .bb(bb)
            .params()
            .iter()
            .chain(node.insts().iter().map(|(val, _)| val));
        for &inst in iter {
            insert_range!(inst);
        }
    }

    let unhandled = {
        let mut unsorted = liveness_ranges.keys().cloned().collect::<Vec<_>>();
        unsorted.sort_unstable_by_key(|x| (*liveness_ranges[x].start(), *liveness_ranges[x].end()));
        unsorted.into_iter()
    };

    let mut register_allocation = HashMap::new();
    let mut curr_inst_offset = 0usize;

    let mut active: Vec<(std::ops::RangeInclusive<usize>, VRegister, Value)> =
        Vec::with_capacity(REGISTER_COUNT);
    for val in unhandled {
        let new_range = liveness_ranges.get(&val).unwrap();
        let remove_partition =
            active.partition_point(|(range, _reg, _val)| range.end() < new_range.start());
        for (_, reg, _) in active.drain(0..remove_partition) {
            register_manager.free(reg);
        }

        macro_rules! active_insert {
            ($new_range:expr, $register:expr, $value: expr) => {
                let insert_idx =
                    active.partition_point(|(range, _reg, _val)| range.end() <= $new_range.end());
                active.insert(insert_idx, ($new_range.clone(), $register, $value));
            };
        }

        macro_rules! alloc_stack {
            ($val: expr) => {
                register_allocation.insert($val, AllocationState::Stack(curr_inst_offset));
                curr_inst_offset += inst_size(data, $val);
            };
        }

        if let Some(alloc) = register_manager.alloc(new_range) {
            active_insert!(new_range, alloc, val);
            register_allocation.insert(val, AllocationState::Register(alloc.0));
        } else {
            eprintln!("Spill!");
            if let Some((index, (occupied_range, occupied_reg, occupied_val))) = active
                .iter()
                .rev()
                .find_position(|&&(_, reg, _)| register_manager.check(reg, new_range))
            {
                if occupied_range.end() > new_range.end() {
                    // spill the occupied one
                    alloc_stack!(*occupied_val);
                    register_allocation.insert(val, AllocationState::Register(occupied_reg.0));
                    let alloc_reg = *occupied_reg;
                    active.remove(index);
                    active_insert!(new_range, alloc_reg, val);
                } else {
                    // spill the current one
                    alloc_stack!(val);
                }
            } else {
                // spill the current one
                alloc_stack!(val);
            }
        }
    }

    eprintln!("function name:{:?}", data.name());

    eprintln!("--------------------------------");

    for (k, v) in liveness_ranges.iter() {
        eprintln!("{:?} {:?}", k, v);
    }

    for (k, v) in register_allocation.iter() {
        eprintln!("{:?} {:?}", k, v);
    }

    eprintln!("--------------------------------");

    RegisterAllocationResult {
        allocation: register_allocation,
        insts_size: curr_inst_offset,
        call_ra,
        extra_args,
    }
    // Some(register_allocation)
}

// TODO:
// last use at 100 and start at 100 is ok.
// but what about other situation like call.
// 2026-02-17 23:18:
// answer is not.
// we need to introduce Input/Output to tell the difference.
// we can ingore this case and consider it for collision for now.

#[cfg(test)]
mod test {
    use crate::register_alloc::is_ranges_intersect;

    #[test]
    fn intersect() {
        assert!(is_ranges_intersect(&(0..=5), &(4..=10)));
        assert!(!is_ranges_intersect(&(0..=5), &(9..=10)));
        assert!(!is_ranges_intersect(&(10..=20), &(4..=9)));
        assert!(is_ranges_intersect(&(0..=5), &(2..=3)));
        assert!(is_ranges_intersect(&(2..=4), &(1..=5)));
        assert!(is_ranges_intersect(&(4..=10), &(0..=5)));
        assert!(is_ranges_intersect(&(4..=104), &(100..=100)));
        assert!(is_ranges_intersect(&(4..=8), &(8..=100)));
    }
}
