#![allow(unused)]
use std::collections::{HashSet, VecDeque};

use koopa::{
    ir::{BasicBlock, Function, FunctionData, Program, Value, entities::ValueData},
    opt::{FunctionPass, ModulePass},
};

use crate::opt::utils::{IDAllocator, build_cfg};

pub struct DeadCodeElimination;

pub struct UnreachableBasicBlock;

pub struct RemoveDiscardedValue;

impl ModulePass for RemoveDiscardedValue {
    fn run_on(&mut self, program: &mut Program) {
        let mut set = HashSet::new();
        for (&gval, _) in program.borrow_values().iter() {
            mark_global_value(gval, program, &mut set);
        }
        let mut remove_list = program
            .borrow_values()
            .keys()
            .filter(|&val| !set.contains(val))
            .copied()
            .collect::<VecDeque<_>>();
        eprintln!("remove_list: {remove_list:?}");
        while let Some(front) = remove_list.pop_front() {
            if program.borrow_value(front).used_by().is_empty() {
                program.remove_value(front);
            } else {
                remove_list.push_back(front);
            }
        }
        for (&func, data) in program.funcs_mut() {
            run_on_func(func, data);
        }
    }
}

fn run_on_func(func: Function, data: &mut FunctionData) {
    // mark
    let mut set = HashSet::new();
    for (&bb, node) in data.layout().bbs() {
        for (&val, _) in node.insts() {
            // eprintln!("{val:?}");
            // eprintln!("item kind: {:?}", data.dfg().value(val).kind());

            mark_local_value(val, data, &mut set);
        }
    }
    let mut remove_list = data
        .dfg()
        .values()
        .keys()
        .filter(|&val| !set.contains(val))
        .copied()
        .collect::<VecDeque<_>>();
    for item in remove_list.iter() {
        eprintln!("item kind: {:?}", data.dfg().value(*item).kind());
    }
    // eprintln!("remove_list: {remove_list:?}");
    while let Some(front) = remove_list.pop_front() {
        if data.dfg().value(front).used_by().is_empty() {
            data.dfg_mut().remove_value(front);
        } else if data
            .dfg()
            .value(front)
            .used_by()
            .iter()
            .all(|x| !set.contains(x))
        {
            remove_list.push_back(front);
        }
    }
}

fn mark_global_value(val: Value, program: &Program, set: &mut HashSet<Value>) {
    set.insert(val);
    let vd = program.borrow_value(val);
    match vd.kind() {
        koopa::ir::ValueKind::Load(load) => mark_global_value(load.src(), program, set),
        koopa::ir::ValueKind::Store(store) => {
            mark_global_value(store.dest(), program, set);
            mark_global_value(store.value(), program, set);
        }
        koopa::ir::ValueKind::GetPtr(get_ptr) => {
            mark_global_value(get_ptr.src(), program, set);
            mark_global_value(get_ptr.index(), program, set);
        }
        koopa::ir::ValueKind::GetElemPtr(get_elem_ptr) => {
            mark_global_value(get_elem_ptr.src(), program, set);
            mark_global_value(get_elem_ptr.index(), program, set);
        }
        koopa::ir::ValueKind::Binary(binary) => {
            mark_global_value(binary.lhs(), program, set);
            mark_global_value(binary.rhs(), program, set);
        }
        koopa::ir::ValueKind::Branch(branch) => {
            mark_global_value(branch.cond(), program, set);
            branch
                .true_args()
                .iter()
                .for_each(|&val| mark_global_value(val, program, set));
            branch
                .false_args()
                .iter()
                .for_each(|&val| mark_global_value(val, program, set));
        }
        koopa::ir::ValueKind::Jump(jump) => {
            jump.args()
                .iter()
                .for_each(|&val| mark_global_value(val, program, set));
        }
        koopa::ir::ValueKind::Call(call) => {
            call.args()
                .iter()
                .for_each(|&val| mark_global_value(val, program, set));
        }
        koopa::ir::ValueKind::Return(ret) => {
            if let Some(val) = ret.value() {
                mark_global_value(val, program, set);
            }
        }
        koopa::ir::ValueKind::Integer(integer) => {}
        koopa::ir::ValueKind::ZeroInit(zero_init) => {}
        koopa::ir::ValueKind::Undef(undef) => {}
        koopa::ir::ValueKind::Aggregate(aggregate) => {
            aggregate
                .elems()
                .iter()
                .for_each(|&val| mark_global_value(val, program, set));
        }
        koopa::ir::ValueKind::FuncArgRef(func_arg_ref) => {}
        koopa::ir::ValueKind::BlockArgRef(block_arg_ref) => {}
        koopa::ir::ValueKind::Alloc(alloc) => {}
        koopa::ir::ValueKind::GlobalAlloc(global_alloc) => {
            mark_global_value(global_alloc.init(), program, set);
        }
    }
}

fn mark_local_value(val: Value, data: &FunctionData, set: &mut HashSet<Value>) {
    set.insert(val);
    let vd = data.dfg().value(val);
    match vd.kind() {
        koopa::ir::ValueKind::Load(load) => mark_local_value(load.src(), data, set),
        koopa::ir::ValueKind::Store(store) => {
            mark_local_value(store.dest(), data, set);
            mark_local_value(store.value(), data, set);
        }
        koopa::ir::ValueKind::GetPtr(get_ptr) => {
            mark_local_value(get_ptr.src(), data, set);
            mark_local_value(get_ptr.index(), data, set);
        }
        koopa::ir::ValueKind::GetElemPtr(get_elem_ptr) => {
            mark_local_value(get_elem_ptr.src(), data, set);
            mark_local_value(get_elem_ptr.index(), data, set);
        }
        koopa::ir::ValueKind::Binary(binary) => {
            mark_local_value(binary.lhs(), data, set);
            mark_local_value(binary.rhs(), data, set);
        }
        koopa::ir::ValueKind::Branch(branch) => {
            mark_local_value(branch.cond(), data, set);
            branch
                .true_args()
                .iter()
                .for_each(|&val| mark_local_value(val, data, set));
            branch
                .false_args()
                .iter()
                .for_each(|&val| mark_local_value(val, data, set));
        }
        koopa::ir::ValueKind::Jump(jump) => {
            jump.args()
                .iter()
                .for_each(|&val| mark_local_value(val, data, set));
        }
        koopa::ir::ValueKind::Call(call) => {
            call.args()
                .iter()
                .for_each(|&val| mark_local_value(val, data, set));
        }
        koopa::ir::ValueKind::Return(ret) => {
            if let Some(val) = ret.value() {
                mark_local_value(val, data, set);
            }
        }
        koopa::ir::ValueKind::Integer(integer) => {}
        koopa::ir::ValueKind::ZeroInit(zero_init) => {}
        koopa::ir::ValueKind::Undef(undef) => {}
        koopa::ir::ValueKind::Aggregate(aggregate) => {
            aggregate
                .elems()
                .iter()
                .for_each(|&val| mark_local_value(val, data, set));
        }
        koopa::ir::ValueKind::FuncArgRef(func_arg_ref) => {}
        koopa::ir::ValueKind::BlockArgRef(block_arg_ref) => {}
        koopa::ir::ValueKind::Alloc(alloc) => {}
        koopa::ir::ValueKind::GlobalAlloc(global_alloc) => {
            mark_local_value(global_alloc.init(), data, set);
        }
    }
}

fn use_the(this: &ValueData) -> Vec<Value> {
    use koopa::ir::ValueKind::*;
    eprintln!("{:?}", this);
    match this.kind() {
        Integer(_) | Jump(_) | Branch(_) | Alloc(_) | GlobalAlloc(_) | ZeroInit(_) | Undef(_)
        | FuncArgRef(_) | BlockArgRef(_) => {
            vec![]
        }
        Aggregate(aggregate) => aggregate.elems().to_vec(),
        Load(load) => vec![load.src()],
        Store(store) => vec![store.value(), store.dest()],
        GetPtr(get_ptr) => vec![get_ptr.src()],
        GetElemPtr(get_elem_ptr) => vec![get_elem_ptr.src(), get_elem_ptr.index()],
        Binary(binary) => vec![binary.lhs(), binary.rhs()],
        Call(call) => todo!(),
        Return(ret) => ret.value().map(|x| vec![x]).unwrap_or_default(),
    }
}

impl FunctionPass for UnreachableBasicBlock {
    fn run_on(&mut self, func: Function, data: &mut FunctionData) {
        if data.layout().entry_bb().is_none() {
            return;
        }
        let mut id_allocator = IDAllocator::new();
        let (g, prece) = build_cfg(data, &mut id_allocator);

        let unreachable_bb = (1..id_allocator.cnt())
            // in-degree is zero.
            .filter(|id| prece[id].is_empty())
            .collect::<Vec<_>>();

        eprintln!("g:{:?}", g);
        eprintln!("prece:{:?}", prece);
        eprintln!("unreachable_bb:{:?}", unreachable_bb);

        for id in unreachable_bb {
            let bb = id_allocator.search_id(id);
            eprintln!("delete basic block: {:?}", bb);
            eprintln!("used_by check: {:?}", data.dfg().bb(bb).used_by());
            for val in data.dfg().bb(bb).used_by() {
                eprintln!("{:?}", data.dfg().value(*val).kind());
            }
            eprintln!("name: {:?}", data.dfg().bb(bb).name());
            let remove_list = data
                .dfg()
                .bb(bb)
                .used_by()
                .iter()
                .chain(
                    data.layout()
                        .bbs()
                        .node(&bb)
                        .unwrap()
                        .insts()
                        .iter()
                        .map(|(x, _)| x),
                )
                .copied()
                .collect::<Vec<_>>();
            for val in remove_list {
                dfs_remove(val, data, bb);
                // data.dfg_mut().remove_value(val);
            }

            data.layout_mut().bbs_mut().remove(&bb);
            data.dfg_mut().remove_bb(bb);
        }
    }
}

fn dfs_remove(val: Value, data: &mut FunctionData, bb: BasicBlock) {
    let mut remove_list = Vec::new();
    _dfs_remove(val, data, &mut remove_list);
    for val in remove_list.into_iter().rev() {
        eprintln!("remove:{val:?}");
        data.layout_mut().bb_mut(bb).insts_mut().remove(&val);
        data.dfg_mut().remove_value(val);
    }
}

fn _dfs_remove(val: Value, data: &FunctionData, remove_list: &mut Vec<Value>) {
    let vd = data.dfg().value(val);
    remove_list.push(val);
    for &child in vd.used_by().iter() {
        _dfs_remove(child, data, remove_list);
    }
}

impl ModulePass for DeadCodeElimination {
    fn run_on(&mut self, program: &mut Program) {
        // for (_func, data) in program.funcs_mut().iter_mut() {
        //     let mut fontier = VecDeque::new();
        //     let mut marker = HashSet::new();
        //     for (&_bb, node) in data.layout().bbs().iter() {
        //         let val = node.insts().back_key().unwrap();
        //         // TODO: Assert that end instruction is `br`, `ret` or `jump`
        //         fontier.push_back(*val);
        //         marker.insert(*val);
        //     }
        //     while !fontier.is_empty() {
        //         let inst = fontier.pop_front().unwrap();
        //         let val_data = data.dfg_mut().value(inst);
        //         for next in use_the(val_data).iter() {
        //             if marker.contains(next) {
        //                 continue;
        //             }
        //             let next_data = data.dfg_mut().value(*next);
        //             let used_by = next_data.used_by();
        //             if used_by.is_subset(&marker) {
        //                 fontier.push_back(*next);
        //                 marker.insert(*next);
        //             }
        //         }
        //     }
        //     let mut cursor_bb = data.layout_mut().bbs_mut().cursor_front_mut();
        //     while !cursor_bb.is_null() {
        //         let bb_node = cursor_bb.node_mut().unwrap();
        //         // for bb_node in data.layout().bbs().nodes() {
        //         let mut cursor_val = bb_node.insts_mut().cursor_front_mut();
        //         while !cursor_val.is_null() {
        //             if !marker.contains(cursor_val.key().unwrap()) {
        //                 cursor_val.remove_current();
        //             }
        //             cursor_val.move_next();
        //         }
        //         cursor_bb.move_next();
        //     }
        //     let mut cursor = data.layout().bbs().cursor_front_mut();
        //     while !cursor.is_null() {
        //         let node = cursor.node_mut().unwrap();
        //         for (&val, node) in node.insts_mut().iter() {
        //             if !marker.contains(&val) {
        //                 data.dfg_mut().remove_value(val);
        //             }
        //         }
        //         cursor.move_next();
        //     }
        // }
    }
}
