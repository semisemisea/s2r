#![allow(unused)]
use std::collections::{HashSet, VecDeque};

use koopa::{
    ir::{Function, FunctionData, Program, Value, entities::ValueData},
    opt::{FunctionPass, ModulePass},
};

pub struct DeadCodeElimination;

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

impl ModulePass for DeadCodeElimination {
    fn run_on(&mut self, program: &mut Program) {
        for (_func, data) in program.funcs_mut().iter_mut() {
            let mut fontier = VecDeque::new();
            let mut marker = HashSet::new();
            for (&_bb, node) in data.layout().bbs().iter() {
                let val = node.insts().back_key().unwrap();
                // TODO: Assert that end instruction is `br`, `ret` or `jump`
                fontier.push_back(*val);
                marker.insert(*val);
            }
            while !fontier.is_empty() {
                let inst = fontier.pop_front().unwrap();
                let val_data = data.dfg_mut().value(inst);
                for next in use_the(val_data).iter() {
                    if marker.contains(next) {
                        continue;
                    }
                    let next_data = data.dfg_mut().value(*next);
                    let used_by = next_data.used_by();
                    if used_by.is_subset(&marker) {
                        fontier.push_back(*next);
                        marker.insert(*next);
                    }
                }
            }
            let mut cursor_bb = data.layout_mut().bbs_mut().cursor_front_mut();
            while !cursor_bb.is_null() {
                let bb_node = cursor_bb.node_mut().unwrap();
                // for bb_node in data.layout().bbs().nodes() {
                let mut cursor_val = bb_node.insts_mut().cursor_front_mut();
                while !cursor_val.is_null() {
                    if !marker.contains(cursor_val.key().unwrap()) {
                        cursor_val.remove_current();
                    }
                    cursor_val.move_next();
                }
                cursor_bb.move_next();
            }
            // let mut cursor = data.layout().bbs().cursor_front_mut();
            // while !cursor.is_null() {
            //     let node = cursor.node_mut().unwrap();
            //     for (&val, node) in node.insts_mut().iter() {
            //         if !marker.contains(&val) {
            //             data.dfg_mut().remove_value(val);
            //         }
            //     }
            //     cursor.move_next();
            // }
        }
    }
}
