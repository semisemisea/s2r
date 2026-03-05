use std::collections::HashMap;

use koopa::{
    ir::{BinaryOp, FunctionData, Value, ValueKind},
    opt::FunctionPass,
};

use crate::opt::utils::{self, BIDAlloc, BId, DomTree, IDAllocator, VIDAlloc};

pub struct GlobalValueNumbering;

type ValueNumber = usize;

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
enum ValueType {
    Const(i32),
    // in the SSA-form, everything is constant.
    // Here variable means: We don't know the value at comptime.
    Var(ValueNumber),
    Binary {
        op: BinaryOp,
        lhs: ValueNumber,
        rhs: ValueNumber,
    },
    GetPtr {
        source: ValueNumber,
        index: ValueNumber,
    },
    GetElemPtr {
        source: ValueNumber,
        index: ValueNumber,
    },
    // Call can also be seen as the same in certain condition.
    // This can be identified through:
    // - If the callee is pure function
    // - If the arguments are all the same.
    // But in simplified GVN pass, we will ingnore this

    // Call {
    //     callee: koopa::ir::Function,
    //     args: Vec<ValueNumber>,
    // },
}

fn is_op_commutative(op: BinaryOp) -> bool {
    matches!(
        op,
        BinaryOp::Add
            | BinaryOp::Mul
            | BinaryOp::NotEq
            | BinaryOp::And
            | BinaryOp::Or
            | BinaryOp::Xor
            | BinaryOp::Eq
    )
}

impl ValueType {
    fn build_from_value(
        data: &FunctionData,
        value: Value,
        val_id: &mut VIDAlloc,
    ) -> Option<ValueType> {
        match data.dfg().value(value).kind() {
            ValueKind::Integer(integer) => Some(Self::Const(integer.value())),
            ValueKind::Load(..)
            | ValueKind::Call(..)
            | ValueKind::Alloc(..)
            | ValueKind::BlockArgRef(..)
            | ValueKind::FuncArgRef(..)
            | ValueKind::Aggregate(..)
            | ValueKind::Undef(..)
            | ValueKind::ZeroInit(..) => Some(Self::Var(val_id.check_or_alloc_id_same(value))),
            ValueKind::GlobalAlloc(_global_alloc) => unreachable!(),
            ValueKind::Store(_store) => None,
            ValueKind::GetPtr(get_ptr) => Some(Self::GetPtr {
                source: val_id.check_or_alloc_id_same(get_ptr.src()),
                index: val_id.check_or_alloc_id_same(get_ptr.index()),
            }),
            ValueKind::GetElemPtr(get_elem_ptr) => Some(Self::GetElemPtr {
                source: val_id.check_or_alloc_id_same(get_elem_ptr.src()),
                index: val_id.check_or_alloc_id_same(get_elem_ptr.index()),
            }),
            ValueKind::Binary(binary) => {
                let lhs = val_id.check_or_alloc_id_same(binary.lhs());
                let rhs = val_id.check_or_alloc_id_same(binary.rhs());
                if is_op_commutative(binary.op()) {
                    Some(Self::Binary {
                        op: binary.op(),
                        lhs: lhs.min(rhs),
                        rhs: rhs.max(lhs),
                    })
                } else {
                    Some(Self::Binary {
                        op: binary.op(),
                        lhs,
                        rhs,
                    })
                }
            }
            ValueKind::Return(..) | ValueKind::Jump(..) | ValueKind::Branch(..) => None,
        }
    }
}

type Map = HashMap<ValueType, Value>;

struct LayeredMap(Vec<Map>);

impl LayeredMap {
    #[inline]
    fn new() -> LayeredMap {
        LayeredMap(Default::default())
    }

    #[inline]
    fn new_scope(&mut self) {
        self.0.push(HashMap::default())
    }

    #[inline]
    fn pop_scope(&mut self) -> Option<Map> {
        self.0.pop()
    }

    fn get(&self, key: &ValueType) -> Option<Value> {
        self.0
            .iter()
            .rev()
            .find_map(|scope| scope.get(key).copied())
    }

    fn insert(&mut self, key: ValueType, value: Value) -> Option<Value> {
        self.0.last_mut().unwrap().insert(key, value)
    }
}

impl FunctionPass for GlobalValueNumbering {
    fn run_on(&mut self, _func: koopa::ir::Function, data: &mut FunctionData) {
        // function declaration. we just have to skip it.
        if data.layout().entry_bb().is_none() {
            return;
        }
        eprintln!("----------------------------------------------------");
        eprintln!("gvn start: {:?}", data.name());

        let mut bb_alloc = IDAllocator::new(1);
        let mut val_alloc = IDAllocator::new(1);
        let mut layered_type_map = LayeredMap::new();
        let (graph, prece) = utils::build_cfg_both(data, &mut bb_alloc);

        // entry bb must be the first to be allocated.
        assert!(bb_alloc.get_id(&data.layout().entry_bb().unwrap()) == 0);

        let rpo_path = utils::rpo_path(&graph);
        let idom_map = utils::idom(&prece, &rpo_path);
        let donimnace_tree = utils::build_dominance_tree(&idom_map, rpo_path.len());

        fn dfs(
            bb_id: BId,
            dom_tree: &DomTree,
            layered_type_map: &mut LayeredMap,
            val_alloc: &mut VIDAlloc,
            bb_alloc: &mut BIDAlloc,
            data: &mut FunctionData,
        ) {
            layered_type_map.new_scope();
            let bb = bb_alloc.search_id(bb_id);

            let mut to_replace = Vec::new();
            let iter = data
                .dfg()
                .bb(bb)
                .params()
                .iter()
                .chain(data.layout().bbs().node(&bb).unwrap().insts().keys())
                .copied();

            for val in iter {
                if let Some(expr) = ValueType::build_from_value(data, val, val_alloc) {
                    eprintln!("epxr: {:?}", expr);
                    if let Some(rep_with) = layered_type_map.get(&expr) {
                        to_replace.push((val, rep_with))
                    } else {
                        layered_type_map.insert(expr, val);
                    }
                }
            }

            for (rep, rep_with) in to_replace {
                utils::visit_and_replace(data, rep, rep_with);
            }

            dom_tree[bb_id].iter().for_each(|&child| {
                dfs(child, dom_tree, layered_type_map, val_alloc, bb_alloc, data)
            });

            layered_type_map.pop_scope();
        }
        dfs(
            0,
            &donimnace_tree,
            &mut layered_type_map,
            &mut val_alloc,
            &mut bb_alloc,
            data,
        );

        eprintln!("----------------------------------------------------");
    }
}
