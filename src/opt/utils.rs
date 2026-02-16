use std::collections::{HashMap, hash_map::Entry};

use koopa::ir::{BasicBlock, FunctionData, Value, ValueKind, builder::LocalInstBuilder};

#[derive(Debug)]
pub struct IDAllocator<Key, Id> {
    id_pos: HashMap<Key, Id>,
    id_neg: HashMap<Id, Key>,
    cnt: Id,
}

impl<K, I> IDAllocator<K, I>
where
    K: Eq + std::hash::Hash + Copy,
    I: std::ops::AddAssign<usize> + Default + Copy + Eq + std::hash::Hash,
{
    pub fn new() -> IDAllocator<K, I> {
        Self {
            id_pos: HashMap::new(),
            id_neg: HashMap::new(),
            cnt: I::default(),
        }
    }

    pub fn check_or_alloca(&mut self, key: K) -> I {
        match self.id_pos.entry(key) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(..) => {
                self.id_pos.insert(key, self.cnt);
                self.id_neg.insert(self.cnt, key);
                let ret = self.cnt;
                self.cnt += 1usize;
                ret
            }
        }
    }

    pub fn get_id_safe(&self, key: K) -> Option<&I> {
        self.id_pos.get(&key)
    }

    pub fn get_id(&self, key: K) -> I {
        *self.id_pos.get(&key).unwrap()
    }

    pub fn search_id(&self, id: I) -> K {
        *self.id_neg.get(&id).unwrap()
    }

    pub fn cnt(&self) -> I {
        self.cnt
    }
}

// Value ID
pub type VId = usize;

// Basic Block ID
pub type BId = usize;

// Control Flow Graph
// Each Vertex is a basic block
pub type CFGGraph = HashMap<BId, Vec<BId>>;

// TODO: We can do cache there.
pub fn build_cfg(
    data: &koopa::ir::FunctionData,
    id_alloc: &mut IDAllocator<BasicBlock, BId>,
) -> (CFGGraph, CFGGraph) {
    // <a,b> in set E when a can directly jump to b
    let mut graph = CFGGraph::new();
    // reverse graph
    let mut prece = CFGGraph::new();
    for (&bb, node) in data.layout().bbs().iter() {
        let id = id_alloc.check_or_alloca(bb);
        let &val = node.insts().back_key().unwrap();
        prece.entry(id).or_default();
        let val_data = data.dfg().value(val);
        match val_data.kind() {
            ValueKind::Jump(jump) => {
                let j_id = id_alloc.check_or_alloca(jump.target());
                graph.entry(id).or_default().push(j_id);

                prece.entry(j_id).or_default().push(id);
            }
            ValueKind::Branch(branch) => {
                let t_id = id_alloc.check_or_alloca(branch.true_bb());
                let f_id = id_alloc.check_or_alloca(branch.false_bb());
                graph.entry(id).or_default().push(t_id);
                graph.entry(id).or_default().push(f_id);

                prece.entry(t_id).or_default().push(id);
                prece.entry(f_id).or_default().push(id);
            }
            ValueKind::Return(_) => {
                graph.entry(id).or_default();
            }
            // every basic block is end with three instructions above.
            _ => unreachable!(),
        }
    }
    (graph, prece)
}

#[inline]
pub fn get_terminator_inst(data: &FunctionData, bb: BasicBlock) -> Value {
    *data
        .layout()
        .bbs()
        .node(&bb)
        .unwrap()
        .insts()
        .back_key()
        .unwrap()
}

#[inline]
pub fn is_terminator_inst(data: &FunctionData, inst: Value) -> bool {
    matches!(
        data.dfg().value(inst).kind(),
        ValueKind::Return(..) | ValueKind::Jump(..) | ValueKind::Branch(..)
    )
}

pub fn alloc_ty(val: Value, data: &koopa::ir::FunctionData) -> &koopa::ir::Type {
    use koopa::ir::TypeKind;
    let val_data = data.dfg().value(val);
    assert!(matches!(val_data.kind(), ValueKind::Alloc(..)));
    // alloc should generate a pointer to its target type.
    let TypeKind::Pointer(pointee) = val_data.ty().kind() else {
        unreachable!()
    };
    pointee
}

pub fn visit_and_replace(data: &mut FunctionData, used_by: Value, rep: Value, rep_with: Value) {
    let rep_val_data = data.dfg().value(used_by);
    #[allow(unused_variables)]
    match rep_val_data.kind() {
        ValueKind::Integer(integer) => todo!(),
        ValueKind::ZeroInit(zero_init) => todo!(),
        ValueKind::Undef(undef) => todo!(),
        ValueKind::Aggregate(aggregate) => todo!(),
        ValueKind::FuncArgRef(func_arg_ref) => todo!(),
        ValueKind::BlockArgRef(block_arg_ref) => todo!(),
        ValueKind::Alloc(alloc) => todo!(),
        ValueKind::GlobalAlloc(global_alloc) => todo!(),
        ValueKind::Load(load) => todo!(),
        ValueKind::Store(store) => {
            if store.value() == rep {
                let dest = store.dest();
                data.dfg_mut()
                    .replace_value_with(used_by)
                    .store(rep_with, dest);
            }
        }
        ValueKind::GetPtr(get_ptr) => {
            if get_ptr.index() == rep {
                let src = get_ptr.src();
                data.dfg_mut()
                    .replace_value_with(used_by)
                    .get_ptr(src, rep_with);
            }
        }
        ValueKind::GetElemPtr(get_elem_ptr) => {
            if get_elem_ptr.index() == rep {
                let src = get_elem_ptr.src();
                data.dfg_mut()
                    .replace_value_with(used_by)
                    .get_elem_ptr(src, rep_with);
            }
        }
        ValueKind::Binary(binary) => {
            let lhs = if binary.lhs() == rep {
                rep_with
            } else {
                binary.lhs()
            };
            let rhs = if binary.rhs() == rep {
                rep_with
            } else {
                binary.rhs()
            };
            let op = binary.op();
            data.dfg_mut()
                .replace_value_with(used_by)
                .binary(op, lhs, rhs);
        }
        ValueKind::Branch(branch) => {
            let cond = if branch.cond() == rep {
                rep_with
            } else {
                branch.cond()
            };
            if let ValueKind::Integer(int) = data.dfg().value(cond).kind() {
                let (target, args) = if int.value() == 0 {
                    (branch.false_bb(), branch.false_args().to_vec())
                } else {
                    (branch.true_bb(), branch.true_args().to_vec())
                };
                data.dfg_mut()
                    .replace_value_with(used_by)
                    .jump_with_args(target, args);
            } else {
                let true_args = branch
                    .true_args()
                    .iter()
                    .map(|&val| if val == rep { rep_with } else { val })
                    .collect();
                let false_args = branch
                    .false_args()
                    .iter()
                    .map(|&val| if val == rep { rep_with } else { val })
                    .collect();
                let (true_bb, false_bb) = (branch.true_bb(), branch.false_bb());
                data.dfg_mut()
                    .replace_value_with(used_by)
                    .branch_with_args(cond, true_bb, false_bb, true_args, false_args);
            }
        }
        ValueKind::Jump(jump) => {
            let args = jump
                .args()
                .iter()
                .map(|&val| if val == rep { rep_with } else { val })
                .collect();
            let target = jump.target();
            data.dfg_mut()
                .replace_value_with(used_by)
                .jump_with_args(target, args);
        }
        ValueKind::Call(call) => {
            let args = call
                .args()
                .iter()
                .map(|&val| if val == rep { rep_with } else { val })
                .collect();
            let callee = call.callee();
            data.dfg_mut()
                .replace_value_with(used_by)
                .call(callee, args);
        }
        ValueKind::Return(ret) => {
            if let Some(ret_val) = ret.value()
                && ret_val == rep
            {
                data.dfg_mut()
                    .replace_value_with(used_by)
                    .ret(Some(rep_with));
            }
        }
    }
}
