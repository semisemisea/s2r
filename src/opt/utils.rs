use std::collections::{HashMap, HashSet, hash_map::Entry};

use koopa::ir::{BasicBlock, Value, ValueKind};

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
