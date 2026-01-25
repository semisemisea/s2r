use std::collections::{HashMap, HashSet, VecDeque};

use crate::opt::utils::{self, BId, CFGGraph, IDAllocator, VId};

use koopa::{
    ir::{
        BasicBlock, FunctionData, Value, ValueKind,
        builder::{LocalInstBuilder, ValueBuilder, ValueInserter},
        values::BlockArgRef,
    },
    opt::FunctionPass,
};

pub struct SSATransform;

// you can replace hashset with more efficient bitset;
type Set = HashSet<BId>;

type GPath = Vec<BId>;

type IDomMap = Vec<BId>;

// not all basic block has it's frontier so we can use HashMap instead of Vec
type Frontier = HashMap<BId, HashSet<BId>>;

type ValUsage = Vec<Vec<VId>>;

type DomTree = Vec<Vec<BId>>;

// variable(vid) is insert as basic block(bbid) at index(usize)
type Index = usize;
type InsertTable = Vec<Vec<(VId, Index)>>;

// Recording each variable version while doing SSA elimination.
type ValStack = Vec<Vec<Value>>;

impl FunctionPass for SSATransform {
    fn run_on(&mut self, func: koopa::ir::Function, data: &mut koopa::ir::FunctionData) {
        // function declaration. skip.
        if data.layout().entry_bb().is_none() {
            return;
        }
        eprintln!("----------------------------------");
        eprintln!("function: {func:?}");
        eprintln!("name: {}", data.name());

        // Discretization. Assign each unique basic block with natural number 0..n
        let mut bb_id = IDAllocator::new();

        // get graph and reverse graph
        let (graph, prece) = utils::build_cfg(data, &mut bb_id);

        // entry_bb must get 0 for id
        assert!(bb_id.get_id(data.layout().entry_bb().unwrap()) == 0);

        let rpo_path = rpo_path(&graph);
        // start from entry_bb so first element of RPO is zero
        assert!(rpo_path[0] == 0);

        // get immediate dominator of each block
        // dominance is a partial order.
        // immediate dominance means partial order coverage
        let idom_map = idom(&prece, &rpo_path);

        // for dominance, its hasse diagram is a tree
        let donimnace_tree = build_dominance_tree(&idom_map);

        // then we can do frontier analysis
        let dom_frontier = dominance_analysis(&bb_id, &prece, &idom_map);

        // find out where are varaibles defined.
        let mut val_id = IDAllocator::new();
        let val_usage = variable_analysis(&mut val_id, &mut bb_id, data);

        // variable(vid) is insert as basic block(bbid) at index(usize)
        let mut insert_table = vec![vec![]; bb_id.cnt()];

        for (vid, frontiers) in val_usage.iter().enumerate().flat_map(|(vid, def_bbs)| {
            def_bbs
                .iter()
                .filter_map(|def_bb| dom_frontier.get(def_bb))
                .map(move |frontier| (vid, frontier))
        }) {
            let mut worked = frontiers.clone();
            let mut work_queue = VecDeque::with_capacity(frontiers.len());
            for &front in frontiers.iter() {
                work_queue.push_back(front);
            }

            // eprintln!("default work_queue {work_queue:?}");

            while !work_queue.is_empty() {
                let front = work_queue.pop_front().unwrap();
                // eprintln!("visited {front}");
                let bb = bb_id.search_id(front);
                let index = data.dfg().bb(bb).params().len();

                let var_ty = utils::alloc_ty(val_id.search_id(vid as _), data).clone();

                let arg = BlockArgRef::new_data(index, var_ty);
                insert_table[front].push((vid, index));
                let new_block_arg_ref = data.dfg_mut().new_value().insert_value(arg);
                data.dfg_mut()
                    .set_value_name(new_block_arg_ref, Some(format!("%vid_{}", vid)));

                data.dfg_mut()
                    .bb_mut(bb)
                    .params_mut()
                    .push(new_block_arg_ref);

                if let Some(sub_frontiers) = dom_frontier.get(&front) {
                    for sub_front in sub_frontiers.iter() {
                        if !worked.contains(sub_front) {
                            worked.insert(*sub_front);
                            work_queue.push_back(*sub_front);
                        } else {
                            eprintln!("detected loop and correctly stop.");
                            // eprintln!("sub front {sub_front}");
                            // eprintln!("worked {worked:?}");
                        }
                    }
                }
            }
        }

        let mut val_stack = vec![vec![]; val_id.cnt()];
        let mut remove_list = Vec::new();

        dfs(
            0,
            &donimnace_tree,
            &mut val_stack,
            &val_id,
            &bb_id,
            data,
            &insert_table,
            &mut remove_list,
        );

        remove_list.into_iter().rev().for_each(|(val, bb)| {
            let vd = data.dfg().value(val);
            eprintln!("delete check {:?}, {:?}", vd.kind(), vd.used_by());
            data.layout_mut().bb_mut(bb).insts_mut().remove(&val);
            data.dfg_mut().remove_value(val);
        });

        eprintln!();
        eprintln!("showing");
        eprintln!("graph: {graph:?}");
        eprintln!("rpo_path: {rpo_path:?}");
        eprintln!("idom_map: {idom_map:?}");
        eprintln!("dominance_frontier: {dom_frontier:?}");
        eprintln!("val_usage: {val_usage:?}");
        eprintln!("dominance_tree: {donimnace_tree:?}");
        eprintln!("finished");
        eprintln!("----------------------------------");
        eprintln!();
    }
}

#[allow(clippy::too_many_arguments)]
fn dfs(
    node: BId,
    tree: &DomTree,
    st: &mut ValStack,
    val_id: &IDAllocator<Value, VId>,
    bb_id: &IDAllocator<BasicBlock, BId>,
    data: &mut koopa::ir::FunctionData,
    insert_table: &InsertTable,
    remove_list: &mut Vec<(Value, BasicBlock)>,
) {
    let mut history = Vec::new();
    // Step 1:   Update `st` if block arguments update the value.
    let bb = bb_id.search_id(node);
    let bb_data = data.dfg().bb(bb);
    for &(vid, idx) in insert_table[node].iter() {
        st[vid].push(bb_data.params()[idx]);
        history.push(vid);
    }

    // Step 2:   Traverse the instruction list and find `alloc`, `store` and `load`.
    let bb_data = data.layout().bbs().node(&bb_id.search_id(node)).unwrap();
    let values = bb_data.insts().iter().map(|(&x, _)| x).collect::<Vec<_>>();
    for val in values {
        let val_data = data.dfg().value(val);
        // Step 2.3: Delete `load` and replace every use of `load` with value of variable.
        // Step 2.4: For `jump` and `branch`, update its arguments.
        match val_data.kind() {
            // Step 2.1: Straight delete `alloc`.
            // `alloc` can only be deleted when all `load` and `store` is deleted.
            ValueKind::Alloc(..) => {
                remove_list.push((val, bb));
            }
            // Step 2.2: Update the value in stack with corresponding variable if we met `store`.
            ValueKind::Store(store) => {
                let dest_id = val_id.get_id(store.dest());
                st[dest_id].push(store.value());
                history.push(dest_id);

                eprintln!("check used_by: {:?}", val_data.used_by());
                remove_list.push((val, bb));
            }
            ValueKind::Load(load) => {
                let rep_with = *st[val_id.get_id(load.src())].last().unwrap();
                let list = val_data.used_by().iter().copied().collect::<Vec<_>>();
                for used_by in list {
                    visit_and_replace(data, used_by, val, rep_with);
                }
                remove_list.push((val, bb));
            }
            ValueKind::Jump(jump) => {
                let target = jump.target();
                let target_id = bb_id.get_id(target);
                let args = jump
                    .args()
                    .iter()
                    .chain(
                        insert_table[target_id]
                            .iter()
                            .map(|&(vid, _)| st[vid].last().unwrap()),
                    )
                    .copied()
                    .collect();
                data.dfg_mut()
                    .replace_value_with(val)
                    .jump_with_args(target, args);
            }
            ValueKind::Branch(branch) => {
                let cond = branch.cond();
                let true_bb = branch.true_bb();
                let true_bb_id = bb_id.get_id(true_bb);
                let true_args = branch
                    .true_args()
                    .iter()
                    .chain(
                        insert_table[true_bb_id]
                            .iter()
                            .map(|&(vid, _)| st[vid].last().unwrap()),
                    )
                    .copied()
                    .collect();
                let false_bb = branch.false_bb();
                let false_bb_id = bb_id.get_id(false_bb);
                let false_args = branch
                    .false_args()
                    .iter()
                    .chain(
                        insert_table[false_bb_id]
                            .iter()
                            .map(|&(vid, _)| st[vid].last().unwrap()),
                    )
                    .copied()
                    .collect();
                data.dfg_mut()
                    .replace_value_with(val)
                    .branch_with_args(cond, true_bb, false_bb, true_args, false_args);
            }
            _ => {}
        }
    }

    // Step 3: Recursively call the function.
    tree[node].iter().for_each(|&child| {
        dfs(
            child,
            tree,
            st,
            val_id,
            bb_id,
            data,
            insert_table,
            remove_list,
        )
    });

    for id in history {
        st[id].pop();
    }
}

fn visit_and_replace(data: &mut FunctionData, used_by: Value, rep: Value, rep_with: Value) {
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
            if data.dfg().value_eq(store.value(), rep) {
                let dest = store.dest();
                data.dfg_mut()
                    .replace_value_with(used_by)
                    .store(rep_with, dest);
            }
        }
        ValueKind::GetPtr(get_ptr) => {
            if data.dfg().value_eq(get_ptr.index(), rep) {
                let src = get_ptr.src();
                data.dfg_mut()
                    .replace_value_with(used_by)
                    .get_ptr(src, rep_with);
            }
        }
        ValueKind::GetElemPtr(get_elem_ptr) => {
            if data.dfg().value_eq(get_elem_ptr.index(), rep) {
                let src = get_elem_ptr.src();
                data.dfg_mut()
                    .replace_value_with(used_by)
                    .get_ptr(src, rep_with);
            }
        }
        ValueKind::Binary(binary) => {
            let lhs = if data.dfg().value_eq(binary.lhs(), rep) {
                rep_with
            } else {
                binary.lhs()
            };
            let rhs = if data.dfg().value_eq(binary.rhs(), rep) {
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
            let true_args = branch
                .true_args()
                .iter()
                .map(|&val| {
                    if data.dfg().value_eq(val, rep) {
                        rep_with
                    } else {
                        val
                    }
                })
                .collect();
            let false_args = branch
                .false_args()
                .iter()
                .map(|&val| {
                    if data.dfg().value_eq(val, rep) {
                        rep_with
                    } else {
                        val
                    }
                })
                .collect();
            let (cond, true_bb, false_bb) = (branch.cond(), branch.true_bb(), branch.false_bb());
            data.dfg_mut()
                .replace_value_with(used_by)
                .branch_with_args(cond, true_bb, false_bb, true_args, false_args);
        }
        ValueKind::Jump(jump) => {
            let args = jump
                .args()
                .iter()
                .map(|&val| {
                    if data.dfg().value_eq(val, rep) {
                        rep_with
                    } else {
                        val
                    }
                })
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
                .map(|&val| {
                    if data.dfg().value_eq(val, rep) {
                        rep_with
                    } else {
                        val
                    }
                })
                .collect();
            let callee = call.callee();
            data.dfg_mut()
                .replace_value_with(used_by)
                .call(callee, args);
        }
        ValueKind::Return(ret) => {
            if let Some(ret_val) = ret.value()
                && data.dfg().value_eq(ret_val, rep)
            {
                data.dfg_mut()
                    .replace_value_with(used_by)
                    .ret(Some(rep_with));
            }
        }
    }
}

pub fn variable_analysis(
    val_id: &mut IDAllocator<Value, VId>,
    bb_id: &mut IDAllocator<BasicBlock, BId>,
    data: &FunctionData,
) -> ValUsage {
    let mut val_usage = ValUsage::new();

    // use iterator to get rid of nested for-loop
    // you don't have to care what does the iterator chain do.
    // only to know it return these things in tuple:
    //
    //  value handle     kind        which basic block it belongs to.
    for (val, val_kind, bb) in data
        .layout()
        .bbs()
        .iter()
        .flat_map(|(&bb, node)| node.insts().iter().zip(std::iter::repeat(bb)))
        .map(|((&val, _), bb)| (val, data.dfg().value(val).kind(), bb))
    {
        match val_kind {
            ValueKind::Alloc(..) => {
                // TODO: ssa do nothing when allocate a array.
                let ty = utils::alloc_ty(val, data);
                val_id.check_or_alloca(val);
                val_usage.push(Vec::new());
            }
            ValueKind::Store(store) => {
                let vid = val_id.get_id(store.dest());
                let bbid = bb_id.get_id(bb);
                val_usage[vid].push(bbid);
            }
            _ => {}
        }
    }

    val_usage
}

pub fn dominance_analysis(
    id_alloca: &IDAllocator<BasicBlock, BId>,
    prece: &CFGGraph,
    idom_map: &IDomMap,
) -> Frontier {
    let mut dominance_frontier = Frontier::new();

    // algorithm I looked up from wikipedia.
    for bb in 0..id_alloca.cnt() {
        if prece[&bb].len() >= 2 {
            for &pre in prece[&bb].iter() {
                let mut runner = pre;
                while runner != idom_map[bb] {
                    dominance_frontier.entry(runner).or_default().insert(bb);
                    runner = idom_map[runner];
                }
            }
        }
    }

    dominance_frontier
}

fn rpo_path(g: &CFGGraph) -> GPath {
    let mut path = Vec::new();
    let mut visited = Set::new();
    fn dfs(node: usize, g: &CFGGraph, ans: &mut GPath, visited: &mut Set) {
        visited.insert(node);
        for &succ in g[&node].iter() {
            if !visited.contains(&succ) {
                dfs(succ, g, ans, visited);
            }
        }
        ans.push(node);
    }
    dfs(0, g, &mut path, &mut visited);
    path.reverse();
    path
}

fn idom(prede: &CFGGraph, rpo: &[BId]) -> IDomMap {
    let mut map = IDomMap::new();
    map.resize(rpo.len(), usize::MAX);
    let mut rpo_idx = vec![0; rpo.len()];
    for (i, &id) in rpo.iter().enumerate() {
        rpo_idx[id] = i;
    }

    map[0] = 0;

    let mut converged = false;
    while !converged {
        converged = true;
        for node in &rpo[1..] {
            let mut it = prede[node].iter();
            let mut new_idom = *it.find(|&&x| map[x] != usize::MAX).unwrap();
            for &other_node in it.filter(|&&x| map[x] != usize::MAX) {
                new_idom = lca(new_idom, other_node, &map, rpo);
            }
            if map[*node] != new_idom {
                map[*node] = new_idom;
                converged = false;
            }
        }
    }
    map
}

fn build_dominance_tree(idom_map: &IDomMap) -> DomTree {
    let mut ret = vec![vec![]; idom_map.len()];
    // remember that idom_map we make `idom_map[0] = 0`
    // that is not allowed in a tree (no loop or ring)
    for (vid, &pa) in idom_map.iter().enumerate().skip(1) {
        ret[pa].push(vid);
    }
    ret
}

fn lca(n1: BId, n2: BId, map: &IDomMap, rpo_idx: &[BId]) -> BId {
    let mut p1 = n1;
    let mut p2 = n2;
    while p1 != p2 {
        while rpo_idx[p1] > rpo_idx[p2] {
            p1 = map[p1];
        }
        while rpo_idx[p1] < rpo_idx[p2] {
            p2 = map[p2];
        }
    }
    p1
}
