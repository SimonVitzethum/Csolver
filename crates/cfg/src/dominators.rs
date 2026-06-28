//! Dominator and post-dominator trees via the Cooper–Harvey–Kennedy
//! "A Simple, Fast Dominance Algorithm" (2001).
//!
//! The algorithm iterates an immediate-dominator approximation in reverse
//! postorder until it stabilizes. It is exact (a true fixpoint of the
//! dominance equations), not an over-approximation.

use crate::graph::Cfg;

/// A dominator (or post-dominator) tree over a dense node index space.
///
/// `idom[n]` is the immediate dominator of node `n`. `idom[root] == root`.
/// Unreachable nodes (from the tree's root) have `idom[n] == None`.
#[derive(Debug, Clone)]
struct DomTree {
    idom: Vec<Option<usize>>,
}

impl DomTree {
    /// Run the dominance fixpoint over the given adjacency. `root` is the start
    /// node; `pred[n]` lists the predecessors of `n` in the graph whose
    /// dominators we are computing.
    fn build(num_nodes: usize, root: usize, succ: &[Vec<usize>], pred: &[Vec<usize>]) -> DomTree {
        let mut idom = vec![None; num_nodes];
        if num_nodes == 0 {
            return DomTree { idom };
        }

        let post = postorder(num_nodes, root, succ);
        let mut post_num = vec![usize::MAX; num_nodes];
        for (i, &node) in post.iter().enumerate() {
            post_num[node] = i;
        }
        let rpo: Vec<usize> = post.iter().rev().copied().collect();

        idom[root] = Some(root);
        let mut changed = true;
        while changed {
            changed = false;
            for &b in &rpo {
                if b == root {
                    continue;
                }
                let mut new_idom: Option<usize> = None;
                for &p in &pred[b] {
                    if idom[p].is_some() {
                        new_idom = Some(match new_idom {
                            None => p,
                            Some(cur) => intersect(p, cur, &idom, &post_num),
                        });
                    }
                }
                if let Some(ni) = new_idom {
                    if idom[b] != Some(ni) {
                        idom[b] = Some(ni);
                        changed = true;
                    }
                }
            }
        }
        DomTree { idom }
    }

    /// Whether `a` dominates `b` (reflexively: every node dominates itself).
    /// `false` if `b` is unreachable from the root.
    fn dominates(&self, a: usize, b: usize) -> bool {
        if self.idom[b].is_none() {
            return false;
        }
        let mut x = b;
        loop {
            if x == a {
                return true;
            }
            match self.idom[x] {
                Some(i) if i != x => x = i,
                // Reached the root (idom == self) without meeting `a`.
                _ => return false,
            }
        }
    }
}

/// The classic "intersect" finger-walk over postorder numbers.
///
/// Every node the walk visits was processed in reverse-postorder before this
/// call, so its `idom` is `Some`; the `expect`s document that invariant.
#[allow(clippy::expect_used)]
fn intersect(mut a: usize, mut b: usize, idom: &[Option<usize>], post_num: &[usize]) -> usize {
    while a != b {
        while post_num[a] < post_num[b] {
            a = idom[a].expect("idom defined for processed node");
        }
        while post_num[b] < post_num[a] {
            b = idom[b].expect("idom defined for processed node");
        }
    }
    a
}

/// Iterative postorder DFS from `root` over `succ`.
fn postorder(num_nodes: usize, root: usize, succ: &[Vec<usize>]) -> Vec<usize> {
    let mut visited = vec![false; num_nodes];
    let mut order = Vec::new();
    let mut stack: Vec<(usize, usize)> = vec![(root, 0)];
    visited[root] = true;
    while let Some(&(node, next)) = stack.last() {
        if next < succ[node].len() {
            let s = succ[node][next];
            let top = stack.len() - 1;
            stack[top].1 += 1;
            if !visited[s] {
                visited[s] = true;
                stack.push((s, 0));
            }
        } else {
            order.push(node);
            stack.pop();
        }
    }
    order
}

/// The dominator tree of a [`Cfg`], rooted at the entry.
#[derive(Debug, Clone)]
pub struct Dominators {
    tree: DomTree,
}

impl Dominators {
    /// Compute dominators for `cfg`.
    pub fn new(cfg: &Cfg) -> Dominators {
        let n = cfg.node_count();
        let succ: Vec<Vec<usize>> = (0..n).map(|i| cfg.successors(i).to_vec()).collect();
        let pred: Vec<Vec<usize>> = (0..n).map(|i| cfg.predecessors(i).to_vec()).collect();
        Dominators {
            tree: DomTree::build(n, cfg.entry(), &succ, &pred),
        }
    }

    /// The immediate dominator of `node` (the entry's idom is itself).
    /// `None` if `node` is unreachable.
    pub fn immediate_dominator(&self, node: usize) -> Option<usize> {
        self.tree.idom[node]
    }

    /// Whether `a` dominates `b` (reflexive).
    pub fn dominates(&self, a: usize, b: usize) -> bool {
        self.tree.dominates(a, b)
    }

    /// Whether `a` *strictly* dominates `b` (`a != b` and `a` dominates `b`).
    pub fn strictly_dominates(&self, a: usize, b: usize) -> bool {
        a != b && self.dominates(a, b)
    }
}

/// The post-dominator tree of a [`Cfg`].
///
/// Built by computing dominators on the reverse graph rooted at a synthetic
/// exit node that all real exits (returns / `unreachable`) flow into. The
/// synthetic node has index `cfg.node_count()`.
#[derive(Debug, Clone)]
pub struct PostDominators {
    tree: DomTree,
    virtual_exit: usize,
}

impl PostDominators {
    /// Compute post-dominators for `cfg`.
    pub fn new(cfg: &Cfg) -> PostDominators {
        let n = cfg.node_count();
        let m = n + 1;
        let x = n; // synthetic exit
        let mut rev_succ = vec![Vec::new(); m];
        let mut rev_pred = vec![Vec::new(); m];
        // Reverse every real edge a -> b into b -> a. `a` is both a node id
        // (for `cfg.successors`) and an index into the reverse arrays.
        #[allow(clippy::needless_range_loop)]
        for a in 0..n {
            for &b in cfg.successors(a) {
                rev_succ[b].push(a);
                rev_pred[a].push(b);
            }
        }
        // Connect the synthetic exit to every real exit.
        for e in cfg.exits() {
            rev_succ[x].push(e);
            rev_pred[e].push(x);
        }
        PostDominators {
            tree: DomTree::build(m, x, &rev_succ, &rev_pred),
            virtual_exit: x,
        }
    }

    /// The index of the synthetic exit node.
    pub fn virtual_exit(&self) -> usize {
        self.virtual_exit
    }

    /// The immediate post-dominator of `node`, or `None` if it is the synthetic
    /// exit (i.e. `node` only post-dominates to program exit) or unreachable
    /// from any exit.
    pub fn immediate_post_dominator(&self, node: usize) -> Option<usize> {
        match self.tree.idom[node] {
            Some(i) if i == self.virtual_exit => None,
            other => other,
        }
    }

    /// Whether `a` post-dominates `b`.
    pub fn post_dominates(&self, a: usize, b: usize) -> bool {
        self.tree.dominates(a, b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use csolver_ir::{BasicBlock, BlockId, FuncId, Function, Operand, RegId, Terminator, Type};

    /// Diamond: 0 -> {1, 2} -> 3.
    fn diamond() -> Function {
        let blk = |id: u32, term: Terminator| BasicBlock::new(BlockId(id), term);
        let to = |id: u32| Terminator::Br {
            target: BlockId(id),
            args: vec![],
        };
        let bb0 = blk(
            0,
            Terminator::CondBr {
                cond: Operand::Reg(RegId(0)),
                then_blk: BlockId(1),
                then_args: vec![],
                else_blk: BlockId(2),
                else_args: vec![],
            },
        );
        let bb1 = blk(1, to(3));
        let bb2 = blk(2, to(3));
        let bb3 = blk(3, Terminator::Return(None));
        Function {
            id: FuncId(0),
            name: "diamond".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2, bb3],
            entry: BlockId(0),
        }
    }

    #[test]
    fn diamond_dominators() {
        let f = diamond();
        let cfg = Cfg::from_function(&f);
        let dom = Dominators::new(&cfg);
        // entry dominates everything.
        for n in 0..4 {
            assert!(dom.dominates(0, n), "0 should dominate {n}");
        }
        // 1 and 2 do NOT dominate the merge 3 (you can reach 3 via the other).
        assert!(!dom.dominates(1, 3));
        assert!(!dom.dominates(2, 3));
        // idom of the merge is the entry, not either branch.
        assert_eq!(dom.immediate_dominator(3), Some(0));
        assert_eq!(dom.immediate_dominator(1), Some(0));
        assert!(dom.strictly_dominates(0, 3));
        assert!(!dom.strictly_dominates(3, 3));
    }

    #[test]
    fn diamond_post_dominators() {
        let f = diamond();
        let cfg = Cfg::from_function(&f);
        let pdom = PostDominators::new(&cfg);
        // The merge post-dominates everything that must flow through it.
        assert!(pdom.post_dominates(3, 0));
        assert!(pdom.post_dominates(3, 1));
        assert!(pdom.post_dominates(3, 2));
        // The branches do not post-dominate the entry.
        assert!(!pdom.post_dominates(1, 0));
        assert!(!pdom.post_dominates(2, 0));
        // ipdom of entry is the merge block.
        assert_eq!(pdom.immediate_post_dominator(0), Some(3));
    }

    /// Self-loop: 0 -> 1 -> 1 (back edge) and 1 -> 2.
    fn with_loop() -> Function {
        let bb0 = BasicBlock::new(
            BlockId(0),
            Terminator::Br {
                target: BlockId(1),
                args: vec![],
            },
        );
        let bb1 = BasicBlock::new(
            BlockId(1),
            Terminator::CondBr {
                cond: Operand::Reg(RegId(0)),
                then_blk: BlockId(1),
                then_args: vec![],
                else_blk: BlockId(2),
                else_args: vec![],
            },
        );
        let bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));
        Function {
            id: FuncId(0),
            name: "loop".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2],
            entry: BlockId(0),
        }
    }

    #[test]
    fn loop_dominators() {
        let f = with_loop();
        let cfg = Cfg::from_function(&f);
        let dom = Dominators::new(&cfg);
        assert!(dom.dominates(1, 1));
        assert!(dom.dominates(0, 2));
        assert_eq!(dom.immediate_dominator(2), Some(1));
        assert_eq!(dom.immediate_dominator(1), Some(0));
    }
}
