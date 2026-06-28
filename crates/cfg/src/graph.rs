//! The control-flow graph: a dense index space over a function's blocks with
//! successor/predecessor adjacency and a reverse-postorder traversal.

use csolver_ir::{BlockId, Function};
use std::collections::HashMap;

/// A control-flow graph derived from an MSIR [`Function`].
///
/// Nodes are dense indices `0..node_count()`. Index 0 is not special; the entry
/// is [`Cfg::entry`]. Use [`Cfg::block_id`] / [`Cfg::index_of`] to translate
/// between dense indices and MSIR [`BlockId`]s.
#[derive(Debug, Clone)]
pub struct Cfg {
    blocks: Vec<BlockId>,
    index_of: HashMap<BlockId, usize>,
    succ: Vec<Vec<usize>>,
    pred: Vec<Vec<usize>>,
    entry: usize,
}

impl Cfg {
    /// Build a CFG from a function. Edges come from each block's terminator.
    ///
    /// Edges to non-existent blocks (malformed IR) are dropped; such IR should
    /// already have been rejected by validation, but we never panic on it.
    pub fn from_function(f: &Function) -> Self {
        let blocks: Vec<BlockId> = f.blocks.iter().map(|b| b.id).collect();
        let mut index_of = HashMap::with_capacity(blocks.len());
        for (i, &b) in blocks.iter().enumerate() {
            index_of.insert(b, i);
        }

        let n = blocks.len();
        let mut succ = vec![Vec::new(); n];
        let mut pred = vec![Vec::new(); n];
        for (i, block) in f.blocks.iter().enumerate() {
            for target in block.successors() {
                if let Some(&j) = index_of.get(&target) {
                    succ[i].push(j);
                    pred[j].push(i);
                }
            }
        }

        let entry = index_of.get(&f.entry).copied().unwrap_or(0);
        Cfg {
            blocks,
            index_of,
            succ,
            pred,
            entry,
        }
    }

    /// Number of nodes.
    pub fn node_count(&self) -> usize {
        self.blocks.len()
    }

    /// Whether the graph has no nodes.
    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    /// The entry node index.
    pub fn entry(&self) -> usize {
        self.entry
    }

    /// The [`BlockId`] for a node index.
    pub fn block_id(&self, node: usize) -> BlockId {
        self.blocks[node]
    }

    /// The node index for a [`BlockId`], if present.
    pub fn index_of(&self, block: BlockId) -> Option<usize> {
        self.index_of.get(&block).copied()
    }

    /// Successor node indices of `node`.
    pub fn successors(&self, node: usize) -> &[usize] {
        &self.succ[node]
    }

    /// Predecessor node indices of `node`.
    pub fn predecessors(&self, node: usize) -> &[usize] {
        &self.pred[node]
    }

    /// Exit nodes (no successors: returns and `unreachable`).
    pub fn exits(&self) -> Vec<usize> {
        (0..self.node_count())
            .filter(|&n| self.succ[n].is_empty())
            .collect()
    }

    /// Nodes reachable from the entry, in reverse postorder (entry first).
    ///
    /// Reverse postorder is the order the dominator computation iterates in;
    /// unreachable nodes are intentionally excluded.
    pub fn reverse_postorder(&self) -> Vec<usize> {
        let mut po = self.postorder();
        po.reverse();
        po
    }

    /// Nodes reachable from the entry, in postorder.
    pub fn postorder(&self) -> Vec<usize> {
        let mut visited = vec![false; self.node_count()];
        let mut order = Vec::new();
        if self.node_count() == 0 {
            return order;
        }
        // Iterative DFS to avoid stack overflow on large CFGs. Each stack
        // frame tracks the next successor index to visit. We read the top frame
        // by copy (no borrow held) so we can push within the loop body.
        let mut stack: Vec<(usize, usize)> = vec![(self.entry, 0)];
        visited[self.entry] = true;
        while let Some(&(node, next)) = stack.last() {
            if next < self.succ[node].len() {
                let s = self.succ[node][next];
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
}
