//! Natural-loop detection.
//!
//! A back edge is an edge `n -> h` whose target `h` dominates its source `n`.
//! The natural loop of a back edge is `h` together with every node that can
//! reach `n` without passing through `h`. Loops that share a header are merged.
//!
//! Loop headers are exactly where the abstract-interpretation fixpoint applies
//! widening, so this analysis is on the soundness-critical path: missing a
//! header would let the fixpoint diverge; spurious headers only cost precision.

use crate::dominators::Dominators;
use crate::graph::Cfg;
use std::collections::BTreeSet;

/// A natural loop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Loop {
    /// The loop header (the unique entry; dominates the whole body).
    pub header: usize,
    /// The latch nodes (sources of back edges into the header).
    pub latches: Vec<usize>,
    /// All nodes in the loop body, including the header, as a sorted set.
    pub body: BTreeSet<usize>,
}

impl Loop {
    /// Whether `node` is part of this loop's body.
    pub fn contains(&self, node: usize) -> bool {
        self.body.contains(&node)
    }
}

/// All natural loops of a function, keyed by header.
#[derive(Debug, Clone, Default)]
pub struct Loops {
    loops: Vec<Loop>,
}

impl Loops {
    /// Detect all natural loops of `cfg` given its `dominators`.
    pub fn detect(cfg: &Cfg, dominators: &Dominators) -> Loops {
        // Gather back edges grouped by header.
        let mut latches_by_header: std::collections::BTreeMap<usize, Vec<usize>> =
            std::collections::BTreeMap::new();
        for n in 0..cfg.node_count() {
            for &h in cfg.successors(n) {
                // h dominates n  =>  n -> h is a back edge with header h.
                if dominators.dominates(h, n) {
                    latches_by_header.entry(h).or_default().push(n);
                }
            }
        }

        let mut loops = Vec::new();
        for (header, latches) in latches_by_header {
            let body = natural_loop_body(cfg, header, &latches);
            loops.push(Loop {
                header,
                latches,
                body,
            });
        }
        Loops { loops }
    }

    /// All detected loops.
    pub fn all(&self) -> &[Loop] {
        &self.loops
    }

    /// Whether `node` is a loop header.
    pub fn is_header(&self, node: usize) -> bool {
        self.loops.iter().any(|l| l.header == node)
    }

    /// The set of all loop-header node indices.
    pub fn headers(&self) -> BTreeSet<usize> {
        self.loops.iter().map(|l| l.header).collect()
    }

    /// The loop whose header is `node`, if any.
    pub fn loop_with_header(&self, node: usize) -> Option<&Loop> {
        self.loops.iter().find(|l| l.header == node)
    }
}

/// Compute the body of the natural loop for back edges into `header` from the
/// given `latches` by reverse reachability that stops at the header.
fn natural_loop_body(cfg: &Cfg, header: usize, latches: &[usize]) -> BTreeSet<usize> {
    let mut body = BTreeSet::new();
    body.insert(header);
    let mut stack = Vec::new();
    for &latch in latches {
        if body.insert(latch) {
            stack.push(latch);
        }
    }
    while let Some(m) = stack.pop() {
        for &p in cfg.predecessors(m) {
            if body.insert(p) {
                stack.push(p);
            }
        }
    }
    body
}

#[cfg(test)]
mod tests {
    use super::*;
    use csolver_ir::{BasicBlock, BlockId, FuncId, Function, Operand, RegId, Terminator, Type};

    fn cond(id: u32, t: u32, e: u32) -> BasicBlock {
        BasicBlock::new(
            BlockId(id),
            Terminator::CondBr {
                cond: Operand::Reg(RegId(0)),
                then_blk: BlockId(t),
                then_args: vec![],
                else_blk: BlockId(e),
                else_args: vec![],
            },
        )
    }
    fn br(id: u32, t: u32) -> BasicBlock {
        BasicBlock::new(
            BlockId(id),
            Terminator::Br {
                target: BlockId(t),
                args: vec![],
            },
        )
    }

    /// 0 -> 1; 1 -> {2(body), 3(exit)}; 2 -> 1 (back edge).
    fn while_loop() -> Function {
        Function {
            id: FuncId(0),
            name: "while".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![
                br(0, 1),
                cond(1, 2, 3),
                br(2, 1),
                BasicBlock::new(BlockId(3), Terminator::Return(None)),
            ],
            entry: BlockId(0),
        }
    }

    #[test]
    fn detects_single_natural_loop() {
        let f = while_loop();
        let cfg = Cfg::from_function(&f);
        let dom = Dominators::new(&cfg);
        let loops = Loops::detect(&cfg, &dom);

        assert_eq!(loops.all().len(), 1);
        let l = &loops.all()[0];
        assert_eq!(l.header, 1);
        assert_eq!(l.latches, vec![2]);
        // Body is the header and the back-edge source, nothing else.
        assert!(l.contains(1));
        assert!(l.contains(2));
        assert!(!l.contains(0));
        assert!(!l.contains(3));
        assert!(loops.is_header(1));
        assert!(!loops.is_header(0));
    }

    #[test]
    fn acyclic_has_no_loops() {
        // 0 -> 1 -> 2, no back edges.
        let f = Function {
            id: FuncId(0),
            name: "acyclic".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![
                br(0, 1),
                br(1, 2),
                BasicBlock::new(BlockId(2), Terminator::Return(None)),
            ],
            entry: BlockId(0),
        };
        let cfg = Cfg::from_function(&f);
        let dom = Dominators::new(&cfg);
        let loops = Loops::detect(&cfg, &dom);
        assert!(loops.all().is_empty());
        assert!(loops.headers().is_empty());
    }
}
