//! The generic monotone-framework worklist solver.
//!
//! Given a CFG, its loops, an entry state and two transfer callbacks, [`solve`]
//! computes a post-fixpoint: per-block `in`/`out` abstract states such that each
//! block's `out` is the transfer of its `in`, and each block's `in` is the join
//! of its predecessors' edge contributions. Widening is applied at loop headers
//! to force termination.

use crate::domain::AbstractDomain;
use csolver_cfg::{Cfg, Loops};
use std::collections::VecDeque;

/// The result of a dataflow solve: abstract state at the entry (`in`) and exit
/// (`out`) of every CFG node, indexed by node.
#[derive(Debug, Clone)]
pub struct Solution<D> {
    /// State on entry to each block.
    pub in_states: Vec<D>,
    /// State on exit from each block.
    pub out_states: Vec<D>,
}

impl<D: Clone> Solution<D> {
    /// The entry state of block `node`.
    pub fn entry_of(&self, node: usize) -> &D {
        &self.in_states[node]
    }

    /// The exit state of block `node`.
    pub fn exit_of(&self, node: usize) -> &D {
        &self.out_states[node]
    }
}

/// Solve a forward dataflow problem.
///
/// * `transfer_block(node, in_state)` returns the block's exit state.
/// * `edge(from, to, from_exit_state)` returns the contribution that flows from
///   `from` to `to` (e.g. binding the successor's block parameters).
///
/// Termination relies on `D::widen` being applied at every loop header (see the
/// soundness note on [`AbstractDomain`]).
pub fn solve<D, B, E>(
    cfg: &Cfg,
    loops: &Loops,
    entry_state: D,
    mut transfer_block: B,
    mut edge: E,
) -> Solution<D>
where
    D: AbstractDomain,
    B: FnMut(usize, &D) -> D,
    E: FnMut(usize, usize, &D) -> D,
{
    let n = cfg.node_count();
    let mut in_states = vec![D::bottom(); n];
    let mut out_states = vec![D::bottom(); n];
    if n == 0 {
        return Solution {
            in_states,
            out_states,
        };
    }

    let entry = cfg.entry();
    let headers = loops.headers();

    let mut in_worklist = vec![false; n];
    // How many times each node's `in` has been recomputed. Used as a safety net so
    // that a cyclic region whose header the natural-loop detector missed — an
    // **irreducible** CFG (a multi-entry loop, common in optimized kernel code with
    // computed gotos / switch state machines) — still gets a widening point and so
    // still terminates. Without it, such a cycle has no header, widening is never
    // applied on it, and an ascending chain (e.g. `x = x + 1` around the cycle) grows
    // forever. Forcing widen after enough revisits cuts every cycle regardless of
    // reducibility; it is sound because widening only ever over-approximates the join.
    let mut updates = vec![0u32; n];
    // High enough that a well-behaved reducible CFG (where real headers already widen)
    // never reaches it, so precision there is unchanged; low enough to bound the work
    // on a pathological cycle to a handful of iterations before it is forced to widen.
    const FORCE_WIDEN_AFTER: u32 = 64;
    let mut worklist: VecDeque<usize> = VecDeque::new();
    // Seed in reverse postorder so forward information propagates quickly.
    for node in cfg.reverse_postorder() {
        worklist.push_back(node);
        in_worklist[node] = true;
    }

    while let Some(u) = worklist.pop_front() {
        in_worklist[u] = false;

        // Join predecessor contributions (plus the seed at the entry).
        let mut joined = if u == entry {
            entry_state.clone()
        } else {
            D::bottom()
        };
        for &p in cfg.predecessors(u) {
            let contrib = edge(p, u, &out_states[p]);
            joined = joined.join(&contrib);
        }

        // Accelerate convergence at loop headers — and, as the termination safety net
        // above, at any node revisited too many times (an undetected irreducible cycle).
        let new_in = if headers.contains(&u) || updates[u] >= FORCE_WIDEN_AFTER {
            in_states[u].widen(&joined)
        } else {
            joined
        };

        if new_in != in_states[u] {
            updates[u] = updates[u].saturating_add(1);
            in_states[u] = new_in;
            let new_out = transfer_block(u, &in_states[u]);
            if new_out != out_states[u] {
                out_states[u] = new_out;
                for &s in cfg.successors(u) {
                    if !in_worklist[s] {
                        worklist.push_back(s);
                        in_worklist[s] = true;
                    }
                }
            }
        }
    }

    Solution {
        in_states,
        out_states,
    }
}
