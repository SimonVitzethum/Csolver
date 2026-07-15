use super::*;

impl Explorer<'_> {
    pub(crate) fn fresh_scalar(&mut self, width: u32) -> ExprId {
        let name = format!("?{}", self.fresh);
        self.fresh += 1;
        self.ctx.symbol(name, width)
    }

    /// The synthetic byte offset of `(region, field)`: cached on first access, else
    /// the region's current frontier, which is then advanced by the field size so
    /// the next new field lands in a disjoint range. Deterministic across paths
    /// (the executor processes each block once), so merges stay consistent.
    pub(crate) fn field_offset(&mut self, rid: usize, field: u32, size: u64) -> u64 {
        if let Some(&o) = self.field_offsets.get(&(rid, field)) {
            return o;
        }
        let frontier = self.field_frontier.entry(rid).or_insert(0);
        let off = *frontier;
        *frontier += size.max(1);
        self.field_offsets.insert((rid, field), off);
        off
    }

    pub(crate) fn fresh_value(&mut self, ty: &Type, origin: POrigin) -> SymValue {
        if ty.is_ptr() {
            // Mint a fresh provenance identity for this opaque pointer (see `Prov::Unknown`).
            // A separate counter keeps symbol numbering (and thus witnesses / determinism)
            // byte-identical to before the id existed.
            let id = self.prov_ids;
            self.prov_ids += 1;
            SymValue::Ptr(SymPointer {
                prov: Prov::Unknown(origin, Some(id)),
                offset: self.ctx.int(PTR_WIDTH, 0),
                align: 1,
                borrow: None,
            })
        } else if origin == POrigin::Load {
            // A scalar read from memory (a struct field / heap slot) gets a distinct `fld…`
            // name, so `--assume-field-invariants` can recognise a shift/divide whose amount is
            // *derived from a field* by walking the operand expression for such a symbol —
            // robust to any value-producing op the value flows through. `fld…` is not a genuine
            // input (like `?…`), so refutation gating is unchanged.
            SymValue::Scalar(self.fresh_scalar_named("fld", type_width(ty)))
        } else {
            SymValue::Scalar(self.fresh_scalar(type_width(ty)))
        }
    }

    /// A fresh scalar symbol with a chosen name prefix (see [`Self::fresh_scalar`], which uses
    /// `?`). The prefix records the value's origin for later recognition.
    pub(crate) fn fresh_scalar_named(&mut self, prefix: &str, width: u32) -> ExprId {
        let name = format!("{prefix}{}", self.fresh);
        self.fresh += 1;
        self.ctx.symbol(name, width)
    }

    /// Drive the analysis over the (back-edge-cut) CFG in **reverse postorder**,
    /// processing **each block exactly once**. Every non-back-edge predecessor is
    /// processed before a block, so its incoming edge-states are all available and
    /// **merged** into one entry state (see [`Explorer::merge_edges`]). This
    /// collapses the per-path explosion of the old recursive walk: a join with N
    /// predecessors is analysed once instead of once per path, so wide CFGs no
    /// longer blow up the path count (or trip the visit budget into truncation).
    pub(crate) fn run_merged(&mut self, entry_state: PathState) {
        let rpo: Vec<BlockId> = {
            let cfg = self.analysis.cfg();
            cfg.reverse_postorder().into_iter().map(|n| cfg.block_id(n)).collect()
        };
        let mut incoming: FxHashMap<BlockId, Vec<EdgeState>> = FxHashMap::default();
        incoming.insert(
            self.f.entry,
            vec![EdgeState { pred_state: entry_state, guard: None, args: Vec::new() }],
        );

        for block in rpo {
            if self.truncated {
                return;
            }
            let Some(edges) = incoming.remove(&block) else {
                continue; // unreachable in the DAG (or all incoming edges pruned)
            };
            if edges.is_empty() {
                continue;
            }
            self.visited_blocks.insert(block);
            self.visits += 1;
            // Truncate on the visit budget, or on the wall-clock budget (checked
            // here, between block visits, so the overrun is bounded by one block's
            // work plus the 250 ms per-solve valve). Both set `truncated`, which
            // discards every decision → non-`PASS`. See `ExecLimits::time_budget`.
            if self.visits > self.limits.max_visits
                || self.deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
            {
                self.truncated = true;
                return;
            }

            let mut state = self.merge_edges(block, edges);
            // At a loop header, over-approximate every iteration by replacing the
            // loop-carried parameters with fresh symbols constrained by the sound
            // interval invariant.
            if self.headers.contains(&block) {
                self.havoc_header(block, &mut state);
            }
            let Some(b) = self.f.block(block) else {
                continue;
            };
            for (idx, inst) in b.insts.iter().enumerate() {
                self.step(block, idx, inst, &mut state);
            }
            self.propagate_edges(block, b, state, &mut incoming);
        }
    }

    /// Push the out-edges of `block` (with their guards / block-parameter args) to
    /// the successors' incoming sets. Back-edges are cut; a branch whose guard is
    /// bit-precisely unreachable is pruned (see [`Explorer::branch_infeasible`]).
    pub(crate) fn propagate_edges(
        &mut self,
        block: BlockId,
        b: &BasicBlock,
        state: PathState,
        incoming: &mut FxHashMap<BlockId, Vec<EdgeState>>,
    ) {
        match &b.term {
            Terminator::Return(Some(o)) => {
                self.check_return(block, o, &state);
            }
            Terminator::Return(None) | Terminator::Unreachable => {}
            Terminator::Br { target, args } => {
                if !self.is_back_edge(block, *target) {
                    incoming.entry(*target).or_default().push(EdgeState {
                        pred_state: state,
                        guard: None,
                        args: args.clone(),
                    });
                }
            }
            Terminator::CondBr { cond, then_blk, then_args, else_blk, else_args } => {
                let mut ce = self.eval_scalar(cond, &state);
                // Coerce a non-boolean condition to `c != 0` (LLVM truthiness). A wider
                // value can reach here — an `i1` register that holds a widened expression,
                // or a loop-havoc'd condition — and using it directly as a boolean guard is
                // unencodable, which spuriously makes the whole path condition UNSAT (so a
                // real violation on that path is recorded UNKNOWN instead of refuted).
                if self.ctx.width(ce) != 1 {
                    let zero = self.ctx.int(self.ctx.width(ce), 0);
                    ce = self.ctx.cmp(SCmp::Ne, ce, zero);
                }
                let nce = self.ctx.not(ce);
                if !self.is_back_edge(block, *then_blk) && self.branch_infeasible(ce, &state) {
                    self.pruned_succs.insert(*then_blk);
                }
                if !self.is_back_edge(block, *then_blk) && !self.branch_infeasible(ce, &state) {
                    incoming.entry(*then_blk).or_default().push(EdgeState {
                        pred_state: state.clone(),
                        guard: Some(ce),
                        args: then_args.clone(),
                    });
                }
                if !self.is_back_edge(block, *else_blk) && self.branch_infeasible(nce, &state) {
                    self.pruned_succs.insert(*else_blk);
                }
                if !self.is_back_edge(block, *else_blk) && !self.branch_infeasible(nce, &state) {
                    incoming.entry(*else_blk).or_default().push(EdgeState {
                        pred_state: state,
                        guard: Some(nce),
                        args: else_args.clone(),
                    });
                }
            }
            Terminator::Switch { value, cases, default } => {
                let ve = self.eval_scalar(value, &state);
                for (cv, target) in cases {
                    if self.is_back_edge(block, *target) {
                        continue;
                    }
                    let k = self.ctx.constant(*cv);
                    let eq = self.ctx.cmp(SCmp::Eq, ve, k);
                    if self.branch_infeasible(eq, &state) {
                        continue;
                    }
                    incoming.entry(*target).or_default().push(EdgeState {
                        pred_state: state.clone(),
                        guard: Some(eq),
                        args: Vec::new(),
                    });
                }
                if !self.is_back_edge(block, *default) {
                    // The default edge carries `value != k` for every case.
                    // Omitting it was sound for proofs (over-approximation) but
                    // let a *refutation* on the default path pick a case value —
                    // an infeasible witness, i.e. a false FAIL (seen on rustc's
                    // jump-threaded slice-length switches).
                    let ne: Vec<ExprId> = cases
                        .iter()
                        .map(|(cv, _)| {
                            let k = self.ctx.constant(*cv);
                            let eq = self.ctx.cmp(SCmp::Eq, ve, k);
                            self.ctx.not(eq)
                        })
                        .collect();
                    let guard = self.ctx.and(ne);
                    if !self.branch_infeasible(guard, &state) {
                        incoming.entry(*default).or_default().push(EdgeState {
                            pred_state: state,
                            guard: Some(guard),
                            args: Vec::new(),
                        });
                    }
                }
            }
        }
    }

    /// Merge the incoming edge-states of a block into one entry state. A single
    /// predecessor is applied precisely (its guard and block-param args); multiple
    /// predecessors are joined by [`Explorer::merge_multi`].
    pub(crate) fn merge_edges(&mut self, block: BlockId, mut edges: Vec<EdgeState>) -> PathState {
        if edges.len() == 1 {
            let e = edges.swap_remove(0);
            let mut s = e.pred_state;
            if let Some(g) = e.guard {
                s.pathcond.push(g);
            }
            self.bind_params_into(block, &e.args, &mut s);
            return s;
        }
        self.merge_multi(block, edges)
    }

    /// Bind a block's parameters from the incoming `args`, evaluated in `s`.
    pub(crate) fn bind_params_into(&mut self, block: BlockId, args: &[Operand], s: &mut PathState) {
        let params = self.f.block(block).map(|b| b.params.clone()).unwrap_or_default();
        let vals: Vec<SymValue> = (0..params.len())
            .map(|j| match args.get(j) {
                Some(a) => self.eval_value(a, s),
                None => self.fresh_value(&params[j].1, POrigin::PhiFallback),
            })
            .collect();
        for ((preg, _), v) in params.iter().zip(vals) {
            s.env.insert(*preg, v);
        }
    }

    /// Join several incoming edge-states. Block parameters (PHIs) are merged with
    /// an `ITE` keyed on each edge's discriminating condition (its full path
    /// condition); the rest is over-approximated by [`Explorer::merge_core`].
    pub(crate) fn merge_multi(&mut self, block: BlockId, edges: Vec<EdgeState>) -> PathState {
        // Each edge's discriminator: the conjunction of its path condition (plus
        // its branch guard) — the condition under which control arrives by it.
        let discs: Vec<ExprId> = edges
            .iter()
            .map(|e| {
                let mut conds = e.pred_state.pathcond.clone();
                if let Some(g) = e.guard {
                    conds.push(g);
                }
                self.ctx.and(conds)
            })
            .collect();

        let mut merged = self.merge_core(&edges);
        merged.heap = self.merge_heap(&edges, &discs, merged.regions.len());

        let params = self.f.block(block).map(|b| b.params.clone()).unwrap_or_default();
        for (j, (preg, pty)) in params.iter().enumerate() {
            let vals: Vec<(ExprId, SymValue)> = edges
                .iter()
                .zip(&discs)
                .map(|(e, &d)| {
                    let v = match e.args.get(j) {
                        Some(a) => self.eval_value(a, &e.pred_state),
                        None => self.fresh_value(pty, POrigin::PhiFallback),
                    };
                    (d, v)
                })
                .collect();
            let mv = self.merge_values(&vals, pty);
            merged.env.insert(*preg, mv);
        }
        merged
    }

    /// The merged heap. A store to an address survives only if that address has a
    /// *last* store on **every** incoming edge (else it is ambiguous — dropped).
    /// Identical values are kept as-is; differing values are **joined** into a
    /// `select` guarded by the edge discriminators (the same construction as a
    /// PHI), so e.g. a `va_list` cursor advanced differently per branch stays a
    /// known — if multi-region — pointer instead of being forgotten. Records whose
    /// address or joined value points into a dropped region are sanitized out.
    pub(crate) fn merge_heap(&mut self, edges: &[EdgeState], discs: &[ExprId], rcount: usize) -> Vec<StoreRecord> {
        let region_kept = |p: &Prov| !matches!(p, Prov::Region(rid) if *rid >= rcount);
        let same_addr = |a: &SymPointer, b: &SymPointer| a.prov == b.prov && a.offset == b.offset;
        let last_for = |heap: &[StoreRecord], t: &SymPointer| -> Option<StoreRecord> {
            heap.iter().rev().find(|r| same_addr(&r.target, t)).cloned()
        };
        let ptr_ty = Type::Ptr { pointee: Box::new(Type::int(8)) };

        // Candidate addresses: the last store to each distinct target on edge 0.
        let mut done: Vec<SymPointer> = Vec::new();
        let mut out: Vec<StoreRecord> = Vec::new();
        for rec in edges[0].pred_state.heap.iter().rev() {
            let t = rec.target.clone();
            if done.iter().any(|d| same_addr(d, &t)) {
                continue;
            }
            done.push(t.clone());
            if !region_kept(&t.prov) {
                continue;
            }
            // The last store to `t` on every edge, with a consistent size.
            let mut per_edge: Vec<(ExprId, SymValue)> = Vec::with_capacity(edges.len());
            let mut ok = true;
            for (e, &d) in edges.iter().zip(discs) {
                match last_for(&e.pred_state.heap, &t) {
                    Some(r) if r.size == rec.size => per_edge.push((d, r.value)),
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            let value = self.merge_values(&per_edge, &ptr_ty);
            // Drop if the joined value points into a region the merge dropped.
            if let SymValue::Ptr(vp) = &value {
                if !self.pointer_regions_kept(&vp.prov, rcount) {
                    continue;
                }
            }
            out.push(StoreRecord { target: t, value, size: rec.size });
        }
        out
    }

    /// Whether every region a (possibly `Select`) provenance can denote survives a
    /// merge that kept `rcount` regions.
    pub(crate) fn pointer_regions_kept(&self, prov: &Prov, rcount: usize) -> bool {
        match prov {
            Prov::Region(rid) => *rid < rcount,
            Prov::Select { then_ptr, else_ptr, .. } => {
                self.pointer_regions_kept(&then_ptr.prov, rcount)
                    && self.pointer_regions_kept(&else_ptr.prov, rcount)
            }
            _ => true,
        }
    }
}
