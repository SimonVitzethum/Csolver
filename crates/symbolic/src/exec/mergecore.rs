use super::*;

impl Explorer<'_> {
    /// The non-parameter part of a multi-predecessor merge: a sound
    /// over-approximation of all incoming states. Regions keep the common prefix
    /// (identical byte size) with a conservative lifetime (`Live` only if live on
    /// every edge); the register environment is taken from the first edge (in SSA
    /// the registers live past a join are defined before the split, hence equal),
    /// sanitizing any pointer into a dropped region; the path condition is the
    /// longest common prefix and the facts their intersection (both sound,
    /// weaker); the heap is **intersected** — a store identical on every incoming
    /// edge definitely holds after the merge, so it is kept (a value written before
    /// the branch and read after it, e.g. a `va_list`'s fields); anything the paths
    /// disagree on is dropped. The path is no longer `exact`.
    pub(crate) fn merge_core(&self, edges: &[EdgeState]) -> PathState {
        let first = &edges[0].pred_state;

        let mut regions = Vec::new();
        'prefix: for i in 0..first.regions.len() {
            let size = first.regions[i].size;
            for e in edges {
                match e.pred_state.regions.get(i) {
                    Some(r) if r.size == size => {}
                    _ => break 'prefix,
                }
            }
            let live_all = edges
                .iter()
                .all(|e| e.pred_state.regions[i].state == LifetimeState::Live);
            let mut r = first.regions[i].clone();
            r.state = if live_all { LifetimeState::Live } else { LifetimeState::Freed };
            // Intersect provenance labels across edges: a label survives the join only if it
            // holds on EVERY incoming path (the meet), so it is never attributed to a path that
            // did not set it — sound (no false FAIL); an entry-set label (on all paths) survives.
            r.prov_labels = first.regions[i]
                .prov_labels
                .iter()
                .copied()
                .filter(|l| edges.iter().all(|e| e.pred_state.regions[i].prov_labels.contains(l)))
                .collect();
            regions.push(r);
        }
        let rcount = regions.len();

        let mut env = first.env.clone();
        for v in env.values_mut() {
            if let SymValue::Ptr(p) = v {
                if let Prov::Region(rid) = p.prov {
                    if rid >= rcount {
                        p.prov = Prov::Unknown(POrigin::RegionDrop, None);
                    }
                }
            }
        }

        let mut pathcond = Vec::new();
        for k in 0..first.pathcond.len() {
            let c = first.pathcond[k];
            if edges.iter().all(|e| e.pred_state.pathcond.get(k) == Some(&c)) {
                pathcond.push(c);
            } else {
                break;
            }
        }

        let facts: Vec<ExprId> = first
            .facts
            .iter()
            .copied()
            .filter(|f| edges.iter().all(|e| e.pred_state.facts.contains(f)))
            .collect();

        // Opaque-pointer labels survive the join by the same **meet** as regions/facts: an id
        // keeps a label only if every incoming edge has it — sound (never attributed to a path
        // that did not set it), and an entry-seed (set before any branch) survives on all paths.
        let opaque_labels: FxHashMap<u32, FxHashSet<u32>> = first
            .opaque_labels
            .iter()
            .filter_map(|(id, labels)| {
                let common: FxHashSet<u32> = labels
                    .iter()
                    .copied()
                    .filter(|l| {
                        edges
                            .iter()
                            .all(|e| e.pred_state.opaque_labels.get(id).is_some_and(|s| s.contains(l)))
                    })
                    .collect();
                (!common.is_empty()).then_some((*id, common))
            })
            .collect();

        // Non-null opaque-provenance ids survive by the same **meet**: an id is non-null on
        // the join only if every incoming edge marks it non-null (entry-seeded, so it survives
        // on all paths). Dropping one is sound (a null-deref just falls back to UNKNOWN).
        let nonnull_provs: FxHashSet<u32> = first
            .nonnull_provs
            .iter()
            .copied()
            .filter(|id| edges.iter().all(|e| e.pred_state.nonnull_provs.contains(id)))
            .collect();

        // Borrow stacks (aliasing model) survive a join only when **all** incoming paths agree
        // exactly on a region's stack; otherwise the region is *poisoned* (`None`), which skips
        // its aliasing checks downstream — sound (an ambiguous merge never drives a false FAIL).
        let region_borrows: FxHashMap<usize, Option<Vec<RegId>>> = {
            let mut keys: Vec<usize> = Vec::new();
            for e in edges {
                keys.extend(e.pred_state.region_borrows.keys().copied());
            }
            keys.sort_unstable();
            keys.dedup();
            keys.into_iter()
                .map(|rid| {
                    let mut it = edges.iter().map(|e| e.pred_state.region_borrows.get(&rid).cloned().flatten());
                    let first = it.next().flatten();
                    let agree = first.is_some() && edges.iter().all(|e| {
                        e.pred_state.region_borrows.get(&rid).cloned().flatten() == first
                    });
                    (rid, if agree { first } else { None })
                })
                .collect()
        };

        // Scalar taint survives the join by the same **meet**: a register keeps a taint label
        // only if every incoming edge has it — so a sink refutes only on a *definitely*-tainted
        // value (no false FAIL under a partly-tainted phi). Under-taints (a value tainted on one
        // branch only is dropped) — sound, recall-only loss.
        let tainted: FxHashMap<RegId, FxHashSet<u32>> = first
            .tainted
            .iter()
            .filter_map(|(reg, labels)| {
                let common: FxHashSet<u32> = labels
                    .iter()
                    .copied()
                    .filter(|l| {
                        edges
                            .iter()
                            .all(|e| e.pred_state.tainted.get(reg).is_some_and(|s| s.contains(l)))
                    })
                    .collect();
                (!common.is_empty()).then_some((*reg, common))
            })
            .collect();

        // Typestate survives the join by the same **meet**: a `(resource, protocol)` keeps its
        // state only if every incoming edge agrees on the *same* state — so a require refutes
        // only on a resource *definitely* in the forbidden state (no false FAIL under a partial
        // state; a disagreement drops the entry, conservatively "unknown").
        let typestates: FxHashMap<(ResKey, u32), u32> = first
            .typestates
            .iter()
            .filter(|(k, st)| edges.iter().all(|e| e.pred_state.typestates.get(k) == Some(*st)))
            .map(|(k, st)| (*k, *st))
            .collect();
        // Refcounts survive the join by the same meet: keep a count only if every incoming
        // edge agrees, so an underflow refutes only when the count is definite.
        let refcounts: FxHashMap<(ResKey, u32), i64> = first
            .refcounts
            .iter()
            .filter(|(k, c)| edges.iter().all(|e| e.pred_state.refcounts.get(k) == Some(*c)))
            .map(|(k, c)| (*k, *c))
            .collect();
        // RCU depth after the join is the min over edges (an access is RCU-protected only if in
        // a read-side section on every path); per-CPU ids survive by intersection (meet).
        let rcu_depth = edges.iter().map(|e| e.pred_state.rcu_depth).min().unwrap_or(0);
        let irq_off = edges.iter().map(|e| e.pred_state.irq_off).min().unwrap_or(0);
        let percpu: FxHashSet<u32> = first
            .percpu
            .iter()
            .copied()
            .filter(|id| edges.iter().all(|e| e.pred_state.percpu.contains(id)))
            .collect();

        // Resolved function-pointer identities survive the join by the same meet:
        // a register keeps its target only if every incoming edge resolved it to
        // the *same* function (an SSA value dominating the merge does; a phi does
        // not appear here). Sound — a disagreement drops back to opaque dispatch.
        let fn_ptrs: FxHashMap<RegId, FuncId> = first
            .fn_ptrs
            .iter()
            .filter(|(r, fid)| edges.iter().all(|e| e.pred_state.fn_ptrs.get(r) == Some(fid)))
            .map(|(r, fid)| (*r, *fid))
            .collect();

        // A lock counts as held after the join only if held on *every* incoming edge
        // (meet), so a subsequent re-acquire is flagged only when it is a definite
        // double-lock on all paths — sound (a partial hold never fabricates one).
        let locks_held: FxHashSet<RefBase> = first
            .locks_held
            .iter()
            .copied()
            .filter(|b| edges.iter().all(|e| e.pred_state.locks_held.contains(b)))
            .collect();
        let spin_held: FxHashSet<RefBase> = first
            .spin_held
            .iter()
            .copied()
            .filter(|b| edges.iter().all(|e| e.pred_state.spin_held.contains(b)))
            .collect();
        // Same meet for held lock classes: keep a base's class only if held (with the
        // same class) on every incoming path.
        let held_classes: FxHashMap<RefBase, String> = first
            .held_classes
            .iter()
            .filter(|(b, c)| edges.iter().all(|e| e.pred_state.held_classes.get(b) == Some(*c)))
            .map(|(b, c)| (*b, c.clone()))
            .collect();
        // Same meet for freed bases: a base counts as freed after the join only if it was
        // freed on every incoming path, so a re-free is flagged only when it is a definite
        // double-free on all paths.
        let freed_bases: FxHashSet<RefBase> = first
            .freed_bases
            .iter()
            .copied()
            .filter(|b| edges.iter().all(|e| e.pred_state.freed_bases.contains(b)))
            .collect();
        // Same meet for fetched user addresses: an address counts as fetched after the
        // join only if fetched on every incoming path, so a re-fetch is flagged as a
        // double-fetch only when it is definite on all paths.
        let user_fetches: FxHashSet<(RefBase, u128)> = first
            .user_fetches
            .iter()
            .copied()
            .filter(|k| edges.iter().all(|e| e.pred_state.user_fetches.contains(k)))
            .collect();

        // The heap is computed by `merge_multi` (it needs the edge discriminators
        // to *join* differing stores); leave it empty here.
        PathState {
            env,
            regions,
            pathcond,
            facts,
            heap: Vec::new(),
            unwritten_reads: FxHashMap::default(),
            ref_regions: FxHashMap::default(),
            opaque_labels,
            nonnull_provs,
            region_borrows,
            tainted,
            typestates,
            refcounts,
            rcu_depth,
            irq_off,
            percpu,
            fn_ptrs,
            locks_held,
            spin_held,
            held_classes,
            user_fetches,
            freed_bases,
            exact: false,
        }
    }

    /// Merge per-edge values into one, as a right-folded `ITE` over the edge
    /// discriminators (the last edge is the final `else`).
    pub(crate) fn merge_values(&mut self, vals: &[(ExprId, SymValue)], ty: &Type) -> SymValue {
        let Some((_, last)) = vals.last().cloned() else {
            return self.fresh_value(ty, POrigin::PhiFallback);
        };
        let mut acc = last;
        for (d, v) in vals[..vals.len() - 1].iter().rev() {
            acc = self.select(*d, v.clone(), acc, ty);
        }
        acc
    }

    /// `select(d, a, b)` = `if d then a else b`, structurally: `ITE` on scalars
    /// and on same-provenance pointer offsets; differing provenance degrades to an
    /// opaque pointer (sound over-approximation).
    pub(crate) fn select(&mut self, d: ExprId, a: SymValue, b: SymValue, ty: &Type) -> SymValue {
        match (a, b) {
            (SymValue::Scalar(ea), SymValue::Scalar(eb)) => SymValue::Scalar(self.ctx.ite(d, ea, eb)),
            (SymValue::Ptr(pa), SymValue::Ptr(pb)) if pa.prov == pb.prov => SymValue::Ptr(SymPointer {
                // The borrow tag survives a select only if both sides agree (else ambiguous → None).
                borrow: if pa.borrow == pb.borrow { pa.borrow } else { None },
                prov: pa.prov,
                offset: self.ctx.ite(d, pa.offset, pb.offset),
                align: gcd(pa.align, pb.align),
            }),
            // Two different regions: keep both as a `Select` join (bounded depth,
            // so a pathological chain of distinct selects degrades to opaque rather
            // than growing without limit). An access through it is proved for each
            // alternative under its guard (see `check_access`).
            (SymValue::Ptr(pa), SymValue::Ptr(pb)) => {
                if prov_select_depth(&pa.prov).max(prov_select_depth(&pb.prov)) >= 8 {
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Unknown(POrigin::SelectJoin, None),
                        offset: self.ctx.int(PTR_WIDTH, 0),
                        align: 1,
                        borrow: None,
                    })
                } else {
                    SymValue::Ptr(SymPointer {
                        borrow: if pa.borrow == pb.borrow { pa.borrow } else { None },
                        prov: Prov::Select {
                            cond: d,
                            then_ptr: Box::new(pa.clone()),
                            else_ptr: Box::new(pb.clone()),
                        },
                        offset: self.ctx.int(PTR_WIDTH, 0),
                        align: gcd(pa.align, pb.align),
                    })
                }
            }
            _ => self.fresh_value(ty, POrigin::SelectJoin),
        }
    }

    /// Whether `cond` is **bit-precisely** unsatisfiable under the current path,
    /// i.e. `pathcond ∧ facts ⟹ ¬cond` holds *exactly*. Then the branch guarded
    /// by `cond` has no concrete execution and is soundly pruned.
    ///
    /// The check is deliberately **bit-precise**, not linear: pruning on a
    /// `linear-no-overflow`-dependent implication could discard a branch that is
    /// actually reachable only through wraparound and so hide a real violation
    /// (a false PASS). A bit-precise `⟹ ¬cond` holds for *every* machine value,
    /// so the branch is genuinely dead. Missing a (linear-only) infeasibility
    /// just keeps a redundant path — never unsound.
    pub(crate) fn branch_infeasible(&mut self, cond: ExprId, state: &PathState) -> bool {
        let not_cond = self.ctx.not(cond);
        // **Relevance pre-filter (exact).** Only a path-condition assumption that shares a variable
        // with `cond` can make `cond` unsatisfiable; if none do, whether the branch is infeasible
        // depends on `cond` alone. So when `cond`'s variables are disjoint from the whole path
        // condition, decide it with an *empty* assumption set — a tiny query — instead of one
        // carrying the full (on large functions, hundreds-deep) path condition. This is the same
        // boolean result (irrelevant assumptions cannot change the entailment), so verdicts are
        // unchanged; it only removes the dominant solver cost on big CFGs. (If the path condition is
        // itself contradictory we may then not prune a dead branch, but a refutation there re-solves
        // the full path condition and finds no model — so no false FAIL; see `try_refute`.)
        let cvars = self.syms(cond);
        if !cvars.is_empty() {
            let mut shares = false;
            for a in state.pathcond.iter().chain(state.facts.iter()) {
                let av = self.syms(*a);
                if sorted_share(&av, &cvars) {
                    shares = true;
                    break;
                }
            }
            if !shares {
                return bitprecise::prove_implies(&self.ctx, &[], not_cond);
            }
        }
        let mut assumptions = state.pathcond.clone();
        assumptions.extend_from_slice(&state.facts);
        bitprecise::prove_implies(&self.ctx, &assumptions, not_cond)
    }

    /// The memoized variable set (sorted `Sym` ids) of an expression — see `sym_memo`.
    pub(crate) fn syms(&mut self, e: ExprId) -> std::rc::Rc<[ExprId]> {
        if let Some(v) = self.sym_memo.get(&e) {
            return v.clone();
        }
        let v: std::rc::Rc<[ExprId]> = self.ctx.symbols_of(e).into();
        self.sym_memo.insert(e, v.clone());
        v
    }

    /// The **cone of influence** of `goal` within `all`: the assumptions transitively reachable
    /// from `goal`'s variables by shared variables (fixpoint). The result is sorted and deduplicated
    /// (a canonical, path-independent key for the prove-cache). A constant goal has no variables, so
    /// no assumption is relevant. See `prove` for why this preserves the entailment on live paths.
    pub(crate) fn relevant_assumptions(&mut self, goal: ExprId, all: &[ExprId]) -> Vec<ExprId> {
        let gvars = self.syms(goal);
        if gvars.is_empty() || all.is_empty() {
            return Vec::new();
        }
        let avars: Vec<std::rc::Rc<[ExprId]>> = all.iter().map(|a| self.syms(*a)).collect();
        let mut cone: std::collections::BTreeSet<ExprId> = gvars.iter().copied().collect();
        let mut kept = vec![false; all.len()];
        loop {
            let mut changed = false;
            for i in 0..all.len() {
                if kept[i] {
                    continue;
                }
                if avars[i].iter().any(|v| cone.contains(v)) {
                    kept[i] = true;
                    cone.extend(avars[i].iter().copied());
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let mut out: Vec<ExprId> = all
            .iter()
            .zip(kept)
            .filter_map(|(a, k)| k.then_some(*a))
            .collect();
        out.sort_unstable();
        out.dedup();
        out
    }

    /// Whether the edge `from -> to` is a loop back-edge (cut during
    /// exploration). A back-edge targets a loop header that dominates its
    /// source.
    pub(crate) fn is_back_edge(&self, from: BlockId, to: BlockId) -> bool {
        if !self.headers.contains(&to) {
            return false;
        }
        let cfg = self.analysis.cfg();
        let (Some(fi), Some(ti)) = (cfg.index_of(from), cfg.index_of(to)) else {
            return false;
        };
        self.dominators.dominates(ti, fi)
    }
}
