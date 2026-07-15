use super::*;

impl Explorer<'_> {
    /// Decide a (possibly conjunctive) safety goal on one path. Tries to **prove**
    /// it (`A ⟹ P ∧ Q` by proving each conjunct — the linear procedure only takes
    /// conjunctive goals); failing that, on an **exact** path, tries to **refute**
    /// it per `mode` and return a concrete counterexample. `extra` adds premises
    /// used *only* for the refutation query (e.g. a region's no-wrap bound) — not
    /// for proving, which stays cheap.
    /// Under `--assume-field-invariants`, a scalar operand that came from an *unknown* memory
    /// read (a `fld…` symbol in its value expression) is assumed valid for its use — a shift amount below the bit
    /// width, a non-zero divisor. Records the `field-invariants` assumption and returns `true` so
    /// the caller treats the obligation as proven (prove-only — never refutes). Off by default,
    /// and inert for a value the analysis actually tracks.
    pub(crate) fn assume_field_scalar(&mut self, op: &Operand, state: &PathState) -> bool {
        if !self.limits.assume_field_invariants {
            return false;
        }
        // The operand's value **expression** carries a `fld…` symbol iff it is (transitively)
        // derived from a memory-loaded scalar — the expression flows through every real op
        // (`umin`'s `ite`, `shl`, `sub`, `zext`, …), so this is robust where a forward-propagated
        // flag would break at an unmodelled op. Prove-only.
        let e = self.eval_scalar(op, state);
        if self.expr_has_field_load(e) {
            self.assumptions.insert(FIELD_INVARIANTS);
            return true;
        }
        false
    }

    /// Whether `expr` contains at least one `fld…` leaf — a symbol minted for a scalar read of
    /// unknown memory (see `fresh_value`). Mirrors the [`Explorer::goal_is_genuine`] walk.
    fn expr_has_field_load(&self, expr: ExprId) -> bool {
        let mut stack = vec![expr];
        let mut seen: HashSet<ExprId> = HashSet::new();
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            match self.ctx.node(e) {
                Node::Sym { name, .. } if name.starts_with("fld") => return true,
                Node::Sym { .. } | Node::Const(_) | Node::Bool(_) => {}
                Node::Not(a) => stack.push(*a),
                Node::Bin { a, b, .. } | Node::Cmp { a, b, .. } => {
                    stack.push(*a);
                    stack.push(*b);
                }
                Node::And(xs) | Node::Or(xs) => stack.extend(xs.iter().copied()),
                Node::Ite { c, t, e } => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                Node::Zext(v) | Node::Sext(v) => stack.push(*v),
            }
        }
        false
    }

    pub(crate) fn decide(
        &mut self,
        conjuncts: &[ExprId],
        state: &PathState,
        mode: RefuteMode,
        extra: &[ExprId],
    ) -> Decision {
        if conjuncts.iter().all(|&g| self.prove(g, state)) {
            return Decision::Proven;
        }
        // Refute on an exact path (the strict, always-sound gate) — EXCEPT when the
        // goal is a free choice of an **internal** function's parameter: those are
        // caller-established (the guard lives at the in-module call sites), so a
        // witness picked freely from the parameter space may never occur, exactly as
        // an internal function's pointer contracts are prove-only. A constant OOB in
        // an internal function still refutes (no caller can prevent it). OR, in
        // bug-finding mode, refute on an inexact path when the goal depends only on
        // genuine inputs (see `goal_is_genuine`), so the witness is genuinely reachable.
        let internal_free_param =
            !self.exported && conjuncts.iter().any(|&g| self.goal_has_param(g));
        let gate = (state.exact && !internal_free_param)
            || (self.bug_finding
                && mode == RefuteMode::Possible
                && conjuncts.iter().all(|&g| self.goal_is_genuine(g)));
        if mode != RefuteMode::Off && gate {
            if let Some(model) = self.try_refute(conjuncts, state, mode, extra) {
                return Decision::Refuted(model);
            }
        }
        Decision::Unknown
    }

    /// Whether every symbolic leaf of `goal` is a **genuine input** — a function
    /// parameter (named `arg…`), as opposed to an over-approximated value (loop
    /// havoc / opaque call / undetermined load, all named `?…`, or a global `@…`).
    /// A goal built only from genuine inputs and constants is exactly refutable
    /// even on an over-approximated path: the path condition constrains genuine
    /// inputs only through real branch guards (never dropped by havoc, which only
    /// replaces the values it modifies), so a witness violating such a goal is a
    /// genuinely reachable input. Stateless — the name records the value's origin.
    /// Whether `goal` depends on a bare function parameter (`arg…`) — used to
    /// suppress refuting an *internal* function's access on a freely-chosen
    /// parameter value (caller-constrained). Constants and derived non-parameter
    /// values do not count, so a definite (constant) violation still refutes.
    pub(crate) fn goal_has_param(&self, goal: ExprId) -> bool {
        let mut stack = vec![goal];
        let mut seen: HashSet<ExprId> = HashSet::new();
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            match self.ctx.node(e) {
                Node::Sym { name, .. } if name.starts_with("arg") => return true,
                Node::Sym { .. } | Node::Const(_) | Node::Bool(_) => {}
                Node::Not(a) => stack.push(*a),
                Node::Bin { a, b, .. } | Node::Cmp { a, b, .. } => {
                    stack.push(*a);
                    stack.push(*b);
                }
                Node::And(xs) | Node::Or(xs) => stack.extend(xs.iter().copied()),
                Node::Ite { c, t, e } => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                Node::Zext(v) | Node::Sext(v) => stack.push(*v),
            }
        }
        false
    }

    pub(crate) fn goal_is_genuine(&self, goal: ExprId) -> bool {
        let mut stack = vec![goal];
        let mut seen: HashSet<ExprId> = HashSet::new();
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            match self.ctx.node(e) {
                Node::Sym { name, .. } => {
                    // Genuine inputs a witness may freely take: untrusted user data
                    // (`user…`, from `copy_from_user`) and unit-stride counting
                    // inductions (`ind…`, which reach every guard-admitted value) are
                    // always genuine; a parameter (`arg…`) only when the function is
                    // **exported** — an internal function's parameters are supplied by
                    // in-module callers (caller-constrained), so refuting on a freely
                    // chosen value would be a false positive.
                    let genuine = name.starts_with("user")
                        || name.starts_with("ind")
                        || (self.exported && name.starts_with("arg"));
                    if !genuine {
                        return false;
                    }
                }
                Node::Const(_) | Node::Bool(_) => {}
                Node::Not(a) => stack.push(*a),
                Node::Bin { a, b, .. } | Node::Cmp { a, b, .. } => {
                    stack.push(*a);
                    stack.push(*b);
                }
                Node::And(xs) | Node::Or(xs) => stack.extend(xs.iter().copied()),
                Node::Ite { c, t, e } => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                Node::Zext(v) | Node::Sext(v) => stack.push(*v),
            }
        }
        true
    }

    /// `true` if `expr` contains **at least one** genuine-input leaf (`user…`, `ind…`,
    /// or — when the function is exported — `arg…`). Unlike [`Explorer::goal_is_genuine`]
    /// (which is vacuously true for a pure constant), this requires the value to
    /// *actually vary* with an adversarial input. Used to keep an assumed region from
    /// refuting a constant-offset access (see `check_access`).
    pub(crate) fn expr_has_genuine_leaf(&self, expr: ExprId) -> bool {
        let mut stack = vec![expr];
        let mut seen: HashSet<ExprId> = HashSet::new();
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            match self.ctx.node(e) {
                Node::Sym { name, .. } => {
                    if name.starts_with("user")
                        || name.starts_with("ind")
                        || (self.exported && name.starts_with("arg"))
                    {
                        return true;
                    }
                }
                Node::Const(_) | Node::Bool(_) => {}
                Node::Not(a) | Node::Zext(a) | Node::Sext(a) => stack.push(*a),
                Node::Bin { a, b, .. } | Node::Cmp { a, b, .. } => {
                    stack.push(*a);
                    stack.push(*b);
                }
                Node::And(xs) | Node::Or(xs) => stack.extend(xs.iter().copied()),
                Node::Ite { c, t, e } => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
            }
        }
        false
    }

    /// On an exact path, return a concrete witness of a violation, or `None`.
    ///
    /// - [`RefuteMode::Definite`] refutes only a **definite** violation
    ///   (`assumptions ⟹ ¬goal`, proved bit-precisely): the goal can never hold
    ///   on this path. Used for scalar `SafetyCheck`s, so a merely
    ///   *satisfiable-but-not-valid* check (e.g. an unconstrained `i < 8`) stays
    ///   `Unknown` rather than becoming a FAIL.
    /// - [`RefuteMode::Possible`] refutes whenever **some** reaching input
    ///   violates the goal (`assumptions ∧ ¬goal` is satisfiable). Used for
    ///   memory accesses: the access *executes*, so any reachable input that
    ///   makes it out of bounds is a definite runtime violation. Sound because
    ///   the model satisfies the (exact) path condition, hence is genuinely
    ///   reachable, and callers restrict it to concrete-size regions (so a
    ///   wrapped allocation size can't fabricate a too-small buffer).
    ///
    /// Either way the witness existing also confirms the path is feasible.
    pub(crate) fn try_refute(
        &mut self,
        conjuncts: &[ExprId],
        state: &PathState,
        mode: RefuteMode,
        extra: &[ExprId],
    ) -> Option<Model> {
        let goal = if conjuncts.len() == 1 {
            conjuncts[0]
        } else {
            self.ctx.and(conjuncts.to_vec())
        };
        let not_goal = self.ctx.not(goal);
        let mut assumptions = state.pathcond.clone();
        assumptions.extend_from_slice(&state.facts);
        assumptions.extend_from_slice(extra);
        // For a *definite* refutation, first require that the goal can never hold
        // on this (feasible, exact) path — proved bit-precisely. A *possible*
        // refutation skips this: any satisfiable violation is a real one.
        if mode == RefuteMode::Definite
            && !bitprecise::prove_implies(&self.ctx, &assumptions, not_goal)
        {
            return None;
        }
        // The witness is a model of `assumptions ∧ ¬goal`: it satisfies the path
        // condition (reachable) and falsifies the goal (violating).
        bitprecise::find_counterexample(&self.ctx, &assumptions, goal)
    }

    /// A model of the path condition — a witness that this program point is
    /// genuinely reached. `None` if the path is infeasible (or over-approximated,
    /// outside bug-finding). Used to witness a *definite* temporal violation
    /// (use-after-free / double-free): the region reached `Freed` through an explicit
    /// `Dealloc` on this path and is now accessed, so the violation holds for every
    /// reaching input and the reachability witness *is* the counterexample.
    ///
    /// In **bug-finding mode** the exactness gate is dropped: the free and the access
    /// are structural facts of this path, so an over-approximation elsewhere (an init
    /// loop before the free, an opaque call) does not make the use-after-free any less
    /// real — reporting it accepts the same small path-feasibility risk the mode
    /// trades for recall. Strict verification keeps the exact gate.
    pub(crate) fn feasibility_witness(&mut self, state: &PathState) -> Option<Model> {
        if !state.exact && !self.bug_finding {
            return None;
        }
        let mut assumptions = state.pathcond.clone();
        assumptions.extend_from_slice(&state.facts);
        let never = self.ctx.boolean(false);
        bitprecise::find_counterexample(&self.ctx, &assumptions, never)
    }

    /// Record a temporal obligation (use-after-free / no-double-free) decided
    /// structurally from the region's lifetime state. On an **exact** path a
    /// region only reaches `Freed` through an explicit `Dealloc`, so a violating
    /// state there is a *definite* violation for every reaching input — `Refuted`
    /// with the feasibility witness. Off an exact path (a freeing call/loop only
    /// *may* have freed) it degrades to `Unknown`; a safe state is `Proven`.
    pub(crate) fn record_temporal(
        &mut self,
        at: (BlockId, usize),
        prop: SafetyProperty,
        violated: bool,
        state: &PathState,
        desc: &str,
        residual: &str,
    ) {
        let (block, idx) = at;
        if !violated {
            self.record(block, idx, prop, true, desc, residual);
            return;
        }
        match self.feasibility_witness(state) {
            Some(model) => {
                self.record_mem(block, idx, prop, Decision::Refuted(model), desc, residual)
            }
            None => self.record(block, idx, prop, false, desc, residual),
        }
    }

    /// Try to prove `goal` under the current path. Prefers the bit-precise
    /// procedure (exact, no overflow assumption); only when the proof falls back
    /// to the linear-integer model is `linear-no-overflow` recorded — so a goal
    /// decided bit-precisely yields a `PASS` with one fewer assumption.
    pub(crate) fn prove(&mut self, goal: ExprId, state: &PathState) -> bool {
        // **Relevance (cone-of-influence) filter.** Only a path-condition assumption transitively
        // sharing a variable with `goal` can affect the entailment `assumptions ⊨ goal`; a
        // disconnected (and, on a live path, satisfiable) assumption cannot change whether `goal`
        // follows. Keeping only the cone shrinks the query and — by dropping path-specific
        // irrelevant guards — raises the prove-cache hit rate (the same goal now shares one entry
        // across paths that differ only in irrelevant guards). Exact on satisfiable paths; on a
        // contradictory (dead) path it may drop a *vacuous* proof to UNKNOWN — sound (unreachable).
        let all: Vec<ExprId> = state
            .pathcond
            .iter()
            .chain(state.facts.iter())
            .copied()
            .collect();
        let assumptions = self.relevant_assumptions(goal, &all);
        let key = (assumptions.clone().into_boxed_slice(), goal);
        let method = match self.prove_cache.get(&key) {
            Some(m) => *m,
            None => {
                let m = prove_implies_method(&self.ctx, &assumptions, goal);
                self.prove_cache.insert(key, m);
                m
            }
        };
        match method {
            Some(ProofMethod::BitPrecise) => true,
            Some(ProofMethod::Linear) => {
                self.assumptions.insert(LINEAR_NO_OVERFLOW);
                true
            }
            None => false,
        }
    }
}
