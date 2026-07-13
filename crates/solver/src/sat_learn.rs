use super::*;

impl Solver {
    /// 1-UIP conflict analysis. Given the falsified clause `confl` (reached at a
    /// decision level ≥ 1), resolve backwards along the implication graph until a
    /// single literal of the current level remains — the *unique implication
    /// point* — and return the asserting learnt clause (with the UIP literal at
    /// index 0) together with the level to backjump to.
    ///
    /// The learnt clause is a chain of resolutions of clauses already in the
    /// store, so it is entailed by the input: adding it prunes the search without
    /// removing any model. This is the crux of the soundness argument.
    ///
    /// Returns `(learnt clause, backjump level, LBD)`. The LBD (count of distinct
    /// decision levels among the clause's literals) is computed here, before the
    /// backjump undoes those levels.
    pub(super) fn analyze(&mut self, confl: usize) -> (Vec<Lit>, u32, u32) {
        let d = self.decision_level();
        let mut learnt: Vec<Lit> = vec![Lit::pos(0)]; // slot 0 = asserting literal
        let mut counter = 0u32; // current-level literals not yet resolved
        let mut pivot: Option<u32> = None;
        let mut confl_ci = confl;
        let mut idx = self.trail.len();
        let uip = loop {
            for &lit in &self.clauses[confl_ci] {
                let v = lit.var;
                if Some(v) == pivot {
                    continue; // the literal we are resolving on
                }
                if !self.seen[v as usize] && self.level[v as usize] > 0 {
                    self.seen[v as usize] = true;
                    if self.level[v as usize] == d {
                        counter += 1;
                    } else {
                        learnt.push(lit); // a lower-level reason literal
                    }
                }
            }
            // Walk the trail back to the most recent literal seen at this level.
            while !self.seen[self.trail[idx - 1] as usize] {
                idx -= 1;
            }
            idx -= 1;
            let tv = self.trail[idx];
            self.seen[tv as usize] = false;
            counter -= 1;
            if counter == 0 {
                break tv; // the UIP
            }
            pivot = Some(tv);
            // `tv` was propagated, so it has an antecedent; the `None` arm is
            // unreachable in a correct 1-UIP walk. Treating it as the UIP is a
            // panic-free fallback that keeps the clause a valid resolvent; it
            // fully clears the scratch so no marks leak into the next analysis.
            match self.reason[tv as usize] {
                Some(r) => confl_ci = r,
                None => {
                    self.seen.iter_mut().for_each(|b| *b = false);
                    break tv;
                }
            }
        };
        // The asserting literal is the one that is *false* under the current
        // assignment (so after backjump the clause becomes unit and flips it).
        learnt[0] = Lit {
            var: uip,
            neg: self.assign[uip as usize] == Some(true),
        };
        // Order the clause for watching: put the highest-level literal (among all
        // but the asserting one) at index 1. After the backjump that literal is the
        // most recently falsified, so watching `lits[0]` (the asserting literal) and
        // `lits[1]` keeps the two-watched invariant. Its level is the backjump
        // target (0 for a learnt unit).
        let mut btlevel = 0u32;
        if learnt.len() >= 2 {
            let mut max_i = 1;
            for i in 2..learnt.len() {
                if self.level[learnt[i].var as usize] > self.level[learnt[max_i].var as usize] {
                    max_i = i;
                }
            }
            learnt.swap(1, max_i);
            btlevel = self.level[learnt[1].var as usize];
        }
        // VSIDS: reward the variables in the learnt clause, then decay globally so
        // recent conflicts weigh more. A pure branch-order heuristic — it changes
        // only the order the space is explored, never which verdicts are reachable.
        for &lit in &learnt {
            self.bump_var(lit.var as usize);
        }
        self.decay_var_inc();
        // Reset the scratch: exactly the lower-level literals are still marked.
        for &lit in &learnt[1..] {
            self.seen[lit.var as usize] = false;
        }
        // LBD: the number of distinct decision levels in the clause, measured now
        // while the assignment is still intact.
        let mut levels: Vec<u32> = learnt.iter().map(|l| self.level[l.var as usize]).collect();
        levels.sort_unstable();
        levels.dedup();
        (learnt, btlevel, levels.len() as u32)
    }

    /// Append a learnt clause and start watching its first two literals (already
    /// ordered by `analyze`: `lits[0]` asserting, `lits[1]` highest-level). A
    /// learnt unit has no second watch — it is enqueued at level 0 and never
    /// falsified again, so it needs none. Returns the new clause index.
    pub(super) fn add_learnt(&mut self, learnt: Vec<Lit>, lbd: u32) -> usize {
        let ci = self.clauses.len();
        if learnt.len() >= 2 {
            self.watches[lit_code(learnt[0])].push(ci);
            self.watches[lit_code(learnt[1])].push(ci);
        }
        self.clauses.push(learnt);
        self.lbd.push(lbd);
        ci
    }

    /// Undo every assignment made above decision level `level`.
    pub(super) fn backtrack_to(&mut self, level: u32) {
        if self.decision_level() <= level {
            return;
        }
        let target = self.trail_lim[level as usize];
        while self.trail.len() > target {
            if let Some(v) = self.trail.pop() {
                self.assign[v as usize] = None;
            }
        }
        self.trail_lim.truncate(level as usize);
        self.prop_queue.clear();
    }

    /// The most active unassigned variable (VSIDS), with the lowest index winning
    /// ties. With all activities zero (the initial state) this is just the
    /// lowest-indexed unassigned variable, so early behaviour is deterministic.
    pub(super) fn pick_branch(&self) -> Option<u32> {
        let mut best: Option<u32> = None;
        let mut best_act = f64::NEG_INFINITY;
        for v in 0..self.num_vars {
            if self.assign[v].is_none() && self.activity[v] > best_act {
                best_act = self.activity[v];
                best = Some(v as u32);
            }
        }
        best
    }

    /// Reward a variable for taking part in the current conflict, rescaling all
    /// activities down if this one grows too large for f64.
    pub(super) fn bump_var(&mut self, v: usize) {
        self.activity[v] += self.var_inc;
        if self.activity[v] > ACTIVITY_RESCALE_LIMIT {
            for a in &mut self.activity {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
    }

    /// Grow the bump so that future conflicts outweigh past ones (VSIDS decay).
    pub(super) fn decay_var_inc(&mut self) {
        self.var_inc *= 1.0 / VAR_DECAY;
    }

    pub(super) fn model(&self) -> Vec<bool> {
        (0..self.num_vars)
            .map(|v| self.assign[v].unwrap_or(false))
            .collect()
    }

    /// Solve under the given decision budget.
    pub fn solve(&mut self, budget: u64) -> SatResult {
        // Seed propagation from the unit clauses; an empty clause is immediate
        // unsatisfiability.
        for ci in 0..self.clauses.len() {
            match self.clauses[ci].len() {
                0 => return SatResult::Unsat,
                // A unit clause seeds propagation; a conflict enqueueing it is level-0 UNSAT.
                // (The guard runs `enqueue` for the side effect; a successful enqueue falls
                // through to the no-op arm.)
                1 if !self.enqueue(self.clauses[ci][0], Some(ci)) => return SatResult::Unsat,
                _ => {}
            }
        }
        if self.propagate().is_some() {
            return SatResult::Unsat; // conflict at level 0
        }

        let mut budget_left = budget;
        let start = std::time::Instant::now();
        let mut ticks: u32 = 0;
        loop {
            // Restart? A pure "pause and re-descend": drop the current guesses back
            // to level 0 but keep every learnt clause and all VSIDS activity, so the
            // fresh descent is guided by what the abandoned one discovered. It only
            // reorders the search — models are untouched — so it cannot make a false
            // verdict; and because it never resets the decision budget, total work
            // stays bounded (a stuck search still bottoms out at `Unknown`).
            if self.decision_level() > 0
                && self.conflicts_since_restart >= self.restart_unit * self.luby_v
            {
                self.backtrack_to(0);
                self.conflicts_since_restart = 0;
                self.restarts += 1;
                self.advance_luby();
                // At level 0 with the trail quiescent — the one safe point to prune
                // the learnt-clause pool (no clause above level 0 is a live reason).
                if self.clauses.len() - self.num_original > self.max_learnt {
                    self.reduce_db();
                    self.max_learnt += self.max_learnt / 2;
                }
            }

            let Some(v) = self.pick_branch() else {
                return SatResult::Sat(self.model());
            };
            if budget_left == 0 {
                return SatResult::Unknown;
            }
            budget_left -= 1;
            if timed_out(&start, &mut ticks) {
                return SatResult::Unknown;
            }

            // New decision level: decide v = true.
            self.trail_lim.push(self.trail.len());
            let _ = self.enqueue(Lit::pos(v), None);

            // Propagate; on each conflict, learn a 1-UIP clause and backjump.
            while let Some(confl) = self.propagate() {
                if self.trail_lim.is_empty() {
                    return SatResult::Unsat; // conflict at level 0 ⇒ refuted
                }
                // A conflict chain does not consume the *decision* budget, so guard
                // its runtime with the same wall-clock backstop.
                if timed_out(&start, &mut ticks) {
                    return SatResult::Unknown;
                }
                let (learnt, btlevel, lbd) = self.analyze(confl);
                self.backtrack_to(btlevel);
                let ci = self.add_learnt(learnt, lbd);
                let asserting = self.clauses[ci][0];
                let _ = self.enqueue(asserting, Some(ci));
                self.conflicts_since_restart += 1;
            }
        }
    }

    /// Advance the Luby sequence by one term via Knuth's reluctant doubling, so
    /// `luby_v` holds the next restart multiplier (1,1,2,1,1,2,4,…).
    pub(super) fn advance_luby(&mut self) {
        if self.luby_u & self.luby_u.wrapping_neg() == self.luby_v {
            self.luby_u += 1;
            self.luby_v = 1;
        } else {
            self.luby_v *= 2;
        }
    }

    /// Drop the worse half of the deletable learnt clauses (highest LBD first),
    /// then compact the store. MUST be called only at decision level 0.
    ///
    /// Only *learnt* clauses are ever removed, and never a "glue" clause (LBD ≤ 2)
    /// nor one that is currently a reason for an assigned variable ("locked").
    /// Deleting entailed learnt clauses only forgoes some learned pruning — it can
    /// never remove a model nor an original clause, so `Unsat` stays sound; a
    /// forgotten clause can simply be relearnt. Original clauses keep their indices
    /// (they are contiguous at the front and never removed); learnt-clause indices
    /// are remapped in every `reason` that survives.
    pub(super) fn reduce_db(&mut self) {
        debug_assert_eq!(self.decision_level(), 0, "reduce_db only at level 0");
        let n = self.clauses.len();
        // Locked = the reason clause of any currently-assigned variable.
        let mut locked = vec![false; n];
        for &v in &self.trail {
            if let Some(r) = self.reason[v as usize] {
                locked[r] = true;
            }
        }
        // Deletable learnt clauses, worst (highest LBD) first.
        let mut candidates: Vec<usize> = (self.num_original..n)
            .filter(|&ci| self.lbd[ci] > 2 && !locked[ci])
            .collect();
        candidates.sort_by_key(|&ci| std::cmp::Reverse(self.lbd[ci]));
        let remove_count = candidates.len() / 2;
        if remove_count == 0 {
            return;
        }
        let mut remove = vec![false; n];
        for &ci in candidates.iter().take(remove_count) {
            remove[ci] = true;
        }
        // Compact, preserving order, and record the old→new index map.
        let mut map = vec![usize::MAX; n];
        let mut new_clauses: Vec<Vec<Lit>> = Vec::with_capacity(n - remove_count);
        let mut new_lbd: Vec<u32> = Vec::with_capacity(n - remove_count);
        for ci in 0..n {
            if !remove[ci] {
                map[ci] = new_clauses.len();
                new_clauses.push(std::mem::take(&mut self.clauses[ci]));
                new_lbd.push(self.lbd[ci]);
            }
        }
        self.clauses = new_clauses;
        self.lbd = new_lbd;
        // Remap the reasons of assigned (level-0) variables; each such clause is
        // locked, hence kept, so its new index exists.
        for v in 0..self.num_vars {
            if let Some(r) = self.reason[v] {
                if self.assign[v].is_some() {
                    self.reason[v] = Some(map[r]);
                }
            }
        }
        self.rebuild_watches();
        self.reductions += 1;
    }

    /// Rebuild every watch list from scratch after the clause store was compacted.
    /// Called at level 0, where each surviving clause has a valid pair of non-false
    /// literals to watch (or is satisfied by a true one).
    pub(super) fn rebuild_watches(&mut self) {
        for w in &mut self.watches {
            w.clear();
        }
        for ci in 0..self.clauses.len() {
            if self.clauses[ci].len() >= 2 {
                self.reorder_watches(ci);
                self.watches[lit_code(self.clauses[ci][0])].push(ci);
                self.watches[lit_code(self.clauses[ci][1])].push(ci);
            }
        }
    }

    /// Move up to two non-false literals to indices 0 and 1 so the clause can be
    /// watched consistently at the current (level-0) assignment.
    pub(super) fn reorder_watches(&mut self, ci: usize) {
        let len = self.clauses[ci].len();
        if let Some(k) = (0..len).find(|&k| self.lit_value(self.clauses[ci][k]) != Some(false)) {
            self.clauses[ci].swap(0, k);
        }
        if let Some(k) = (1..len).find(|&k| self.lit_value(self.clauses[ci][k]) != Some(false)) {
            self.clauses[ci].swap(1, k);
        }
    }
}

/// A dense index for a literal (`2*var + polarity`), used to key the watch lists.
pub(super) fn lit_code(l: Lit) -> usize {
    ((l.var as usize) << 1) | (l.neg as usize)
}

/// Wall-clock backstop, checked every 8192 calls so the clock read is negligible.
/// Returns `true` when [`SOLVE_TIME_BUDGET`] is exceeded (⇒ bail to `Unknown`).
pub(super) fn timed_out(start: &std::time::Instant, ticks: &mut u32) -> bool {
    *ticks += 1;
    if *ticks >= 8192 {
        *ticks = 0;
        return start.elapsed() > SOLVE_TIME_BUDGET;
    }
    false
}

#[cfg(test)]
#[path = "sat_tests.rs"]
mod tests;
