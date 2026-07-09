//! A small, self-contained DPLL SAT solver (pure Rust, no dependencies).
//!
//! It exists so the bit-precise decision procedure ([`crate::bitprecise`]) can
//! decide bit-vector formulas exactly, without binding an external C/C++ solver
//! — keeping the whole tool pure Rust and fast to build.
//!
//! ## Soundness contract
//!
//! The only result the verifier *trusts* is [`SatResult::Unsat`]: it is emitted
//! only after the search has exhausted the whole assignment space without
//! finding a model, which a correct DPLL guarantees means the formula is truly
//! unsatisfiable. To stay affordable, the search is bounded by a decision
//! budget; when the budget is exhausted the solver returns
//! [`SatResult::Unknown`] rather than guessing. A caller proving a goal by
//! refutation therefore treats anything other than `Unsat` as "not proved"
//! (never as a refutation), so a budget bail can only ever lose precision, never
//! soundness.
//!
//! The engine is CDCL (conflict-driven clause learning) with the usual modern
//! machinery: two-watched-literal unit propagation, **1-UIP** conflict analysis
//! that derives an *asserting* learnt clause and backjumps non-chronologically to
//! its assertion level, a VSIDS branch heuristic, Luby restarts, and LBD-based
//! deletion that keeps the learnt-clause database bounded.
//!
//! None of that touches soundness. Every learnt clause is a resolvent of clauses
//! already present, hence a logical consequence of the input — it removes no
//! models. VSIDS and restarts only reorder the search. Deletion only ever drops
//! *learnt* clauses (never an original, never a live reason), so it can forgo
//! pruning but never a model. Thus `Unsat` stays exactly as trustworthy as under
//! plain DPLL (the soundness contract above is preserved throughout), and the
//! whole thing stays pure Rust with no external solver.

/// A boolean literal: a variable together with a polarity.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Lit {
    /// The 0-based variable index.
    pub var: u32,
    /// Whether the literal is negated (`true` ⇒ the literal is `¬var`).
    pub neg: bool,
}

impl Lit {
    /// The positive literal of a variable.
    pub fn pos(var: u32) -> Lit {
        Lit { var, neg: false }
    }

    /// The negative literal of a variable.
    pub fn neg(var: u32) -> Lit {
        Lit { var, neg: true }
    }

    /// This literal with its polarity flipped.
    pub fn negated(self) -> Lit {
        Lit {
            var: self.var,
            neg: !self.neg,
        }
    }
}

/// The outcome of a solve.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SatResult {
    /// Satisfiable, with a total model (`model[v]` is the value of variable `v`).
    Sat(Vec<bool>),
    /// Proven unsatisfiable (the trusted result).
    Unsat,
    /// The decision budget was exhausted before a verdict was reached.
    Unknown,
}

/// Default decision budget. With the wall-clock valve (`SOLVE_TIME_BUDGET`) as the
/// real liveness backstop, this no longer needs to be huge — a query that would do
/// more work than this is a pathological grind the wall-clock already caps on time.
pub const DEFAULT_BUDGET: u64 = 200_000;

/// VSIDS decay: each conflict multiplies the activity bump by `1/VAR_DECAY`, so a
/// bump loses ~5% of its relative weight per later conflict. The classic MiniSat
/// value; it makes the branch order track *recent* conflict structure.
const VAR_DECAY: f64 = 0.95;

/// When any activity (or the bump) exceeds this, all activities are rescaled down
/// by `1e-100`. Ratios — the only thing that matters — are preserved, and the
/// f64 range can never overflow.
const ACTIVITY_RESCALE_LIMIT: f64 = 1e100;

/// Conflicts per Luby unit: the restart interval is `RESTART_UNIT * luby(n)`. Kept
/// modest because the bit-blasted queries are small — a restart should be able to
/// fire on a genuinely hard one, but never churn on an easy one.
const RESTART_UNIT: u64 = 50;

/// Floor for the learnt-clause budget, so small formulas still permit a healthy
/// pool before any reduction kicks in.
const MIN_LEARNT_LIMIT: usize = 100;

/// Wall-clock backstop per `solve`. The decision budget bounds *work* but not
/// *time* — a single hard query (e.g. wide byte-pointer arithmetic in a SIMD
/// search) can grind for many seconds before exhausting 2M decisions and hang the
/// whole analysis. This caps the time instead: a query that runs past the budget
/// bails to `Unknown` (sound — only `Unsat` is ever trusted, so a bail can only
/// weaken a verdict to UNKNOWN or leave it on the linear path, never fabricate a
/// PASS). It is generous enough that ordinary sub-millisecond queries never reach
/// it (so they stay deterministic); it fires only on a pathological grind.
const SOLVE_TIME_BUDGET: std::time::Duration = std::time::Duration::from_millis(250);

/// A CDCL solver over a fixed set of variables and clauses.
pub struct Solver {
    num_vars: usize,
    clauses: Vec<Vec<Lit>>,
    /// Two-watched-literal scheme: `watches[lit_code(l)]` holds every clause that
    /// currently watches literal `l`. A clause is visited only when one of its two
    /// watched literals becomes false, so propagation touches far fewer clauses
    /// than a full occurrence list. Each length-≥2 clause watches `lits[0]` and
    /// `lits[1]`; units and the empty clause are handled directly at seed time.
    watches: Vec<Vec<usize>>,
    assign: Vec<Option<bool>>,
    /// Decision level at which each variable was assigned (valid while assigned).
    level: Vec<u32>,
    /// Antecedent: the clause that *forced* a variable during propagation, or
    /// `None` for a decision (or a level-0 unit seed). Drives 1-UIP analysis.
    reason: Vec<Option<usize>>,
    /// Variables assigned, in chronological order (for backtracking).
    trail: Vec<u32>,
    /// `trail_lim[d]` = trail length just before the `(d+1)`-th decision; its
    /// length is the current decision level.
    trail_lim: Vec<usize>,
    /// Variables newly assigned and awaiting propagation.
    prop_queue: Vec<u32>,
    /// Reusable "touched in this conflict analysis" scratch (avoids a per-conflict
    /// allocation); always fully reset before `analyze` returns.
    seen: Vec<bool>,
    /// VSIDS activity per variable: how often it has recently taken part in a
    /// conflict. The next decision branches on the most active unassigned variable.
    activity: Vec<f64>,
    /// The current activity bump. It grows by `1/VAR_DECAY` each conflict, which is
    /// an O(1) way to make older bumps decay relative to newer ones.
    var_inc: f64,
    /// Conflicts seen since the last restart; when it reaches the current Luby
    /// threshold the search restarts (backjumps to level 0, keeping what it learnt).
    conflicts_since_restart: u64,
    /// Reluctant-doubling state generating the Luby sequence 1,1,2,1,1,2,4,… — the
    /// restart interval (in units of [`RESTART_UNIT`] conflicts).
    luby_u: u64,
    luby_v: u64,
    /// How many restarts have happened (telemetry; asserted on in tests).
    restarts: u64,
    /// Clauses `[0, num_original)` are the input; they are never deleted and keep
    /// their indices for the whole solve. Learnt clauses are appended after and are
    /// the only deletion candidates.
    num_original: usize,
    /// Per-clause LBD (literal block distance = distinct decision levels at learning
    /// time). Lower is better; `≤ 2` clauses are "glue" and kept forever. Parallel
    /// to `clauses`. Originals carry `0` (unused — they are never candidates).
    lbd: Vec<u32>,
    /// When the learnt-clause count exceeds this, the next level-0 restart reduces
    /// the database; the bound then grows so reductions become rarer.
    max_learnt: usize,
    /// How many database reductions have happened (telemetry; asserted on in tests).
    reductions: u64,
}

impl Solver {
    /// Build a solver from a variable count and a clause list.
    pub fn new(num_vars: usize, clauses: Vec<Vec<Lit>>) -> Solver {
        let mut watches = vec![Vec::new(); 2 * num_vars];
        for (ci, clause) in clauses.iter().enumerate() {
            if clause.len() >= 2 {
                watches[lit_code(clause[0])].push(ci);
                watches[lit_code(clause[1])].push(ci);
            }
        }
        let num_original = clauses.len();
        let lbd = vec![0; num_original];
        Solver {
            num_vars,
            clauses,
            watches,
            assign: vec![None; num_vars],
            level: vec![0; num_vars],
            reason: vec![None; num_vars],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            prop_queue: Vec::new(),
            seen: vec![false; num_vars],
            activity: vec![0.0; num_vars],
            var_inc: 1.0,
            conflicts_since_restart: 0,
            luby_u: 1,
            luby_v: 1,
            restarts: 0,
            num_original,
            lbd,
            max_learnt: (num_original / 3).max(MIN_LEARNT_LIMIT),
            reductions: 0,
        }
    }

    /// The current decision level (number of decisions on the trail).
    fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    /// The truth value of a literal under the current partial assignment.
    fn lit_value(&self, lit: Lit) -> Option<bool> {
        self.assign[lit.var as usize].map(|b| b != lit.neg)
    }

    /// Assign `lit` to true if unassigned, recording its decision level and the
    /// `reason` clause that forced it (`None` for a decision). Returns `false` on
    /// a direct conflict (the variable already holds the opposite value).
    fn enqueue(&mut self, lit: Lit, reason: Option<usize>) -> bool {
        let v = lit.var as usize;
        match self.assign[v] {
            Some(b) => b != lit.neg,
            None => {
                self.assign[v] = Some(!lit.neg);
                self.level[v] = self.decision_level();
                self.reason[v] = reason;
                self.trail.push(lit.var);
                self.prop_queue.push(lit.var);
                true
            }
        }
    }

    /// Unit-propagate to a fixpoint using two-watched literals. Returns the index
    /// of a falsified clause on conflict, else `None`.
    ///
    /// When a variable is assigned, exactly one literal per polarity becomes
    /// false; we visit only the clauses watching that false literal. For each such
    /// clause we try to slide the watch onto any non-false literal; failing that
    /// the clause is unit (propagate its other watch) or, if that too is false, in
    /// conflict.
    fn propagate(&mut self) -> Option<usize> {
        while let Some(v) = self.prop_queue.pop() {
            // The literal that just became false for this variable.
            let false_lit = Lit {
                var: v,
                neg: self.assign[v as usize] == Some(true),
            };
            let fc = lit_code(false_lit);
            // Take the watch list out so we can mutate other lists / clauses while
            // walking it; `keep` is rebuilt as the retained watchers of `false_lit`.
            let watchers = std::mem::take(&mut self.watches[fc]);
            let mut keep: Vec<usize> = Vec::with_capacity(watchers.len());
            let mut conflict: Option<usize> = None;
            for &ci in &watchers {
                if conflict.is_some() {
                    keep.push(ci); // retain the untouched tail unchanged
                    continue;
                }
                // Normalise so the false watched literal sits at index 1.
                if self.clauses[ci][0] == false_lit {
                    self.clauses[ci].swap(0, 1);
                }
                // If the other watch is already true, the clause is satisfied.
                let other = self.clauses[ci][0];
                if self.lit_value(other) == Some(true) {
                    keep.push(ci);
                    continue;
                }
                // Look for a non-false literal beyond the two watches to watch next.
                let mut replacement = None;
                for k in 2..self.clauses[ci].len() {
                    if self.lit_value(self.clauses[ci][k]) != Some(false) {
                        replacement = Some(k);
                        break;
                    }
                }
                if let Some(k) = replacement {
                    self.clauses[ci].swap(1, k);
                    let new_watch = self.clauses[ci][1];
                    self.watches[lit_code(new_watch)].push(ci);
                    // dropped from `false_lit`'s list (not pushed to `keep`)
                    continue;
                }
                // No replacement: `other` (at index 0) is the last hope.
                keep.push(ci);
                match self.lit_value(other) {
                    Some(false) => conflict = Some(ci), // all literals false
                    None => {
                        self.enqueue(other, Some(ci));
                    }
                    Some(true) => {} // handled above; unreachable here
                }
            }
            self.watches[fc] = keep;
            if let Some(ci) = conflict {
                return Some(ci);
            }
        }
        None
    }

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
    fn analyze(&mut self, confl: usize) -> (Vec<Lit>, u32, u32) {
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
    fn add_learnt(&mut self, learnt: Vec<Lit>, lbd: u32) -> usize {
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
    fn backtrack_to(&mut self, level: u32) {
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
    fn pick_branch(&self) -> Option<u32> {
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
    fn bump_var(&mut self, v: usize) {
        self.activity[v] += self.var_inc;
        if self.activity[v] > ACTIVITY_RESCALE_LIMIT {
            for a in &mut self.activity {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
    }

    /// Grow the bump so that future conflicts outweigh past ones (VSIDS decay).
    fn decay_var_inc(&mut self) {
        self.var_inc *= 1.0 / VAR_DECAY;
    }

    fn model(&self) -> Vec<bool> {
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
                1 => {
                    if !self.enqueue(self.clauses[ci][0], Some(ci)) {
                        return SatResult::Unsat;
                    }
                }
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
                && self.conflicts_since_restart >= RESTART_UNIT * self.luby_v
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
    fn advance_luby(&mut self) {
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
    fn reduce_db(&mut self) {
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
    fn rebuild_watches(&mut self) {
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
    fn reorder_watches(&mut self, ci: usize) {
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
fn lit_code(l: Lit) -> usize {
    ((l.var as usize) << 1) | (l.neg as usize)
}

/// Wall-clock backstop, checked every 8192 calls so the clock read is negligible.
/// Returns `true` when [`SOLVE_TIME_BUDGET`] is exceeded (⇒ bail to `Unknown`).
fn timed_out(start: &std::time::Instant, ticks: &mut u32) -> bool {
    *ticks += 1;
    if *ticks >= 8192 {
        *ticks = 0;
        return start.elapsed() > SOLVE_TIME_BUDGET;
    }
    false
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]
    use super::*;

    fn check_model(clauses: &[Vec<Lit>], model: &[bool]) -> bool {
        clauses.iter().all(|c| {
            c.iter()
                .any(|l| model[l.var as usize] != l.neg)
        })
    }

    #[test]
    fn empty_clause_is_unsat() {
        let mut s = Solver::new(1, vec![vec![]]);
        assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
    }

    #[test]
    fn no_clauses_is_sat() {
        let mut s = Solver::new(3, vec![]);
        assert!(matches!(s.solve(DEFAULT_BUDGET), SatResult::Sat(_)));
    }

    #[test]
    fn unit_contradiction_is_unsat() {
        // (x) ∧ (¬x)
        let mut s = Solver::new(1, vec![vec![Lit::pos(0)], vec![Lit::neg(0)]]);
        assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
    }

    #[test]
    fn simple_sat_has_valid_model() {
        // (x ∨ y) ∧ (¬x ∨ z)
        let clauses = vec![
            vec![Lit::pos(0), Lit::pos(1)],
            vec![Lit::neg(0), Lit::pos(2)],
        ];
        let mut s = Solver::new(3, clauses.clone());
        match s.solve(DEFAULT_BUDGET) {
            SatResult::Sat(m) => assert!(check_model(&clauses, &m)),
            other => panic!("expected SAT, got {other:?}"),
        }
    }

    #[test]
    fn pigeonhole_2_into_1_is_unsat() {
        // Two pigeons, one hole: p0, p1 each must be in hole 0, but not both.
        // vars: x0 = pigeon0 in hole0, x1 = pigeon1 in hole0.
        // each pigeon in the hole: (x0), (x1); not both: (¬x0 ∨ ¬x1).
        let clauses = vec![
            vec![Lit::pos(0)],
            vec![Lit::pos(1)],
            vec![Lit::neg(0), Lit::neg(1)],
        ];
        let mut s = Solver::new(2, clauses);
        assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
    }

    #[test]
    fn xor_chain_unsat() {
        // x0=x1, x1=x2, x2≠x0 — unsatisfiable.
        // x=y encoded (¬x∨y)(x∨¬y); x≠y encoded (x∨y)(¬x∨¬y).
        let clauses = vec![
            vec![Lit::neg(0), Lit::pos(1)],
            vec![Lit::pos(0), Lit::neg(1)],
            vec![Lit::neg(1), Lit::pos(2)],
            vec![Lit::pos(1), Lit::neg(2)],
            vec![Lit::pos(2), Lit::pos(0)],
            vec![Lit::neg(2), Lit::neg(0)],
        ];
        let mut s = Solver::new(3, clauses);
        assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
    }

    #[test]
    fn pigeonhole_4_into_3_is_unsat() {
        // 4 pigeons into 3 holes — the smallest hole-principle instance that
        // actually forces conflict-driven learning + backjumping. var(p,h) = p*3+h.
        let v = |p: u32, h: u32| p * 3 + h;
        let mut clauses = Vec::new();
        // each pigeon sits in some hole
        for p in 0..4 {
            clauses.push((0..3).map(|h| Lit::pos(v(p, h))).collect());
        }
        // no two pigeons share a hole
        for h in 0..3 {
            for p1 in 0..4 {
                for p2 in (p1 + 1)..4 {
                    clauses.push(vec![Lit::neg(v(p1, h)), Lit::neg(v(p2, h))]);
                }
            }
        }
        let mut s = Solver::new(12, clauses);
        assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
    }

    /// Pigeonhole `pigeons` into `holes` as a CNF over vars `v(p,h)=p*holes+h`.
    fn pigeonhole(pigeons: u32, holes: u32) -> (usize, Vec<Vec<Lit>>) {
        let v = |p: u32, h: u32| p * holes + h;
        let mut clauses = Vec::new();
        for p in 0..pigeons {
            clauses.push((0..holes).map(|h| Lit::pos(v(p, h))).collect());
        }
        for h in 0..holes {
            for p1 in 0..pigeons {
                for p2 in (p1 + 1)..pigeons {
                    clauses.push(vec![Lit::neg(v(p1, h)), Lit::neg(v(p2, h))]);
                }
            }
        }
        ((pigeons * holes) as usize, clauses)
    }

    #[test]
    fn restarts_fire_on_a_hard_unsat_without_changing_the_verdict() {
        // Pigeonhole 6→5 is unsatisfiable and needs well over RESTART_UNIT
        // conflicts, so at least one restart must fire — and the verdict must
        // still be exactly Unsat (a restart only reorders the search).
        let (n, clauses) = pigeonhole(6, 5);
        let mut s = Solver::new(n, clauses);
        assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
        assert!(s.restarts > 0, "expected a restart, got {}", s.restarts);
    }

    #[test]
    fn clause_deletion_fires_without_changing_the_verdict() {
        // Pigeonhole 6→5 learns enough clauses to cross the reduction threshold, so
        // at least one database reduction must run — and the verdict must still be
        // exactly Unsat. Deleting learnt clauses may only forgo pruning, never a
        // model nor an original clause.
        let (n, clauses) = pigeonhole(6, 5);
        let mut s = Solver::new(n, clauses);
        assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
        assert!(s.reductions > 0, "expected a reduction, got {}", s.reductions);
    }

    #[test]
    fn learned_clause_never_loses_a_model() {
        // A satisfiable instance that drives several conflicts before a model is
        // found; the learnt clauses must not prune the (only) solution.
        // (a∨b)(¬a∨c)(¬b∨c)(¬c∨d)(a∨¬d∨e) with a forced route.
        let clauses = vec![
            vec![Lit::pos(0), Lit::pos(1)],
            vec![Lit::neg(0), Lit::pos(2)],
            vec![Lit::neg(1), Lit::pos(2)],
            vec![Lit::neg(2), Lit::pos(3)],
            vec![Lit::pos(0), Lit::neg(3), Lit::pos(4)],
        ];
        let mut s = Solver::new(5, clauses.clone());
        match s.solve(DEFAULT_BUDGET) {
            SatResult::Sat(m) => assert!(check_model(&clauses, &m)),
            other => panic!("expected SAT, got {other:?}"),
        }
    }

    #[test]
    fn conflict_at_level_zero_after_learning_is_unsat() {
        // Forces a learnt unit that then propagates into a top-level conflict.
        // (x∨y)(x∨¬y)(¬x∨z)(¬x∨¬z) ⇒ x must be false (first two) and true
        // (last two, once y/z resolved) — unsatisfiable via learning.
        let clauses = vec![
            vec![Lit::pos(0), Lit::pos(1)],
            vec![Lit::pos(0), Lit::neg(1)],
            vec![Lit::neg(0), Lit::pos(2)],
            vec![Lit::neg(0), Lit::neg(2)],
        ];
        let mut s = Solver::new(3, clauses);
        assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
    }

    #[test]
    fn budget_zero_on_open_problem_is_unknown() {
        // A problem needing at least one decision, with budget 0 ⇒ Unknown.
        let clauses = vec![vec![Lit::pos(0), Lit::pos(1)]];
        let mut s = Solver::new(2, clauses);
        assert_eq!(s.solve(0), SatResult::Unknown);
    }

    /// Brute-force oracle: is `clauses` satisfiable over `n` variables?
    fn brute_force_sat(n: u32, clauses: &[Vec<Lit>]) -> bool {
        (0u32..(1u32 << n)).any(|mask| {
            let model: Vec<bool> = (0..n).map(|v| mask & (1 << v) != 0).collect();
            check_model(clauses, &model)
        })
    }

    #[test]
    fn cdcl_agrees_with_brute_force_on_random_instances() {
        // The decisive "nothing is lost" guard: over many random small 3-CNFs,
        // CDCL's verdict must match an exhaustive truth-table oracle exactly —
        // in particular it must NEVER report Unsat on a satisfiable instance
        // (a false refutation) nor Sat with an invalid model.
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut rng = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _ in 0..4000 {
            let n: u32 = 3 + (rng() % 4) as u32; // 3..=6 vars
            let m = 1 + (rng() % 14) as usize; // 1..=14 clauses
            let clauses: Vec<Vec<Lit>> = (0..m)
                .map(|_| {
                    let k = 1 + (rng() % 3) as usize; // 1..=3 literals
                    (0..k)
                        .map(|_| {
                            let var = (rng() % n as u64) as u32;
                            if rng() & 1 == 0 { Lit::pos(var) } else { Lit::neg(var) }
                        })
                        .collect()
                })
                .collect();

            let oracle = brute_force_sat(n, &clauses);
            let mut s = Solver::new(n as usize, clauses.clone());
            match s.solve(DEFAULT_BUDGET) {
                SatResult::Sat(model) => {
                    assert!(oracle, "CDCL said SAT but oracle says UNSAT: {clauses:?}");
                    assert!(
                        check_model(&clauses, &model),
                        "CDCL returned an invalid model: {clauses:?} / {model:?}"
                    );
                }
                SatResult::Unsat => {
                    assert!(!oracle, "CDCL falsely refuted a satisfiable instance: {clauses:?}");
                }
                SatResult::Unknown => panic!("small instance hit the budget: {clauses:?}"),
            }
        }
    }
}
