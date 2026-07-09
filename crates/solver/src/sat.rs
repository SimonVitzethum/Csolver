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
//! The engine is CDCL (conflict-driven clause learning): unit propagation over
//! per-variable occurrence lists, and on every conflict a **1-UIP** analysis
//! that derives an *asserting* learnt clause and backjumps non-chronologically
//! to its assertion level. Every learnt clause is a resolvent of clauses already
//! present, hence a logical consequence of the input — it removes no models, so
//! `Unsat` stays exactly as trustworthy as under plain DPLL (the soundness
//! contract above is preserved; learning only prunes the search, never the
//! model set). A learnt-clause store that only grows within a single bounded
//! `solve` keeps the whole thing pure Rust with no external solver.

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
    /// `var_clauses[v]` = indices of clauses that mention variable `v` (kept in
    /// sync as learnt clauses are appended).
    var_clauses: Vec<Vec<usize>>,
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
}

impl Solver {
    /// Build a solver from a variable count and a clause list.
    pub fn new(num_vars: usize, clauses: Vec<Vec<Lit>>) -> Solver {
        let mut var_clauses = vec![Vec::new(); num_vars];
        for (ci, clause) in clauses.iter().enumerate() {
            for lit in clause {
                let v = lit.var as usize;
                // Avoid recording the same clause twice for a repeated variable.
                if var_clauses[v].last() != Some(&ci) {
                    var_clauses[v].push(ci);
                }
            }
        }
        Solver {
            num_vars,
            clauses,
            var_clauses,
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

    /// Unit-propagate to a fixpoint. Returns the index of a falsified clause on
    /// conflict, else `None`.
    fn propagate(&mut self) -> Option<usize> {
        while let Some(v) = self.prop_queue.pop() {
            // Re-examine every clause mentioning `v`. We index by position so we
            // do not hold a borrow of `self.var_clauses` across `enqueue`.
            let n = self.var_clauses[v as usize].len();
            for k in 0..n {
                let ci = self.var_clauses[v as usize][k];
                // Scan the clause: is it satisfied, and how many unassigned lits?
                let mut satisfied = false;
                let mut unassigned = None;
                let mut count = 0u32;
                for &lit in &self.clauses[ci] {
                    match self.lit_value(lit) {
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        Some(false) => {}
                        None => {
                            count += 1;
                            unassigned = Some(lit);
                        }
                    }
                }
                if satisfied {
                    continue;
                }
                match (count, unassigned) {
                    (0, _) => return Some(ci), // all literals false ⇒ conflict
                    (1, Some(unit)) => {
                        // Unit clause: the lone unassigned literal is forced, with
                        // `ci` as its antecedent. It is unassigned, so this never
                        // conflicts here.
                        self.enqueue(unit, Some(ci));
                    }
                    _ => {}
                }
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
    fn analyze(&mut self, confl: usize) -> (Vec<Lit>, u32) {
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
        // Backjump to the second-highest level in the clause (0 for a unit).
        let mut btlevel = 0u32;
        for &lit in &learnt[1..] {
            btlevel = btlevel.max(self.level[lit.var as usize]);
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
        (learnt, btlevel)
    }

    /// Append a learnt clause and index it in the occurrence lists. Returns its
    /// clause index; the asserting literal is at position 0.
    fn add_learnt(&mut self, learnt: Vec<Lit>) -> usize {
        let ci = self.clauses.len();
        for &lit in &learnt {
            let v = lit.var as usize;
            if self.var_clauses[v].last() != Some(&ci) {
                self.var_clauses[v].push(ci);
            }
        }
        self.clauses.push(learnt);
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
                let (learnt, btlevel) = self.analyze(confl);
                self.backtrack_to(btlevel);
                let ci = self.add_learnt(learnt);
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
