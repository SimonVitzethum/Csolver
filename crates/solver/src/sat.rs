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
    /// restart interval (in units of `restart_unit` conflicts).
    luby_u: u64,
    luby_v: u64,
    /// Conflicts per Luby unit (default [`RESTART_UNIT`]). A field so tests can drive
    /// the restart/reduction machinery hard on tiny instances.
    restart_unit: u64,
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
            restart_unit: RESTART_UNIT,
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
}

#[path = "sat_learn.rs"]
mod sat_learn;
use sat_learn::*;
