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
//! The implementation is deliberately simple: chronological backtracking with
//! unit propagation driven by per-variable occurrence lists. It is complete for
//! the formulas it is given (within the budget) but makes no attempt at the
//! sophistication of a modern CDCL solver — the bit-blasted memory-safety
//! queries are small.

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

/// Default decision budget — generous for the small bit-blasted queries here,
/// but a hard backstop against pathological blow-up.
pub const DEFAULT_BUDGET: u64 = 2_000_000;

/// Wall-clock backstop per `solve`. The decision budget bounds *work* but not
/// *time* — a single hard query (e.g. wide byte-pointer arithmetic in a SIMD
/// search) can grind for many seconds before exhausting 2M decisions and hang the
/// whole analysis. This caps the time instead: a query that runs past the budget
/// bails to `Unknown` (sound — only `Unsat` is ever trusted, so a bail can only
/// weaken a verdict to UNKNOWN or leave it on the linear path, never fabricate a
/// PASS). It is generous enough that ordinary sub-millisecond queries never reach
/// it (so they stay deterministic); it fires only on a pathological grind.
const SOLVE_TIME_BUDGET: std::time::Duration = std::time::Duration::from_millis(250);

/// A DPLL solver over a fixed set of variables and clauses.
pub struct Solver {
    num_vars: usize,
    clauses: Vec<Vec<Lit>>,
    /// `var_clauses[v]` = indices of clauses that mention variable `v`.
    var_clauses: Vec<Vec<usize>>,
    assign: Vec<Option<bool>>,
    /// Variables assigned, in chronological order (for backtracking).
    trail: Vec<u32>,
    /// Variables newly assigned and awaiting propagation.
    prop_queue: Vec<u32>,
}

/// One decision frame for iterative backtracking.
struct Decision {
    var: u32,
    /// Whether the second (negative) phase has been tried.
    second: bool,
    /// Trail length just before the decision was made.
    mark: usize,
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
            trail: Vec::new(),
            prop_queue: Vec::new(),
        }
    }

    /// The truth value of a literal under the current partial assignment.
    fn lit_value(&self, lit: Lit) -> Option<bool> {
        self.assign[lit.var as usize].map(|b| b != lit.neg)
    }

    /// Assign `lit` to true if unassigned. Returns `false` on a direct conflict
    /// (the variable is already assigned the opposite value).
    fn enqueue(&mut self, lit: Lit) -> bool {
        let v = lit.var as usize;
        match self.assign[v] {
            Some(b) => b != lit.neg,
            None => {
                self.assign[v] = Some(!lit.neg);
                self.trail.push(lit.var);
                self.prop_queue.push(lit.var);
                true
            }
        }
    }

    /// Unit-propagate to a fixpoint. Returns `false` if a conflict is reached.
    fn propagate(&mut self) -> bool {
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
                    (0, _) => return false, // all literals false ⇒ conflict
                    (1, Some(unit)) => {
                        // Unit clause: the lone unassigned literal is forced.
                        if !self.enqueue(unit) {
                            return false;
                        }
                    }
                    _ => {}
                }
            }
        }
        true
    }

    /// Undo all assignments made after `mark`, and discard pending propagations.
    fn backtrack_to(&mut self, mark: usize) {
        while self.trail.len() > mark {
            if let Some(v) = self.trail.pop() {
                self.assign[v as usize] = None;
            }
        }
        self.prop_queue.clear();
    }

    /// The lowest-indexed unassigned variable, if any.
    fn pick_branch(&self) -> Option<u32> {
        self.assign.iter().position(|a| a.is_none()).map(|i| i as u32)
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
                    if !self.enqueue(self.clauses[ci][0]) {
                        return SatResult::Unsat;
                    }
                }
                _ => {}
            }
        }
        if !self.propagate() {
            return SatResult::Unsat;
        }

        let mut decisions: Vec<Decision> = Vec::new();
        let mut budget_left = budget;
        let start = std::time::Instant::now();
        let mut ticks: u32 = 0;
        loop {
            let Some(v) = self.pick_branch() else {
                return SatResult::Sat(self.model());
            };
            if budget_left == 0 {
                return SatResult::Unknown;
            }
            budget_left -= 1;
            // Wall-clock backstop (see `SOLVE_TIME_BUDGET`): checked every 8192
            // decisions so the clock read is negligible.
            ticks += 1;
            if ticks >= 8192 {
                ticks = 0;
                if start.elapsed() > SOLVE_TIME_BUDGET {
                    return SatResult::Unknown;
                }
            }

            // Decide v = true first.
            decisions.push(Decision {
                var: v,
                second: false,
                mark: self.trail.len(),
            });
            let _ = self.enqueue(Lit::pos(v));

            // Propagate; on conflict, backtrack (flipping/popping decisions).
            while !self.propagate() {
                loop {
                    let Some(top) = decisions.last_mut() else {
                        return SatResult::Unsat;
                    };
                    let mark = top.mark;
                    let var = top.var;
                    self.backtrack_to(mark);
                    if !top.second {
                        top.second = true;
                        let _ = self.enqueue(Lit::neg(var));
                        break; // re-propagate with the flipped decision
                    }
                    // Both phases exhausted: drop this decision and keep
                    // backtracking.
                    decisions.pop();
                }
            }
        }
    }
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
    fn budget_zero_on_open_problem_is_unknown() {
        // A problem needing at least one decision, with budget 0 ⇒ Unknown.
        let clauses = vec![vec![Lit::pos(0), Lit::pos(1)]];
        let mut s = Solver::new(2, clauses);
        assert_eq!(s.solve(0), SatResult::Unknown);
    }
}
