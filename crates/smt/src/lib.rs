//! # csolver-smt — SMT backend abstraction (M0 stub)
//!
//! A uniform [`SmtSolver`] interface over the bit-vector + array + UF theories,
//! with pluggable backends (Z3, Bitwuzla, CVC5) selected at runtime. A portable
//! [`NullSolver`] that answers [`SatResult::Unknown`] ships now so the rest of
//! the pipeline and CI work without any external solver installed.
//!
//! ## Status
//!
//! The trait and the [`NullSolver`] are real; the external backends (and a
//! small internal bit-blasting fallback) arrive in milestones M2–M3.

use std::fmt;

/// An opaque sort handle vended by a solver.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Sort(pub u32);

/// An opaque term handle vended by a solver.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Term(pub u32);

/// The theory sort to declare.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SortKind {
    /// A boolean.
    Bool,
    /// A bit-vector of the given width.
    BitVec(u32),
    /// An array from `index` width to `element` width.
    Array {
        /// Index bit width.
        index: u32,
        /// Element bit width.
        element: u32,
    },
}

/// The result of a satisfiability check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatResult {
    /// Satisfiable, with an opaque model handle the caller can query.
    Sat,
    /// Unsatisfiable, optionally with an unsat core (rendered).
    Unsat {
        /// The relevant subset of assertions, if extracted.
        core: Vec<String>,
    },
    /// The solver could not decide.
    Unknown {
        /// Why (timeout, incompleteness, unsupported theory…).
        reason: String,
    },
}

/// A push/pop-scoped SMT solver over the bit-vector/array/UF theories.
pub trait SmtSolver {
    /// A short backend name for reports (e.g. `"z3"`).
    fn name(&self) -> &str;

    /// Declare a sort.
    fn declare_sort(&mut self, kind: SortKind) -> Sort;

    /// Declare a fresh constant of the given sort, returning its term.
    fn declare_const(&mut self, name: &str, sort: Sort) -> Term;

    /// Assert that `term` (of boolean sort) holds.
    fn assert(&mut self, term: Term);

    /// Check satisfiability of the current assertion stack.
    fn check(&mut self) -> SatResult;

    /// Push an assertion scope.
    fn push(&mut self);

    /// Pop an assertion scope.
    fn pop(&mut self);
}

/// A solver that declares everything but decides nothing — it always returns
/// [`SatResult::Unknown`]. Used as the default backend when no external solver
/// is configured, keeping the pipeline sound (every query degrades to
/// `UNKNOWN`, never a false `PASS`).
#[derive(Debug, Default)]
pub struct NullSolver {
    next: u32,
    scopes: usize,
}

impl NullSolver {
    /// Create a null solver.
    pub fn new() -> Self {
        NullSolver::default()
    }

    fn fresh(&mut self) -> u32 {
        let id = self.next;
        self.next += 1;
        id
    }
}

impl SmtSolver for NullSolver {
    fn name(&self) -> &str {
        "null"
    }

    fn declare_sort(&mut self, _kind: SortKind) -> Sort {
        Sort(self.fresh())
    }

    fn declare_const(&mut self, _name: &str, _sort: Sort) -> Term {
        Term(self.fresh())
    }

    fn assert(&mut self, _term: Term) {}

    fn check(&mut self) -> SatResult {
        SatResult::Unknown {
            reason: "no decision procedure configured (NullSolver)".into(),
        }
    }

    fn push(&mut self) {
        self.scopes += 1;
    }

    fn pop(&mut self) {
        self.scopes = self.scopes.saturating_sub(1);
    }
}

impl fmt::Display for SatResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SatResult::Sat => f.write_str("sat"),
            SatResult::Unsat { .. } => f.write_str("unsat"),
            SatResult::Unknown { reason } => write!(f, "unknown ({reason})"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn null_solver_is_sound_unknown() {
        let mut s = NullSolver::new();
        let bv = s.declare_sort(SortKind::BitVec(64));
        let x = s.declare_const("x", bv);
        s.push();
        s.assert(x);
        assert!(matches!(s.check(), SatResult::Unknown { .. }));
        s.pop();
    }
}
