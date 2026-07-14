//! Proof trees and counterexamples — the evidence behind a verdict.
//!
//! For a `PASS`, a [`ProofTree`] records *why* an obligation holds, down to the
//! axioms, abstract-interpretation invariants, and `unsat` results it rests
//! on. For a `FAIL`, a [`CounterExample`] gives a concrete [`Model`] (a value
//! for every relevant symbol) and an optional trace. Both are designed to be
//! rendered by `csolver-report` and to be machine-checkable in principle.

use crate::BitVector;

/// A structured justification for one proof step.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Justification {
    /// A primitive fact taken as given by the proof system itself.
    Axiom {
        /// Name of the axiom (e.g. "alloc-returns-aligned").
        name: String,
    },
    /// Established by an abstract-interpretation invariant.
    AbstractInterpretation {
        /// The domain that produced the invariant (e.g. "interval").
        domain: String,
        /// The invariant as rendered (e.g. "0 <= i <= len").
        invariant: String,
    },
    /// Established because the negation of the goal was found **unsatisfiable** by the
    /// in-house decision engine (the CDCL/bit-precise or linear procedure), optionally
    /// with an unsat core.
    Unsat {
        /// The decision procedure that decided it (e.g. `internal-linear`, `symbolic-memory`).
        solver: String,
        /// The relevant subset of asserted facts, if extracted.
        unsat_core: Vec<String>,
    },
    /// Established by exhaustive case analysis over the listed cases.
    CaseSplit {
        /// The cases that were each discharged.
        cases: Vec<String>,
    },
    /// Discharged relative to a named [`crate::Assumption`].
    ByAssumption {
        /// The id of the assumption relied upon.
        assumption_id: String,
    },
}

/// One node of a proof: a conclusion, the rule that justifies it, and the
/// sub-proofs of its premises.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofStep {
    /// The proposition established by this step.
    pub conclusion: String,
    /// Why it follows.
    pub justification: Justification,
    /// Sub-proofs this step depends on (empty for leaves).
    pub premises: Vec<ProofStep>,
}

impl ProofStep {
    /// A leaf step (no premises).
    pub fn leaf(conclusion: impl Into<String>, justification: Justification) -> Self {
        ProofStep {
            conclusion: conclusion.into(),
            justification,
            premises: Vec::new(),
        }
    }

    /// Number of leaf steps (axioms / solver results) the step rests on.
    pub fn leaf_count(&self) -> usize {
        if self.premises.is_empty() {
            1
        } else {
            self.premises.iter().map(ProofStep::leaf_count).sum()
        }
    }
}

/// A complete proof for one obligation: its root step plus the assumptions it
/// depends on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofTree {
    /// The root conclusion's proof.
    pub root: ProofStep,
    /// Ids of assumptions the proof depends on (resolved against the report's
    /// assumption table).
    pub assumptions: Vec<String>,
}

impl ProofTree {
    /// Build a proof tree from a root step with no assumptions.
    pub fn new(root: ProofStep) -> Self {
        ProofTree {
            root,
            assumptions: Vec::new(),
        }
    }

    /// Attach the assumptions this proof depends on.
    pub fn with_assumptions(mut self, assumptions: Vec<String>) -> Self {
        self.assumptions = assumptions;
        self
    }
}

/// A single name → value assignment within a counterexample model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assignment {
    /// The symbol being assigned (e.g. "idx", "rsi", "%4").
    pub name: String,
    /// Its concrete value.
    pub value: BitVector,
}

/// A satisfying assignment that witnesses a violation.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Model {
    /// The concrete assignments.
    pub assignments: Vec<Assignment>,
}

impl Model {
    /// Look up the value assigned to `name`, if any.
    pub fn get(&self, name: &str) -> Option<BitVector> {
        self.assignments
            .iter()
            .find(|a| a.name == name)
            .map(|a| a.value)
    }
}

/// A concrete witness that an obligation is violated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CounterExample {
    /// Human-readable summary of the violation.
    pub summary: String,
    /// The concrete model that triggers it.
    pub model: Model,
    /// An optional ordered trace of program points leading to the violation.
    pub trace: Vec<String>,
}

impl CounterExample {
    /// A counterexample with just a summary and a model.
    pub fn new(summary: impl Into<String>, model: Model) -> Self {
        CounterExample {
            summary: summary.into(),
            model,
            trace: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leaf_count_counts_axioms() {
        let tree = ProofStep {
            conclusion: "0 <= i < len".into(),
            justification: Justification::CaseSplit {
                cases: vec!["i == 0".into(), "i > 0".into()],
            },
            premises: vec![
                ProofStep::leaf(
                    "base case",
                    Justification::Axiom { name: "zero".into() },
                ),
                ProofStep::leaf(
                    "step case",
                    Justification::Unsat {
                        solver: "internal".into(),
                        unsat_core: vec![],
                    },
                ),
            ],
        };
        assert_eq!(tree.leaf_count(), 2);
    }

    #[test]
    fn model_lookup() {
        let m = Model {
            assignments: vec![Assignment {
                name: "idx".into(),
                value: BitVector::new(64, 42),
            }],
        };
        assert_eq!(m.get("idx").map(|v| v.unsigned()), Some(42));
        assert_eq!(m.get("nope"), None);
    }
}
