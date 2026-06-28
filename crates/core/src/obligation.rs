//! Proof obligations and their results.
//!
//! A [`ProofObligation`] is the unit of work for the verifier: one
//! [`crate::SafetyProperty`] that must hold at one [`crate::Location`]. Trying
//! to discharge it yields an [`ObligationResult`], which is the *only* place a
//! proof, a counterexample, or a residual can enter a report.

use crate::{CounterExample, Location, ProofTree, SafetyProperty};
use std::fmt;

/// A stable identifier for a proof obligation within a verification run.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ObligationId(pub u32);

impl fmt::Display for ObligationId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PO{}", self.0)
    }
}

/// One memory-safety property that must hold at one program location.
///
/// The `predicate` is a human-readable rendering of the condition that, if
/// valid, establishes the property (e.g. `0 <= idx && idx < len`). The
/// machine-checkable form of the predicate lives in higher layers
/// (`csolver-solver`); keeping only the rendering here avoids a dependency
/// cycle and keeps `core` free of the constraint IR.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofObligation {
    /// Identifier, unique within a run.
    pub id: ObligationId,
    /// The property class to be proven.
    pub property: SafetyProperty,
    /// Where the obligation arises.
    pub location: Location,
    /// Human-readable rendering of the condition to be proven.
    pub predicate: String,
}

impl ProofObligation {
    /// Create a new obligation.
    pub fn new(
        id: ObligationId,
        property: SafetyProperty,
        location: Location,
        predicate: impl Into<String>,
    ) -> Self {
        ProofObligation {
            id,
            property,
            location,
            predicate: predicate.into(),
        }
    }
}

/// The outcome of attempting to discharge a [`ProofObligation`].
#[derive(Debug, Clone, PartialEq)]
pub enum ObligationResult {
    /// The obligation holds; the [`ProofTree`] records why.
    Proven(ProofTree),
    /// The obligation is violated; the [`CounterExample`] witnesses it.
    Refuted(CounterExample),
    /// Undetermined: what remains to be shown, and what minimal assumptions
    /// would close the gap.
    Open {
        /// The sub-conditions that could not be established.
        residual: Vec<ResidualObligation>,
        /// Minimal extra assumptions/annotations that would close the proof.
        suggested: Vec<SuggestedAssumption>,
    },
}

impl ObligationResult {
    /// The [`crate::Verdict`] this result contributes.
    pub fn verdict(&self) -> crate::Verdict {
        match self {
            ObligationResult::Proven(_) => crate::Verdict::Pass,
            ObligationResult::Refuted(_) => crate::Verdict::Fail,
            ObligationResult::Open { .. } => crate::Verdict::Unknown,
        }
    }
}

/// A sub-condition that the verifier could not establish, with the reason.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResidualObligation {
    /// What remains to be shown.
    pub predicate: String,
    /// Why it could not be discharged (e.g. "unbounded loop", "opaque FFI
    /// call", "solver returned unknown").
    pub reason: String,
}

/// A minimal extra assumption or annotation that, if accepted, would let the
/// verifier close an otherwise-open obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SuggestedAssumption {
    /// The proposed assumption, in user-facing terms.
    pub assumption: String,
    /// Why this assumption is sufficient to close the obligation.
    pub rationale: String,
}

/// An assumption that an established proof depends on.
///
/// Every `PASS` is relative to a set of `Assumption`s. They are surfaced in the
/// report so a reader knows exactly what the proof took for granted (FFI
/// contracts, allocator behaviour, hardware memory model, …).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assumption {
    /// A stable identifier for cross-referencing from proof trees.
    pub id: String,
    /// The assumption in user-facing terms.
    pub statement: String,
    /// Why the assumption is needed / where it comes from.
    pub justification: String,
}
