//! # csolver-core
//!
//! Shared, dependency-free contracts that every other CSolver crate speaks.
//!
//! The single most important property of this crate is that it defines, in one
//! place, *what a proof is* in CSolver:
//!
//! * a [`SafetyProperty`] is the kind of thing we prove (no out-of-bounds, no
//!   use-after-free, …);
//! * a [`ProofObligation`] is a specific instance of such a property at a
//!   specific program location;
//! * an [`ObligationResult`] is the outcome of trying to discharge it — either
//!   [`ObligationResult::Proven`] (with a [`ProofTree`]),
//!   [`ObligationResult::Refuted`] (with a [`CounterExample`]), or
//!   [`ObligationResult::Open`] (with residual obligations and the minimal
//!   extra assumptions that would close the proof);
//! * a [`Verdict`] is the per-function / per-module roll-up.
//!
//! ## Soundness note
//!
//! [`Verdict::Pass`] means *proven safe under the reported assumptions*. The
//! [`Verdict::combine`] lattice is deliberately conservative: a single
//! [`Verdict::Fail`] makes the whole roll-up `Fail`, and anything not provably
//! `Pass` degrades to [`Verdict::Unknown`]. No analysis may upgrade a verdict;
//! they may only contribute obligations and their results.

pub mod error;
pub mod hash;
pub mod location;
pub mod obligation;
pub mod proof;
pub mod property;
pub mod region;
pub mod value;
pub mod verdict;

pub use error::{Error, Result};
pub use hash::{FxBuildHasher, FxHashMap, FxHashSet};
pub use location::{Location, SourceLevel, Span};
pub use region::RegionKind;
pub use obligation::{
    Assumption, ObligationId, ObligationResult, ProofObligation, ResidualObligation,
    SuggestedAssumption,
};
pub use proof::{Assignment, CounterExample, Justification, Model, ProofStep, ProofTree};
pub use property::SafetyProperty;
pub use value::BitVector;
pub use verdict::Verdict;
