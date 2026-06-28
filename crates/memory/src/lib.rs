//! # csolver-memory — the symbolic memory model
//!
//! CSolver reasons about memory through *regions* (allocations with a kind,
//! size, alignment, permission set and lifetime) and *symbolic pointers*
//! (a provenance + a symbolic offset). A memory access is checked against the
//! region its pointer points into, producing — per safety property — one of:
//!
//! * [`CheckOutcome::Proven`]   — concretely safe, no solver needed;
//! * [`CheckOutcome::Violated`] — concretely unsafe (a counterexample exists);
//! * [`CheckOutcome::Residual`] — depends on symbolic facts; hand to the solver.
//!
//! This split is what lets CSolver discharge the "obvious" majority of checks
//! cheaply and reserve the SMT solver for the genuinely symbolic ones.
//!
//! ## Soundness
//!
//! The model is an *over-approximation* of real memory: when a fact is unknown
//! (symbolic size/offset, opaque provenance), the model never returns `Proven`.
//! `Proven` is emitted only when the relevant quantities are concrete and the
//! property holds for them. See `Verification/` for the argument.

pub mod access;
pub mod alias;
pub mod pointer;
pub mod region;

pub use access::{Access, AccessReport, CheckOutcome};
pub use alias::AliasResult;
pub use pointer::{Pointer, Provenance, SymOffset};
pub use region::{LifetimeState, MemoryModel, Permissions, Region, RegionId, SymSize};
