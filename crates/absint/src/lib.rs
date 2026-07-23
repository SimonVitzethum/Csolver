//! # csolver-absint — abstract interpretation
//!
//! A small, sound abstract-interpretation framework plus its first numeric
//! domain (intervals).
//!
//! * [`AbstractDomain`] is the lattice contract every domain implements.
//! * [`interval::Interval`] is the classic integer-interval lattice with
//!   widening and narrowing.
//! * [`env::IntervalState`] lifts intervals to a per-register environment.
//! * [`engine::solve`] is the generic monotone-framework worklist solver; it
//!   applies widening at the loop headers reported by `csolver-cfg`, which is
//!   what guarantees termination.
//! * [`analysis::analyze_intervals`] wires the interval domain to MSIR transfer
//!   functions and produces per-block invariants.
//!
//! ## Soundness
//!
//! Each domain's transfer functions over-approximate the concrete semantics,
//! and the solver computes a post-fixpoint of those transfers. Therefore the
//! invariant inferred for a program point holds on *every* concrete execution
//! that reaches it. Widening only ever enlarges the abstract state, preserving
//! this over-approximation while forcing termination.

pub mod analysis;
pub mod domain;
pub mod engine;
pub mod env;
pub mod induction;
pub mod interval;
pub mod pointsto;
pub mod relational;
pub mod zone;

pub use analysis::{analyze_intervals, IntervalAnalysis, Trivalent};
pub use domain::AbstractDomain;
pub use induction::{analyze_induction, EqExitIndVar, InductionAnalysis, PtrIndVar};
pub use engine::{solve, Solution};
pub use env::IntervalState;
pub use interval::{Bound, Interval};
pub use pointsto::{ModulePointsTo, PointsTo, ProgramPointsTo};
pub use relational::{analyze_zones, ZoneAnalysis};
pub use zone::Zone;
