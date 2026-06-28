//! # csolver-symbolic — symbolic execution (M1, increment 1)
//!
//! A path-sensitive symbolic discharge for **acyclic** MSIR functions. It walks
//! every path from the entry, accumulating a path condition (the branch facts
//! taken to reach a point) and a symbolic register environment, and for each
//! [`csolver_ir::Inst::SafetyCheck`] asks the linear decision procedure whether
//! the path condition *implies* the checked condition.
//!
//! A check is reported [`SymOutcome::Proven`] only if it is proved on **every**
//! path that reaches it. Anything else is [`SymOutcome::Unknown`]. The engine
//! never produces a refutation here (that needs model extraction, a later
//! increment), so it can only ever *reduce* the number of UNKNOWNs — never
//! introduce an unsound PASS or FAIL.
//!
//! ## Limits (this increment)
//!
//! * Functions containing loops are skipped (the interval analysis still
//!   handles them); loop summaries arrive in a later increment.
//! * Exploration is bounded; if it is truncated, **no** decisions are reported
//!   (so truncation can never hide a violating path). See `Verification/`.
//! * Memory is not yet modelled symbolically here — only scalar/relational
//!   reasoning over registers. Symbolic pointers/heaps are the next increment.

mod exec;
mod summary;

pub use exec::{
    discharge_full, discharge_function, discharge_with, discharge_with_summaries, MemDecision,
    SymOutcome, SymbolicReport,
};
pub use summary::{summarize_module, Affine, RetSummary, Summary};

/// Resource bounds for symbolic exploration.
#[derive(Debug, Clone, Copy)]
pub struct ExecLimits {
    /// Maximum number of block visits before exploration is truncated.
    pub max_visits: usize,
}

impl Default for ExecLimits {
    fn default() -> Self {
        ExecLimits {
            max_visits: 200_000,
        }
    }
}
