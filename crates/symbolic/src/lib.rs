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
    discharge_full, discharge_function, discharge_with, discharge_with_fields,
    discharge_with_summaries, MemDecision, SymOutcome, SymbolicReport,
};
pub use summary::{summarize_module, Affine, RetSummary, Summary};

/// Resource bounds for symbolic exploration.
#[derive(Debug, Clone, Copy)]
pub struct ExecLimits {
    /// Maximum number of block visits before exploration is truncated.
    pub max_visits: usize,
    /// Wall-clock budget for exploring one function. On expiry, exploration
    /// truncates exactly as the visit budget does — no decisions are reported, so
    /// every memory obligation falls to `Open` and the function to non-`PASS`
    /// (sound; the same rule the visit-truncation pin rests on). `None` disables
    /// the clock.
    ///
    /// The default is generous on purpose: it is a *termination guarantee* for the
    /// turnkey path (an arbitrary/adversarial crate must not make one function run
    /// unbounded), not a speed knob. Current code never reaches it, so it changes
    /// no verdict. Tightening it trades the `PASS` of a slow-but-provable function
    /// for a snappier `UNKNOWN` — a precision-for-latency choice, left to the caller.
    pub time_budget: Option<std::time::Duration>,
    /// Bug-finding mode: report a spatial memory violation (OOB) whose offset and
    /// size depend only on genuine inputs (parameters) even on an over-approximated
    /// path — e.g. an OOB access reached after an init loop, where the loop havoc
    /// made the path inexact but the violating index is a free parameter, so the
    /// witness is genuinely reachable. Trades a small false-positive risk (a branch
    /// on an over-approximated value that is actually infeasible) for far higher
    /// recall on real code. Off by default: verification stays strict.
    pub bug_finding: bool,
    /// Whether this function is **exported** (externally reachable), so its
    /// parameters may be attacker-controlled. In bug-finding mode only an exported
    /// function's scalar parameters are treated as genuine adversarial inputs; an
    /// *internal* function's parameters are supplied by in-module callers
    /// (caller-constrained), so refuting on a freely-chosen value would report a
    /// false positive (e.g. an internal helper indexed by a bounded enum). Default
    /// `true`: an isolated function is treated as an entry point.
    pub exported: bool,
}

impl Default for ExecLimits {
    fn default() -> Self {
        ExecLimits {
            max_visits: 200_000,
            time_budget: Some(std::time::Duration::from_secs(30)),
            bug_finding: false,
            exported: true,
        }
    }
}
