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
mod lockclass;
mod summary;
pub mod sync;

pub use exec::{
    discharge_full, discharge_function, discharge_with, discharge_with_fields,
    discharge_with_scalars, discharge_with_summaries, MemDecision, SymOutcome, SymbolicReport,
};
pub use summary::{
    summarize_module, summarize_program, Affine, RetSummary, Summary, SummaryFacts,
};

/// Resource bounds for symbolic exploration.
#[derive(Debug, Clone, Copy)]
pub struct ExecLimits {
    /// Maximum number of block visits before exploration is truncated. The default is *unbounded*
    /// (`usize::MAX`): the merged exploration walks each basic block of the reverse-postorder at most
    /// once (loop back-edges are cut, headers over-approximated), so the visit count is bounded by
    /// the CFG size *by construction* — no artificial cap is needed. A test may set a small value to
    /// force truncation.
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
    /// Honour `RefWitness { assumed: true }` — a raw pointer field recovered from
    /// debug info, valid only under the `assume_valid_params` opt-in.
    pub assume_valid_params: bool,
    /// **Assume an unsummarised call's pointer result is valid.** Model a pointer returned by
    /// a call with no summary/contract/return-attribute as a valid non-null live region of
    /// unknown size, instead of an opaque `POrigin::Call` pointer. Off by default (unsound in
    /// general — a call may return null / an error pointer / a dangling pointer); the
    /// interprocedural twin of `assume_valid_params`, surfaced as `valid-returns`.
    pub assume_valid_returns: bool,
    /// **Assume a loop-carried pointer stays valid.** At a loop header a pointer the body
    /// modifies is havoc'd to an opaque value (it genuinely moves: `iter = iter->next`).
    /// With this on, it becomes a valid live region of unknown size instead — liveness and
    /// non-null are provable through the iterator, bounds stay UNKNOWN. Off by default
    /// (unsound in general: a moving pointer can walk off its object, a list node can be
    /// freed); surfaced as `valid-loop-ptrs`.
    pub assume_valid_loop_ptrs: bool,
    /// Honour a C `(buf, len)` parameter pairing recovered by the frontend. Unsound in
    /// general: C guarantees no such pairing, so a wrong one could prove an overrun safe.
    pub assume_param_buffer_len: bool,
    /// Size an object that the code navigates past its declared struct type to cover that
    /// reach (the C trailing-context idiom). Unsound in general: the tail's real size is
    /// known only at the allocation site.
    pub assume_struct_tail: bool,
    /// Trust that an access through an `iomem`-labelled (`ioremap`) pointer stays within the
    /// device mapping. Prove-only, unsound in general (a symbolic register offset may overrun).
    pub assume_valid_mmio: bool,
    /// Assume a scalar loaded from memory (a struct field) is valid for its use (shift/divide).
    /// Unsound in general (an opaque write could store an out-of-range value).
    pub assume_field_invariants: bool,
    /// **Rust aliasing (borrow-stack) model.** When on, track each pointer's originating
    /// borrow (from `RefWitness`) and flag a `NoAliasingViolation` — currently a write
    /// through a shared `&T` reference. Off by default (the reference model is only
    /// partially reconstructed from the frontends; opt-in until complete).
    pub aliasing_model: bool,
    /// **Flat machine-code memory** (a binary / assembly front-end). Heap allocations
    /// modelled from a call contract are then **prove-only for bounds**: the flat register
    /// model cannot reliably reconstruct a bounds *guard* on a heap index (the guard often
    /// compares a spilled stack local that is reloaded at the access), so refuting a heap
    /// OOB would risk a false FAIL on guarded-safe code. The region is still created — so a
    /// *temporal* violation (use-after-free / double-free, which needs no guard) is refuted
    /// and a provably in-bounds access still proves — only its bounds are not refuted. Off
    /// by default (source/IR front-ends have precise guards and stay fully refutable).
    pub flat_memory: bool,
}

impl Default for ExecLimits {
    fn default() -> Self {
        ExecLimits {
            max_visits: usize::MAX,
            time_budget: Some(std::time::Duration::from_secs(30)),
            bug_finding: false,
            exported: true,
            assume_valid_params: false,
            assume_valid_returns: false,
            assume_valid_loop_ptrs: false,
            assume_param_buffer_len: false,
            assume_struct_tail: false,
            assume_valid_mmio: false,
            assume_field_invariants: false,
            aliasing_model: false,
            flat_memory: false,
        }
    }
}
