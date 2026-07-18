//! # csolver-verifier — orchestration
//!
//! Turns an MSIR [`Module`] into a [`ModuleReport`] of `PASS`/`FAIL`/`UNKNOWN`
//! verdicts with proofs, counterexamples, and residual obligations.
//!
//! ## Discharge strategy (escalating, cheapest first)
//!
//! 1. **Abstract interpretation.** Run the interval analysis and evaluate each
//!    [`csolver_ir::Inst::SafetyCheck`] condition. Because intervals
//!    over-approximate, "condition holds on the whole over-approximation" is a
//!    sound `PASS`, and "holds on none of it" is a sound `FAIL`.
//! 2. **Symbolic execution + SMT.** (Milestones M2+.) For conditions the
//!    intervals leave [`csolver_absint::Trivalent::Unknown`], hand the residual
//!    to symbolic execution and the SMT solver.
//! 3. **Residual.** Anything still open becomes `UNKNOWN` with the precise
//!    remaining condition and a suggested minimal assumption.
//!
//! ## Soundness
//!
//! The roll-up uses [`Verdict::combine`]: any `FAIL` fails the function/module,
//! and anything not provably `PASS` degrades to `UNKNOWN`. A function with no
//! emitted obligations is vacuously `PASS` *over the obligations present* — the
//! report is always relative to the checks the frontend emitted.

mod contracts;
pub use contracts::address_taken_names;
pub mod datarace;
pub mod interleave;
pub mod lockorder;
mod mem2reg;
pub mod precond;
mod report;
mod wholeprog;

pub use datarace::{detect_races, DataRace, TaggedAccess};
pub use interleave::{
    find_aba, find_atomicity_violations, find_cross_entry_typestate, find_cross_entry_uaf,
    find_cross_thread_uaf, find_refcount_races, find_weak_memory_bugs, store_buffer_violations,
    trace_to_thread, weak_memory_nonrobustness, AbaWitness, AtomicityWitness,
    CrossEntryTypestateWitness, CrossEntryWitness, FreeUseWitness, RefcountRaceWitness,
    StoreBufferWitness, Thread, WeakMemoryWitness,
};
pub use lockorder::{detect_cycles, LockOrderCycle, TaggedEdge};
pub use report::{FunctionReport, ModuleReport, ObligationOutcome};
pub use csolver_symbolic::Summary;
pub use wholeprog::{ProgramFacts, WholeProgramContext, WholeProgramFacts};

use csolver_absint::{analyze_intervals, Trivalent};
use csolver_core::{
    proof::{Justification, ProofStep, ProofTree},
    Assumption, CounterExample, Location, Model, ObligationId, ObligationResult, ProofObligation,
    ResidualObligation, SafetyProperty, SourceLevel, SuggestedAssumption, Verdict,
};
use csolver_ir::{
    Condition, Const, FieldContract, FuncId, Function, Inst, Module, Operand, PtrContract, SizeSpec,
    Terminator,
};
use csolver_symbolic::{
    discharge_function, discharge_with_scalars, summarize_module, SymOutcome, SymbolicReport,
};
use std::collections::HashMap;

/// The id of the assumption that symbolic linear proofs depend on.
const LINEAR_ASSUMPTION: &str = "linear-no-overflow";

/// Verifier configuration.
#[derive(Debug, Clone)]
pub struct Config {
    /// The source level to tag obligation locations with (for reporting).
    pub level: SourceLevel,
    /// Whether to run the interval abstract interpretation pass.
    pub use_intervals: bool,
    /// Whether to escalate undecided checks to symbolic execution + the solver.
    pub use_symbolic: bool,
    /// Treat the module as the **whole program** (closed world): assume the
    /// module's direct call sites are *all* of every function's call sites, not
    /// only those with internal linkage. This licenses call-site contract
    /// synthesis for exported functions too — sound exactly when the assumption
    /// holds (a self-contained program, LTO-style link, or a `main`-rooted
    /// binary). Off by default: an open module (a library with unseen callers)
    /// would be unsound, so it is opt-in.
    pub closed_world: bool,
    /// **Bug-finding mode.** Relax the memory-refutation gate: report a spatial
    /// violation (OOB) whose offset/size depend only on genuine inputs even on an
    /// over-approximated path (after an init loop, an opaque call, …), trading a
    /// small false-positive risk for far higher recall. Off by default —
    /// verification stays strict (a false FAIL is as bad as a false PASS there).
    pub bug_finding: bool,
    /// **Assume framework-passed pointers are valid.** For each raw pointer parameter
    /// of a statically-known pointee size (from debug info), install a prove-only
    /// contract of that size resting on the `param-valid` assumption. Off by default
    /// (unsound in general — a raw pointer may dangle); opt-in for context-free
    /// analysis whose dominant `UNKNOWN` cause is an uncontracted pointer parameter
    /// (per-TU kernel/driver code).
    pub assume_valid_params: bool,
    /// **Assume unsummarised call results are valid pointers.** When a call returns a pointer
    /// that no summary/contract/return-attribute characterises (an external or unanalysed
    /// callee — the dominant `opaque call result` UNKNOWN cause), model it as a valid non-null
    /// live region of *unknown* size instead of an opaque `POrigin::Call` pointer. Off by
    /// default (**unsound in general** — a call may return null, an `ERR_PTR` error code, or a
    /// dangling pointer); the interprocedural twin of [`assume_valid_params`], opt-in for
    /// recall-first kernel/driver analysis. Surfaced as the `valid-returns` assumption. Bounds
    /// stay prove-only (unknown size), so it can prove non-null / liveness / in-object access
    /// but never *refutes* against a guessed size (no false FAIL from the guess).
    pub assume_valid_returns: bool,
    /// **Assume a loop-carried pointer stays valid.** At a loop header a pointer the body
    /// modifies is havoc'd to an opaque value — it genuinely moves (`iter = iter->next`), so
    /// its region/bounds provenance cannot be carried soundly. With this on it becomes a valid
    /// live region of *unknown* size instead: liveness (`no_use_after_free`) and non-null are
    /// provable through the iterator, while bounds stay `UNKNOWN` (nothing is refuted against a
    /// guessed size, so no false FAIL). Off by default — **unsound in general**: a moving
    /// pointer can walk off its object and a list node can already be freed. Models the kernel's
    /// intrusive-container / iterator discipline (`list_for_each_entry` walks live nodes).
    /// Surfaced as the `valid-loop-ptrs` assumption.
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
    /// **Rust aliasing (borrow-stack) model.** Opt-in Stacked/Tree-Borrows checking: flag a
    /// `NoAliasingViolation` (currently a write through a shared `&T` reference). Off by
    /// default — the reference model is only partially reconstructed from the frontends, so
    /// this is opt-in (`--aliasing-model`) until the full borrow-stack lands.
    pub aliasing_model: bool,
    /// Optional **entry-point name patterns** (exact, or a trailing-`*` prefix). When
    /// present, ONLY a function whose name matches is treated as an attacker-reachable
    /// entry — its `arg…` parameters are genuine adversarial inputs in bug-finding mode;
    /// every other function is analysed as an internal helper whose parameters are
    /// caller-validated. This replaces the default heuristic (LLVM external linkage) for
    /// kernel analysis, where external linkage means "callable by other kernel code",
    /// NOT "reachable from userspace" — the source of the internal-helper false positives
    /// (e.g. `notify_cpu_starting(cpu)` flagged OOB at `cpu = UINT_MAX`, impossible since
    /// the hotplug machinery always passes a valid cpu). Excluding a non-entry can only
    /// reduce recall (a wrongly-excluded entry's obligation stays UNKNOWN), never turn a
    /// FAIL into a PASS, so it is sound. `None` ⇒ the linkage default (unchanged).
    pub entry_patterns: Option<Vec<String>>,
    /// Per-function symbolic exploration wall-clock budget. `None` disables the
    /// clock (unbounded — used by a scan's *deferred* second phase to give a
    /// budget-limited unit a full-effort re-run). Defaults to the executor's
    /// generous 30 s termination guarantee.
    pub time_budget: Option<std::time::Duration>,
    /// **Attack-surface reporting filter** (opt-in, scan only). When set, the scan
    /// reports only findings in functions **directly** reachable (whole-program
    /// direct-call graph) from a genuine attacker entry — a syscall wrapper or an
    /// `*ioctl*` handler — suppressing the large mass of internal driver callbacks
    /// (register accessors, clk/drm ops) that `--auto-entries` promotes to
    /// free-parameter entries and that are reachable only through *indirect* ops
    /// dispatch. Purely a **reporting lens**: verdicts and the coverage counts are
    /// unchanged, so it can never introduce a false PASS — it trades recall (a real
    /// bug reached only via an indirect callback is hidden) for precision on the
    /// syscall/ioctl attack surface. `false` ⇒ every finding is reported (default).
    pub attack_surface_only: bool,
}

/// Whether `name` matches an entry pattern. A single `*` is a wildcard at the
/// start and/or end of the pattern (no interior wildcards):
/// - `foo`     — exact match
/// - `foo*`    — prefix  (`__x64_sys_*` matches `__x64_sys_read`)
/// - `*foo`    — suffix  (`*_ioctl` matches `tun_chr_ioctl`)
/// - `*foo*`   — contains
pub fn matches_entry(name: &str, patterns: &[String]) -> bool {
    patterns.iter().any(|p| {
        let starred_start = p.starts_with('*');
        let starred_end = p.ends_with('*');
        let core = p.trim_matches('*');
        match (starred_start, starred_end) {
            (false, false) => name == core,
            (false, true) => name.starts_with(core),
            (true, false) => name.ends_with(core),
            (true, true) => name.contains(core),
        }
    })
}

impl Default for Config {
    fn default() -> Self {
        Config {
            level: SourceLevel::Llvm,
            use_intervals: true,
            use_symbolic: true,
            closed_world: false,
            bug_finding: false,
            assume_valid_params: false,
            assume_valid_returns: false,
            assume_valid_loop_ptrs: false,
            assume_param_buffer_len: false,
            assume_struct_tail: false,
            assume_valid_mmio: false,
            assume_field_invariants: false,
            aliasing_model: false,
            entry_patterns: None,
            time_budget: Some(std::time::Duration::from_secs(30)),
            attack_surface_only: false,
        }
    }
}

/// Verify every function in `module`.
///
/// Interprocedural: function summaries are computed once and used so that calls
/// preserve pointer provenance and respect the callee's memory effects.
pub fn verify_module(module: &Module, config: &Config) -> ModuleReport {
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get());
    verify_module_with_threads(module, config, threads)
}

/// As [`verify_module`], with an explicit worker-thread count (`1` = serial).
///
/// The result is **independent of the thread count** — bit-for-bit. Functions are
/// verified in isolation (each builds its own solver context; there is no shared
/// mutable state), and obligation ids are assigned by a *serial* renumbering pass
/// in function order after the fact, so completion order cannot leak into the
/// output. The determinism test (`parallel_matches_serial`) is the oracle for this,
/// the role Miri plays for the MIR lowering. The count trades only latency.
pub fn verify_module_with_threads(module: &Module, config: &Config, threads: usize) -> ModuleReport {
    verify_module_inner(module, config, threads, None)
}

/// As [`verify_module_with_threads`], but analysing one file with **whole-program
/// precision, without linking** (2b). A cross-file `Callee::Symbol(name)` call with no
/// in-module definition resolves to the callee's real effect summary, and an external
/// function's whole-program preconditions (scalar/pointer/field, derived over the whole
/// tree) overlay its per-file contracts — everything the streaming-facts driver
/// extracted, keyed by name (see [`WholeProgramContext`]).
///
/// Sound: the effect summaries only ever tighten a call from "havoc everything" toward
/// the callee's actual effect, and fall back to havoc when absent. The precondition
/// overlays reproduce exactly what a fully-linked **closed-world** run would synthesize
/// for those functions (the facts are bit-identical); they are the caller's
/// responsibility to have extracted closed-world (`ctx` is empty otherwise, so this
/// degrades to effect-summary-only resolution — still sound in open world). To keep the
/// per-file synthesis itself sound (one file is not the whole program), it is run
/// open-world here; the closed-world precision comes solely from the overlay.
pub fn verify_module_whole_program(
    module: &Module,
    config: &Config,
    threads: usize,
    ctx: WholeProgramContext<'_>,
) -> ModuleReport {
    verify_module_inner(module, config, threads, Some(ctx))
}


// --- module split (mechanical refactor) ---
mod assumptions;
mod discharge;
mod run;
pub use discharge::verify_function;
use assumptions::*;
use discharge::*;
use run::*;

#[cfg(test)]
mod entry_tests {
    use super::matches_entry;

    #[test]
    fn exact_prefix_suffix_and_contains_patterns_match() {
        let pats = vec![
            "aead_recvmsg".to_string(),
            "__x64_sys_*".to_string(),
            "*_ioctl".to_string(),
            "*netlink*".to_string(),
        ];
        // Exact.
        assert!(matches_entry("aead_recvmsg", &pats));
        assert!(!matches_entry("aead_recvmsg_nokey", &pats));
        // Prefix.
        assert!(matches_entry("__x64_sys_read", &pats));
        assert!(!matches_entry("__x64_sy", &pats));
        // Suffix.
        assert!(matches_entry("tun_chr_ioctl", &pats));
        assert!(!matches_entry("ioctl_helper", &pats));
        // Contains.
        assert!(matches_entry("rtnetlink_rcv_msg", &pats));
        // A pure internal helper matches nothing.
        assert!(!matches_entry("notify_cpu_starting", &pats));
    }
}
