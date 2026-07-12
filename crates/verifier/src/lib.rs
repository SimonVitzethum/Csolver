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
pub mod datarace;
pub mod interleave;
pub mod lockorder;
mod mem2reg;
pub mod precond;
mod report;
mod wholeprog;

pub use datarace::{detect_races, DataRace, TaggedAccess};
pub use interleave::{find_atomicity_violations, trace_to_thread, AtomicityWitness, Thread};
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
            entry_patterns: None,
            time_budget: Some(std::time::Duration::from_secs(30)),
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

fn verify_module_inner(
    module: &Module,
    config: &Config,
    threads: usize,
    ctx: Option<WholeProgramContext<'_>>,
) -> ModuleReport {
    // Promote non-escaping scalar stack slots to SSA first: unoptimized front-end
    // output spills locals (loop counters, pointer parameters) to allocas, which
    // defeats induction bounds and store-load provenance. Semantics-preserving, so
    // sound; it only lets the analysis see what `-O1` would have.
    let promoted = mem2reg::promote_module(module);
    let module = &promoted;
    let summaries = config.use_symbolic.then(|| summarize_module(module));
    // In whole-program mode the per-file synthesis MUST run open-world — a single file
    // is not the whole program, so its call sites are incomplete — and the closed-world
    // precision is supplied instead by the name-keyed overlay (`ctx`), which was derived
    // over the whole tree. Outside whole-program mode, honour the caller's setting.
    let unit_cw = if ctx.is_some() { false } else { config.closed_world };
    // Interprocedural: contracts synthesized from the (complete) call sites of
    // internal functions overlay the declared ones (declared always wins).
    let synthesized = contracts::synthesize(module, unit_cw);
    // Interprocedural member-provenance: which fields of a contracted parameter
    // every call site fills with a valid pointer (empty unless internal/closed).
    let field_synth = contracts::synthesize_fields(module, &synthesized, unit_cw);
    // Interprocedural scalar value-range preconditions: the range each integer parameter
    // is bounded to by the union of its (complete) call sites — so a callee proves an index
    // in bounds using its callers' validation (e.g. a `switch (optname) case A..B:` guard).
    let scalar_synth = contracts::synthesize_scalars(module, unit_cw);
    let mut functions = verify_functions(
        module,
        summaries.as_ref(),
        ctx,
        &synthesized,
        &field_synth,
        &scalar_synth,
        config,
        threads,
    );

    // Assign global obligation ids by a serial pass in function order — this
    // reproduces exactly the sequential ids a serial run would give, regardless of
    // the order in which the workers finished.
    let mut next_id: u32 = 0;
    for fr in &mut functions {
        for o in &mut fr.outcomes {
            o.obligation.id = ObligationId(next_id);
            next_id += 1;
        }
    }

    // Functions a frontend could not lower are reported as UNKNOWN (never a
    // silent omission), so the module verdict reflects that they were not
    // verified.
    for (uname, reason) in &module.unanalyzed {
        let id = ObligationId(next_id);
        next_id += 1;
        let location = Location::level_only(config.level).in_function(uname.as_str());
        let obligation = ProofObligation::new(
            id,
            SafetyProperty::ValidReference,
            location,
            "the function body is analyzable",
        );
        let result = ObligationResult::Open {
            residual: vec![ResidualObligation {
                predicate: "whole function body".into(),
                reason: format!("not analyzed by the frontend: {reason}"),
            }],
            suggested: vec![],
        };
        functions.push(FunctionReport {
            function: uname.clone(),
            verdict: Verdict::Unknown,
            outcomes: vec![ObligationOutcome { obligation, result }],
            truncated: false,
            lock_edges: Vec::new(),
            race_accesses: Vec::new(),
            race_trace: Vec::new(),
        });
    }

    let verdict = Verdict::combine_all(functions.iter().map(|f| f.verdict));

    // Surface — once each — every assumption any proof in the module depends on.
    let mut ids: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for func in &functions {
        for o in &func.outcomes {
            if let ObligationResult::Proven(tree) = &o.result {
                ids.extend(tree.assumptions.iter().cloned());
            }
        }
    }
    let assumptions = ids.into_iter().map(assumption_record).collect();

    ModuleReport {
        module: module.name.clone(),
        verdict,
        functions,
        assumptions,
    }
}

/// Verify one function in isolation with a *local* obligation-id counter (the
/// caller renumbers globally). Self-contained: its own solver context, read-only
/// summaries/contracts/config — so it is safe to run on any worker thread.
#[allow(clippy::too_many_arguments)]
fn verify_one_function(
    module: &Module,
    summaries: Option<&HashMap<FuncId, Summary>>,
    ctx: Option<WholeProgramContext<'_>>,
    synthesized: &HashMap<(FuncId, u32), PtrContract>,
    field_synth: &HashMap<(FuncId, u32), Vec<FieldContract>>,
    scalar_synth: &HashMap<(FuncId, u32), (i128, i128)>,
    config: &Config,
    f: &Function,
) -> FunctionReport {
    let mut contracts = module.contracts_for(f);
    for (i, slot) in contracts.iter_mut().enumerate() {
        if slot.is_none() {
            *slot = synthesized.get(&(f.id, i as u32)).copied();
        }
        // Opt-in `assume_valid_params`: a still-uncontracted raw pointer parameter of
        // known pointee size becomes a prove-only, valid, correctly-sized region under
        // the `param-valid` assumption (the framework passes a valid pointer at entry).
        if slot.is_none() && config.assume_valid_params {
            if let Some(&(size, align)) = module.raw_ptr_hints.get(&(f.id, i as u32)) {
                // A valid instance is naturally aligned; when debug info omits the
                // alignment, derive it from the size (a type's size is a multiple of
                // its alignment) — the largest power of two dividing it, capped at 16
                // (`max_align_t`) — so an aligned field access proves.
                let derived = 1u32 << size.trailing_zeros().min(4);
                *slot = Some(PtrContract {
                    assumption: Some("param-valid"),
                    refutable: false,
                    size: SizeSpec::Bytes(size),
                    align: align.max(derived).max(1),
                    readable: true,
                    writable: true,
                    sentinel: None,
                });
            }
        }
        // An internal function's (or closure's) contract is a caller-established
        // precondition: the guard lives at the call sites, so a witness picked
        // freely from the parameter space may never occur in the real program.
        // Prove-only — refuting it reported false FAILs on bytes' closures.
        if module.internal.contains(&f.id) {
            if let Some(c) = slot {
                c.refutable = false;
            }
        }
    }
    // Per-parameter member-provenance field contracts (empty vec = none).
    let mut field_contracts: Vec<Vec<FieldContract>> = (0..f.params.len())
        .map(|i| field_synth.get(&(f.id, i as u32)).cloned().unwrap_or_default())
        .collect();
    // Per-parameter scalar value-range preconditions (None = unconstrained).
    let mut scalar_pre: Vec<Option<(i128, i128)>> = (0..f.params.len())
        .map(|i| scalar_synth.get(&(f.id, i as u32)).copied())
        .collect();

    // Whole-program precondition overlay (2b): for a **linkage-external** function, lay
    // its whole-tree preconditions (from the streaming facts, keyed by name) over the
    // per-file (open-world) ones — the cross-file caller→callee validation flow that
    // linking provided, without linking. Gated on external linkage so a file-local
    // `static` never picks up an unrelated same-named external's contract. Sound only
    // because these facts were extracted closed-world (the driver's responsibility); the
    // maps are empty otherwise, making this a no-op. They reproduce exactly what a linked
    // closed-world synthesis would assign (the facts are bit-identical), including each
    // contract's baked-in refutability.
    if let Some(ctx) = ctx {
        if !module.internal.contains(&f.id) {
            for i in 0..f.params.len() as u32 {
                let key = (f.name.clone(), i);
                if let Some(&range) = ctx.name_scalars.get(&key) {
                    scalar_pre[i as usize] = Some(range);
                }
                // A declared / `assume_valid_params` contract still wins (as synthesized
                // never overrides declared); only fill an otherwise-uncontracted pointer.
                if contracts[i as usize].is_none() {
                    if let Some(&c) = ctx.name_ptr_contracts.get(&key) {
                        contracts[i as usize] = Some(c);
                    }
                }
                if let Some(fc) = ctx.name_field_contracts.get(&key) {
                    if !fc.is_empty() {
                        field_contracts[i as usize] = fc.clone();
                    }
                }
            }
        }
    }

    // An entry policy (if given) decides attacker-reachability by name — the sound
    // kernel model, where LLVM external linkage does NOT mean userspace-reachable.
    let exported = match &config.entry_patterns {
        Some(pats) => matches_entry(&f.name, pats),
        None => !module.internal.contains(&f.id),
    };
    let empty_summaries = HashMap::new();
    let name_summaries = ctx.map(|c| c.name_summaries).unwrap_or(&empty_summaries);
    let mut local_id = 0u32;
    verify_function_with(
        f,
        summaries,
        name_summaries,
        &contracts,
        &field_contracts,
        &scalar_pre,
        &module.globals,
        &module.prov_grants,
        &module.global_fn_ptrs,
        config,
        exported,
        &mut local_id,
    )
}

/// Verify every function, distributing them over `threads` workers. Work is pulled
/// from a shared atomic index (not fixed chunks), so a few slow functions do not
/// stall a whole worker — scalable to the machine's cores. Results are returned in
/// function order (sorted by index), so the caller's renumbering is deterministic.
#[allow(clippy::too_many_arguments)]
fn verify_functions(
    module: &Module,
    summaries: Option<&HashMap<FuncId, Summary>>,
    ctx: Option<WholeProgramContext<'_>>,
    synthesized: &HashMap<(FuncId, u32), PtrContract>,
    field_synth: &HashMap<(FuncId, u32), Vec<FieldContract>>,
    scalar_synth: &HashMap<(FuncId, u32), (i128, i128)>,
    config: &Config,
    threads: usize,
) -> Vec<FunctionReport> {
    let fns = &module.functions;
    let n = fns.len();
    if threads <= 1 || n <= 1 {
        return fns
            .iter()
            .map(|f| verify_one_function(module, summaries, ctx, synthesized, field_synth, scalar_synth, config, f))
            .collect();
    }
    let next = std::sync::atomic::AtomicUsize::new(0);
    let out = std::sync::Mutex::new(Vec::<(usize, FunctionReport)>::with_capacity(n));
    std::thread::scope(|s| {
        for _ in 0..threads.min(n) {
            s.spawn(|| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if i >= n {
                    break;
                }
                let r = verify_one_function(
                    module, summaries, ctx, synthesized, field_synth, scalar_synth,
                    config, &fns[i],
                );
                // Recover from a poisoned lock (a worker panicked) rather than
                // cascading the panic — the collected data is still valid.
                out.lock().unwrap_or_else(std::sync::PoisonError::into_inner).push((i, r));
            });
        }
    });
    let mut v = out.into_inner().unwrap_or_else(std::sync::PoisonError::into_inner);
    v.sort_by_key(|&(i, _)| i);
    v.into_iter().map(|(_, r)| r).collect()
}

/// Expand a known assumption id into its full record for the report.
fn assumption_record(id: String) -> Assumption {
    match id.as_str() {
        "caller-range-precondition" => Assumption {
            id,
            statement: "a non-entry function's integer parameter stays within the range \
                        that every visible call site passes it"
                .into(),
            justification: "the callee's call sites are provably complete (internal linkage, \
                            or the whole-program assertion), so the union of the argument \
                            ranges over all sites bounds the parameter; the callee is not an \
                            attacker-reachable entry, so no unseen caller can escape the range"
                .into(),
        },
        LINEAR_ASSUMPTION => Assumption {
            id,
            statement: "the integer/offset/size quantities reasoned about are \
                        non-negative and fit in isize::MAX, so they do not wrap and \
                        their signed and unsigned comparisons coincide"
                .into(),
            justification: "the internal linear decision procedure models bit-vectors \
                            as mathematical integers; Rust caps any allocation at \
                            isize::MAX bytes, so offsets, sizes and valid indices lie \
                            in [0, isize::MAX] where this holds. Programs using the \
                            full unsigned range with the sign bit set need the \
                            bit-precise SMT backend (later milestone)"
                .into(),
        },
        "alloc-succeeds" => Assumption {
            id,
            statement: "allocation requests succeed: they return a valid, non-null, \
                        suitably-sized and -aligned block (out-of-memory is not modelled)"
                .into(),
            justification: "the symbolic memory model treats an allocation as producing \
                            a live region; programs that must handle allocation failure \
                            need that null-check modelled separately"
                .into(),
        },
        "param-contracts" => Assumption {
            id,
            statement: "pointer parameters satisfy their declared contracts: a \
                        `dereferenceable(N)`/`align`/`readonly`/`writeonly` pointer \
                        points to N valid bytes with that alignment and access mode"
                .into(),
            justification: "these come from the parameters' Rust reference types \
                            (`&[T]`, `&mut [T; N]`, …), which the compiler guarantees and \
                            emits as LLVM parameter attributes; the proof is relative to \
                            the caller upholding the reference's validity"
                .into(),
        },
        "param-valid" => Assumption {
            id,
            statement: "a raw pointer parameter points to a valid, live, correctly-sized \
                        instance of its (debug-info) pointee type"
                .into(),
            justification: "the opt-in `--assume-valid-params`: a framework/kernel entry \
                            point is passed a valid pointer by its caller (the framework), \
                            which C's type system cannot state; unsound for an arbitrary raw \
                            pointer, so the proof is explicitly relative to this assumption"
                .into(),
        },
        contracts::INTERNAL_CALL_CONTRACT => Assumption {
            id,
            statement: "an internal function's pointer parameter satisfies the weakest \
                        contract its call sites guarantee (minimum size and alignment, \
                        intersected permissions)"
                .into(),
            justification: "the function has internal linkage and its address is never \
                            taken, so the module's direct call sites are provably all of \
                            its call sites; every one passes a live region with at least \
                            the synthesized size (a constant-size stack allocation or a \
                            parameter with a declared contract, borrowed for the call)"
                .into(),
        },
        contracts::CLOSED_WORLD_CONTRACT => Assumption {
            id,
            statement: "in whole-program (closed-world) mode, an exported function's \
                        pointer parameter satisfies the weakest contract its call sites \
                        guarantee (minimum size and alignment, intersected permissions)"
                .into(),
            justification: "the run was told the module is the whole program \
                            (`--closed-world`), so the module's direct call sites are \
                            taken to be all of the function's call sites — the same \
                            derivation as internal linkage, resting on the whole-program \
                            assertion instead of on linkage; every seen call passes a \
                            live region of at least the synthesized size"
                .into(),
        },
        "precondition" => Assumption {
            id,
            statement: "a caller-declared parameter precondition holds: the pointer is a \
                        valid, non-null region of the declared size (readable, and writable \
                        if so declared)"
                .into(),
            justification: "supplied by the user as an opt-in precondition annotation (a \
                            sidecar `--pre` file), the way a `_Nonnull` / `access` attribute \
                            documents an API contract; the callee may assume it, and every \
                            caller is obliged to establish it — so it proves but never refutes"
                .into(),
        },
        "debuginfo" => Assumption {
            id,
            statement: "a reference parameter points to a live object of its                         debug-info pointee type's size (readable, and writable for                         `&mut`/non-const)"
                .into(),
            justification: "recovered from the module's DWARF debug metadata (`!DI…`),                             which records the pointee type the opaque `ptr` erased. A                             contract is synthesized only for pointer kinds the source                             language guarantees valid — a Rust `&T`/`&mut T` or a C++                             `T&` — never a raw pointer, so it grants exactly what the                             type system already does"
                .into(),
        },
        "valid-reference" => Assumption {
            id,
            statement: "a `&T`/`&mut T` value points to a live, correctly-sized                         and -aligned `T`, readable (and writable for `&mut`)"
                .into(),
            justification: "Rust's reference invariant: a reference of type `&T` is                             always valid for its pointee, even when obtained where the                             analysis cannot see its origin (a call result, a by-value                             aggregate field). The region is modelled fresh, so it never                             aliases — the assumption only ever loses precision"
                .into(),
        },
        "global-memory" => Assumption {
            id,
            statement: "a global/static symbol points to a region of its declared                         size and alignment that lives for the whole program (writable                         unless declared `constant`) and is initialized"
                .into(),
            justification: "the size, alignment and mutability come from the module's                             own `@name = global/constant <type>` definition, the same                             trust level as the function bodies being verified"
                .into(),
        },
        "slice-abi" => Assumption {
            id,
            statement: "a `(ptr, usize len)` parameter pair is a Rust slice `&[T]`: \
                        the pointer is valid for `len * size_of::<T>()` bytes"
                .into(),
            justification: "the front-end paired an aligned pointer parameter with the \
                            following length parameter per the Rust slice ABI and took the \
                            element size from a use; this is a heuristic, made explicit so \
                            the proof's trust boundary is visible"
                .into(),
        },
        _ => Assumption {
            statement: id.clone(),
            id,
            justification: String::new(),
        },
    }
}

/// Verify a single function in isolation (no interprocedural summaries or
/// parameter contracts), drawing obligation ids from `next_id`.
pub fn verify_function(f: &Function, config: &Config, next_id: &mut u32) -> FunctionReport {
    verify_function_with(
        f, None, &HashMap::new(), &[], &[], &[], &HashMap::new(), &HashMap::new(),
        &HashMap::new(), config, true, next_id,
    )
}

/// Verify a single function, optionally using module-wide summaries for calls
/// and per-parameter pointer contracts.
#[allow(clippy::too_many_arguments)]
fn verify_function_with(
    f: &Function,
    summaries: Option<&HashMap<FuncId, Summary>>,
    name_summaries: &HashMap<String, Summary>,
    contracts: &[Option<PtrContract>],
    field_contracts: &[Vec<FieldContract>],
    scalar_pre: &[Option<(i128, i128)>],
    globals: &HashMap<String, csolver_ir::GlobalDef>,
    prov_grants: &HashMap<u32, std::collections::HashSet<u32>>,
    global_fn_ptrs: &HashMap<String, Vec<(u64, FuncId)>>,
    config: &Config,
    exported: bool,
    next_id: &mut u32,
) -> FunctionReport {
    let analysis = config.use_intervals.then(|| analyze_intervals(f));
    let symbolic = config.use_symbolic.then(|| match summaries {
        // Hand the interval analysis (already computed for interval discharge) to
        // the executor so it is not recomputed — a clone instead of a 2nd fixpoint.
        Some(s) => discharge_with_scalars(
            f, s, name_summaries, contracts, field_contracts, scalar_pre, globals, prov_grants,
            global_fn_ptrs, analysis.as_ref(), config.time_budget, config.bug_finding, exported,
            config.assume_valid_params,
        ),
        None => discharge_function(f),
    });

    let truncated = symbolic.as_ref().is_some_and(|r| r.truncated);
    let sym_assumptions = symbolic
        .as_ref()
        .map(|r| r.assumptions.clone())
        .unwrap_or_default();

    let mut outcomes = Vec::new();
    for block in &f.blocks {
        for (index, inst) in block.insts.iter().enumerate() {
            if let Inst::SafetyCheck {
                property,
                condition,
                note,
            } = inst
            {
                // Explicit check: intervals first, then symbolic scalar.
                let id = ObligationId(*next_id);
                *next_id += 1;
                let location = Location::level_only(config.level)
                    .in_function(f.name.as_str())
                    .at_instruction(index as u32)
                    .with_raw(block.inst_spans.get(index).cloned().flatten());
                let predicate = render_condition(condition);
                let obligation = ProofObligation::new(id, *property, location, predicate.clone());

                let interval = analysis
                    .as_ref()
                    .map(|a| a.eval_condition(f, block.id, index, condition))
                    .unwrap_or(Trivalent::Unknown);
                let sym = symbolic.as_ref().and_then(|r| r.outcome(block.id, index));

                let result = discharge(interval, sym, *property, &predicate, note);
                outcomes.push(ObligationOutcome { obligation, result });
                continue;
            }

            // Implied memory-op obligations: discharged by the symbolic memory
            // model. Enumerated from the IR so a memory op is never silently
            // treated as safe (when symbolic did not run, it is `Open`).
            for &property in inst.implied_checks() {
                // Size-overflow is a bug-finding-only obligation: in sound `verify` mode
                // it is not enumerated, so it never affects PASS/FAIL there (an allocation
                // size is treated as non-wrapping under `alloc-succeeds`, as before). Only
                // the kernel bug-finding mode checks it.
                if matches!(
                    property,
                    SafetyProperty::NoSizeOverflow
                        | SafetyProperty::DataRace
                        | SafetyProperty::DoubleFetch
                        | SafetyProperty::SleepInAtomic
                        | SafetyProperty::TaintedSink
                        | SafetyProperty::TypestateViolation
                        | SafetyProperty::SecretDependent
                ) && !config.bug_finding
                {
                    continue;
                }
                let id = ObligationId(*next_id);
                *next_id += 1;
                let location = Location::level_only(config.level)
                    .in_function(f.name.as_str())
                    .at_instruction(index as u32)
                    .with_raw(block.inst_spans.get(index).cloned().flatten());
                let decision = symbolic
                    .as_ref()
                    .and_then(|r| r.mem_decision(block.id, index, property));
                let predicate = decision
                    .map(|d| d.predicate.clone())
                    .unwrap_or_else(|| property.describe().to_string());
                let obligation =
                    ProofObligation::new(id, property, location, predicate.clone());

                let result = match decision {
                    Some(d) if d.proven => proven_by_symbolic_memory(&predicate, &sym_assumptions),
                    Some(d) => match &d.refutation {
                        Some(model) => refuted_by_symbolic(property, &predicate, model.clone()),
                        None => open_memory(property, &predicate, &d.residual),
                    },
                    None => open_memory(property, &predicate, not_analyzed_reason(&symbolic)),
                };
                outcomes.push(ObligationOutcome { obligation, result });
            }
        }
    }

    let verdict = Verdict::combine_all(outcomes.iter().map(ObligationOutcome::verdict));
    let lock_edges = symbolic
        .as_ref()
        .map(|r| r.lock_edges.clone())
        .unwrap_or_default();
    let race_accesses = symbolic
        .as_ref()
        .map(|r| r.race_accesses.clone())
        .unwrap_or_default();
    let race_trace = symbolic
        .as_ref()
        .map(|r| r.race_trace.clone())
        .unwrap_or_default();
    FunctionReport {
        function: f.name.clone(),
        verdict,
        outcomes,
        truncated,
        lock_edges,
        race_accesses,
        race_trace,
    }
}

/// Combine the interval result and the symbolic result into one obligation
/// outcome. Intervals are tried first (cheapest); an interval `Unknown`
/// escalates to the symbolic linear proof.
fn discharge(
    interval: Trivalent,
    symbolic: Option<SymOutcome>,
    property: SafetyProperty,
    predicate: &str,
    note: &str,
) -> ObligationResult {
    match interval {
        Trivalent::True => proven_by_intervals(predicate, note),
        Trivalent::False => refuted(property, predicate, note),
        Trivalent::Unknown => match symbolic {
            Some(SymOutcome::Proven) => proven_by_symbolic(predicate, note),
            Some(SymOutcome::Refuted(model)) => refuted_by_symbolic(property, predicate, model),
            _ => open(property, predicate, note),
        },
    }
}

fn proven_by_intervals(predicate: &str, note: &str) -> ObligationResult {
    ObligationResult::Proven(ProofTree::new(ProofStep::leaf(
        predicate.to_string(),
        Justification::AbstractInterpretation {
            domain: "interval".into(),
            invariant: format!("{predicate} holds for the inferred interval ({note})"),
        },
    )))
}

fn proven_by_symbolic(predicate: &str, note: &str) -> ObligationResult {
    let tree = ProofTree::new(ProofStep::leaf(
        predicate.to_string(),
        Justification::SmtUnsat {
            solver: "internal-linear".into(),
            unsat_core: vec![format!("path condition implies `{predicate}` ({note})")],
        },
    ))
    .with_assumptions(vec![LINEAR_ASSUMPTION.into()]);
    ObligationResult::Proven(tree)
}

fn proven_by_symbolic_memory(predicate: &str, assumptions: &[String]) -> ObligationResult {
    let tree = ProofTree::new(ProofStep::leaf(
        predicate.to_string(),
        Justification::SmtUnsat {
            solver: "symbolic-memory".into(),
            unsat_core: vec![predicate.to_string()],
        },
    ))
    .with_assumptions(assumptions.to_vec());
    ObligationResult::Proven(tree)
}

/// Why a memory op produced no symbolic decision, kept distinct so the scaling
/// sweep can separate three very different situations that all read as `Open`:
///
/// - **disabled** — symbolic analysis was switched off (a config, not a limit);
/// - **truncated** — exploration hit its visit budget, after which *no* decisions
///   are reported for the whole function (a deliberate soundness rule: truncation
///   must never hide a violating path, so every op falls back to `Open`);
/// - **undecided** — exploration ran to completion and *reached* this op but the
///   symbolic memory model could not decide it (a loop body it does not summarise,
///   or an unsupported construct) — the genuine per-op engine limit.
///
/// All three are sound: the op is still enumerated as an obligation and stays
/// `Open`, so the function can never `PASS` on an unanalysed access. The split only
/// makes the *reason* honest, so a coverage cap is not mistaken for an engine gap
/// (nor either for a hidden front-end truncation, which cannot reach here — a
/// dropped body yields fewer obligations or a whole-function parse error, not an
/// `Open` memory op). See `Verification/`.
fn not_analyzed_reason(symbolic: &Option<SymbolicReport>) -> &'static str {
    match symbolic {
        None => "memory operation not analyzed (symbolic analysis disabled)",
        Some(r) if r.truncated => {
            "memory operation not analyzed (symbolic exploration truncated at the visit budget)"
        }
        Some(_) => "memory operation not analyzed (reached but not decided by the \
                    symbolic memory model: loop body or unsupported op)",
    }
}

fn open_memory(property: SafetyProperty, predicate: &str, reason: &str) -> ObligationResult {
    ObligationResult::Open {
        residual: vec![ResidualObligation {
            predicate: predicate.to_string(),
            reason: reason.to_string(),
        }],
        suggested: vec![SuggestedAssumption {
            assumption: format!("an invariant establishing `{predicate}`"),
            rationale: format!("{} would then follow", property.describe()),
        }],
    }
}

fn refuted(property: SafetyProperty, predicate: &str, note: &str) -> ObligationResult {
    ObligationResult::Refuted(CounterExample {
        summary: format!(
            "{}: {predicate} is false for every value in the inferred interval ({note})",
            property.describe()
        ),
        // The interval proof establishes the violation for the whole
        // over-approximation; for symbolic definite violations the bit-precise
        // layer supplies a concrete model (see `refuted_by_symbolic`).
        model: Model::default(),
        trace: vec![format!("at check: {note}")],
    })
}

/// A refutation discharged by the symbolic engine: on a genuinely reachable
/// (exact) path the property is *always* violated, witnessed by a concrete
/// bit-precise model.
fn refuted_by_symbolic(
    property: SafetyProperty,
    predicate: &str,
    model: Model,
) -> ObligationResult {
    ObligationResult::Refuted(CounterExample {
        summary: format!(
            "{}: `{predicate}` is violated for the witnessed inputs on a reachable path",
            property.describe()
        ),
        model,
        trace: vec!["symbolic execution reached this point with the model below".into()],
    })
}

fn open(property: SafetyProperty, predicate: &str, note: &str) -> ObligationResult {
    ObligationResult::Open {
        residual: vec![ResidualObligation {
            predicate: predicate.to_string(),
            reason: "neither interval analysis nor the linear symbolic layer could \
                     decide it; needs a stronger domain or full SMT (later increment)"
                .into(),
        }],
        suggested: vec![SuggestedAssumption {
            assumption: format!("a bound establishing `{predicate}` at this point"),
            rationale: format!("{} would then follow directly ({note})", property.describe()),
        }],
    }
}

/// Render a condition to a readable predicate string.
fn render_condition(c: &Condition) -> String {
    match c {
        Condition::True => "true".to_string(),
        Condition::Cmp { op, lhs, rhs } => {
            format!("{} {} {}", render_operand(lhs), render_cmp(*op), render_operand(rhs))
        }
        Condition::And(cs) => join(cs, " && "),
        Condition::Or(cs) => join(cs, " || "),
        Condition::Not(c) => format!("!({})", render_condition(c)),
    }
}

fn join(cs: &[Condition], sep: &str) -> String {
    if cs.is_empty() {
        return "true".to_string();
    }
    cs.iter()
        .map(render_condition)
        .collect::<Vec<_>>()
        .join(sep)
}

fn render_cmp(op: csolver_ir::CmpOp) -> &'static str {
    use csolver_ir::CmpOp::*;
    match op {
        Eq => "==",
        Ne => "!=",
        Ult | Slt => "<",
        Ule | Sle => "<=",
        Ugt | Sgt => ">",
        Uge | Sge => ">=",
    }
}

fn render_operand(op: &Operand) -> String {
    match op {
        Operand::Reg(r) => format!("{r}"),
        Operand::Const(Const::Int(bv)) => format!("{}", bv.unsigned()),
        Operand::Const(Const::Null) => "null".into(),
        Operand::Const(Const::Undef) => "undef".into(),
        Operand::Const(Const::Symbol(s)) => format!("@{s}"),
        Operand::Const(Const::SymbolOffset(s, off)) => format!("@{s}+{off}"),
    }
}

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
