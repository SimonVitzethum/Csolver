//! The acyclic path-enumerating symbolic executor with a symbolic memory model.
//!
//! Each path carries a [`PathState`]: a symbolic register environment
//! (scalars and pointers), a per-path region table (so allocate/free is
//! path-sensitive), a path condition, and a set of assumed facts. At every
//! memory operation the executor decides the canonical safety obligations using
//! the path condition, the region table and the linear solver.
//!
//! This increment proves (`Proven`) or leaves open (`Unknown`) — it never
//! refutes, because a sound refutation needs a satisfiable model on a provably
//! reachable path, which the UNSAT-only solver cannot supply.

use crate::ExecLimits;
use csolver_absint::{
    analyze_induction, analyze_intervals, analyze_zones, Bound, EqExitIndVar, InductionAnalysis,
    IntervalAnalysis, PtrIndVar, ZoneAnalysis,
};
use csolver_cfg::{Dominators, Loops};
use csolver_core::{Model, RegionKind, SafetyProperty};
use crate::summary::{Affine, ProvTransfer, RetSummary, Summary};
use csolver_ir::{
    BasicBlock, BinOp, BlockId, Callee, CastOp, CmpOp, Condition, Const, DataLayout, FieldContract,
    FuncId, Function, GlobalDef, Inst, MemKind, Operand, PtrContract, RValue, RefResult, RegId,
    SizeSpec, Terminator, Type,
};
use csolver_memory::{AliasResult, LifetimeState, Permissions};
use csolver_solver::{
    bitprecise, prove_implies_method, BvOp, CmpOp as SCmp, ExprCtx, ExprId, Node, ProofMethod,
};
use std::collections::{HashMap, HashSet};

const PTR_WIDTH: u32 = 64;
const LAYOUT: DataLayout = DataLayout::LP64;
/// The largest valid allocation/offset magnitude: `isize::MAX`. A successful
/// allocation (or a valid Rust slice/reference) has a byte size in
/// `[0, isize::MAX]` — the allocator and `Layout` guarantee it — so its element
/// count times the element size does not wrap. Recording this lets a memory-OOB
/// counterexample over a *symbolic*-size region stay faithful (no wrapped
/// `count * stride` fabricating a too-small buffer).
const ISIZE_MAX: u128 = i64::MAX as u128;

/// Named assumptions a symbolic proof may rely on.
const ALLOC_SUCCEEDS: &str = "alloc-succeeds";
const LINEAR_NO_OVERFLOW: &str = "linear-no-overflow";
const PARAM_CONTRACTS: &str = "param-contracts";
/// A callee assuming its integer parameter stays in the range every visible caller
/// passes (interprocedural scalar precondition — see `discharge_with_scalars`).
const SCALAR_PRECONDITION: &str = "caller-range-precondition";
const SLICE_ABI: &str = "slice-abi";
/// Proofs about accesses to global/static definitions rest on the module's
/// declared global layout (size/alignment/mutability of `@name = global/constant …`).
const GLOBAL_MEMORY: &str = "global-memory";
/// A `&T`/`&mut T` value is a valid reference to its pointee (Rust's reference
/// invariant), even when the analysis cannot see where it came from.
const VALID_REFERENCE: &str = "valid-reference";
const STRUCT_ABI: &str = "struct-abi";

/// **Unconditional** lock-acquiring kernel primitives (by argument-0 = the lock).
/// Re-acquiring one already held on a path is an AA self-deadlock
/// (`SafetyProperty::DataRace`). Only primitives that *always* take the lock are
/// listed — `*_trylock` may fail, so it is deliberately excluded (adding it would
/// false-flag a `trylock`-then-`lock` retry). A *release* needs no list: any call
/// handed a held lock's base drops it (see `check_lock_call`), which covers matched
/// unlocks (incl. `spin_unlock_irqrestore`), unlock wrappers, and callees that unlock.
const LOCK_ACQUIRE: &[&str] = &[
    "spin_lock", "_raw_spin_lock", "spin_lock_irq", "spin_lock_bh", "spin_lock_irqsave",
    "_raw_spin_lock_irq", "_raw_spin_lock_bh", "_raw_spin_lock_irqsave",
    "raw_spin_lock", "raw_spin_lock_irq", "raw_spin_lock_irqsave", "raw_spin_lock_bh",
    "mutex_lock", "mutex_lock_nested", "mutex_lock_interruptible", "mutex_lock_killable",
    "read_lock", "write_lock", "read_lock_irq", "write_lock_irq",
    "read_lock_irqsave", "write_lock_irqsave", "read_lock_bh", "write_lock_bh",
    "_raw_read_lock", "_raw_write_lock", "down", "down_write", "down_read",
    "down_interruptible", "down_killable", "down_write_killable",
];

/// **Spinning** lock acquisitions — those that enter **atomic context** (preemption off),
/// so a subsequent sleeping call deadlocks. Spinlocks and rwlocks spin; `mutex`/`down`
/// (semaphore) may themselves sleep and are NOT atomic context (they are blocking calls).
const SPIN_ACQUIRE: &[&str] = &[
    "spin_lock", "_raw_spin_lock", "spin_lock_irq", "spin_lock_bh", "spin_lock_irqsave",
    "_raw_spin_lock_irq", "_raw_spin_lock_bh", "_raw_spin_lock_irqsave",
    "raw_spin_lock", "raw_spin_lock_irq", "raw_spin_lock_irqsave", "raw_spin_lock_bh",
    "read_lock", "write_lock", "read_lock_irq", "write_lock_irq",
    "read_lock_irqsave", "write_lock_irqsave", "read_lock_bh", "write_lock_bh",
    "_raw_read_lock", "_raw_write_lock",
];

/// Cap on the per-function ordered interleaving trace — a very long function contributes at
/// most this many events, keeping the two-thread interleaving DFS bounded.
const RACE_TRACE_CAP: usize = 64;

// A spinning-lock **release** (`spin_unlock`/…) leaves atomic context. It is not a named
// set here: like any other call it is handed the lock base as a pointer argument, and the
// general call arm below already drops every passed base from `spin_held` (and `locks_held`).

/// Calls that **may sleep** (block): illegal while a spinlock is held (atomic context).
/// The unambiguous always-may-sleep primitives — a `mutex`/semaphore acquire, an explicit
/// yield/sleep, a completion/RCU wait, or the kernel's own `might_sleep` marker. (GFP-flag-
/// conditional allocators like `kmalloc(GFP_KERNEL)` need flag analysis and are not here.)
const BLOCKING: &[&str] = &[
    "mutex_lock", "mutex_lock_nested", "mutex_lock_interruptible", "mutex_lock_killable",
    "down", "down_write", "down_read", "down_interruptible", "down_killable",
    "down_write_killable", "down_timeout", "schedule", "schedule_timeout",
    "schedule_timeout_interruptible", "schedule_timeout_uninterruptible", "io_schedule",
    "msleep", "msleep_interruptible", "ssleep", "usleep_range", "might_sleep",
    "___might_sleep", "__might_sleep", "wait_for_completion", "wait_for_completion_interruptible",
    "wait_for_completion_killable", "wait_for_completion_timeout", "synchronize_rcu",
    "synchronize_srcu", "synchronize_net", "synchronize_irq", "flush_work",
    "flush_workqueue", "cond_resched",
];

/// Whether a scalar `SafetyCheck` was discharged symbolically.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymOutcome {
    /// Proved on every path that reaches it.
    Proven,
    /// Not proved.
    Unknown,
    /// Refuted: on an exact (genuinely reachable) path the property is *always*
    /// violated, witnessed by the concrete model.
    Refuted(Model),
}

/// The decision for one implied memory-op obligation.
#[derive(Debug, Clone)]
pub struct MemDecision {
    /// Whether it was proved (on every reaching path).
    pub proven: bool,
    /// A concrete counterexample, when the obligation was *refuted* on an exact
    /// path (a definite violation). `None` for proved or merely-undecided.
    pub refutation: Option<Model>,
    /// A human-readable rendering of what was (or would be) shown.
    pub predicate: String,
    /// Why it is not proved (empty when proved).
    pub residual: String,
}

/// The result of symbolically discharging a function.
#[derive(Debug, Clone, Default)]
pub struct SymbolicReport {
    /// Decisions for explicit `SafetyCheck` instructions, keyed by (block, idx).
    pub decided: HashMap<(BlockId, usize), SymOutcome>,
    /// Decisions for implied memory-op obligations, keyed by (block, idx, prop).
    pub mem: HashMap<(BlockId, usize, SafetyProperty), MemDecision>,
    /// Named assumptions the proofs depend on.
    pub assumptions: Vec<String>,
    /// **Lock-order edges** observed in this function: `(held-class, acquired-class)`
    /// pairs (see `lockclass`). Empty unless a lock was acquired while another was held.
    /// Aggregated program-wide for ABBA cycle detection.
    pub lock_edges: Vec<(String, String)>,
    /// **Shared-memory access records**: `(access-class, is_write, lock-classes held)` per
    /// access to a shareable location. Aggregated program-wide for the lockset data-race check.
    pub race_accesses: Vec<(String, bool, Vec<String>)>,
    /// **Ordered event trace** `(kind, class)` (0=acquire,1=release,2=read,3=write) for the
    /// two-thread interleaving atomicity check (`csolver_verifier::interleave`).
    pub race_trace: Vec<(u8, String)>,
    /// Whether exploration was truncated (then no decisions are reported).
    pub truncated: bool,
}

impl SymbolicReport {
    /// The outcome for an explicit `SafetyCheck`.
    pub fn outcome(&self, block: BlockId, index: usize) -> Option<SymOutcome> {
        self.decided.get(&(block, index)).cloned()
    }

    /// The decision for an implied memory obligation.
    pub fn mem_decision(
        &self,
        block: BlockId,
        index: usize,
        prop: SafetyProperty,
    ) -> Option<&MemDecision> {
        self.mem.get(&(block, index, prop))
    }
}

/// Symbolically discharge the obligations of `f` (default limits, no
/// interprocedural summaries — calls are havoc'd).
pub fn discharge_function(f: &Function) -> SymbolicReport {
    discharge_inner(f, ExecLimits::default(), &HashMap::new(), &HashMap::new(), &[], &[], &[], &HashMap::new(), &HashMap::new(), &HashMap::new(), None)
}

/// As [`discharge_function`], but using the given function summaries to reason
/// about calls (provenance-preserving returns, effect-aware heap handling).
pub fn discharge_with_summaries(
    f: &Function,
    summaries: &HashMap<FuncId, Summary>,
) -> SymbolicReport {
    discharge_inner(f, ExecLimits::default(), summaries, &HashMap::new(), &[], &[], &[], &HashMap::new(), &HashMap::new(), &HashMap::new(), None)
}

/// As [`discharge_with_summaries`], plus per-parameter pointer contracts: a
/// contracted pointer parameter is modelled as a known live region of its
/// `dereferenceable` size, so accesses through it can be proved (under the
/// `param-contracts` assumption).
pub fn discharge_full(
    f: &Function,
    summaries: &HashMap<FuncId, Summary>,
    contracts: &[Option<PtrContract>],
    globals: &HashMap<String, GlobalDef>,
) -> SymbolicReport {
    discharge_inner(f, ExecLimits::default(), summaries, &HashMap::new(), contracts, &[], &[], globals, &HashMap::new(), &HashMap::new(), None)
}

/// As [`discharge_full`], plus interprocedural **member-provenance**:
/// `field_contracts[i]` lists the aggregate fields of parameter `i` that every
/// call site provably fills with a valid pointer. Each is seeded as an initial
/// store of a fresh valid region into that field's slot, so the callee's load of
/// the field yields a pointer with provenance (proved under the field pointee's
/// own trust basis).
#[allow(clippy::too_many_arguments)]
pub fn discharge_with_fields(
    f: &Function,
    summaries: &HashMap<FuncId, Summary>,
    contracts: &[Option<PtrContract>],
    field_contracts: &[Vec<FieldContract>],
    globals: &HashMap<String, GlobalDef>,
    prov_grants: &HashMap<u32, HashSet<u32>>,
    bug_finding: bool,
    exported: bool,
    assume_valid_params: bool,
) -> SymbolicReport {
    discharge_with_scalars(
        f, summaries, &HashMap::new(), contracts, field_contracts, &[], globals, prov_grants,
        &HashMap::new(), None, ExecLimits::default().time_budget, bug_finding, exported,
        assume_valid_params,
    )
}

/// As [`discharge_with_fields`], plus per-parameter **scalar value-range preconditions**:
/// `scalar_pre[i] = Some((lo, hi))` lets a *non-entry* function assume its integer
/// parameter `i` stays in `[lo, hi]` — the union of the ranges every visible caller passes
/// (see the interprocedural scalar synthesis). Prove-only, surfaced as a
/// `caller-range-precondition` assumption.
#[allow(clippy::too_many_arguments)]
pub fn discharge_with_scalars(
    f: &Function,
    summaries: &HashMap<FuncId, Summary>,
    name_summaries: &HashMap<String, Summary>,
    contracts: &[Option<PtrContract>],
    field_contracts: &[Vec<FieldContract>],
    scalar_pre: &[Option<(i128, i128)>],
    globals: &HashMap<String, GlobalDef>,
    prov_grants: &HashMap<u32, HashSet<u32>>,
    global_fn_ptrs: &HashMap<String, Vec<(u64, FuncId)>>,
    analysis_in: Option<&IntervalAnalysis>,
    time_budget: Option<std::time::Duration>,
    bug_finding: bool,
    exported: bool,
    assume_valid_params: bool,
) -> SymbolicReport {
    let limits =
        ExecLimits { bug_finding, exported, assume_valid_params, time_budget, ..ExecLimits::default() };
    discharge_inner(
        f, limits, summaries, name_summaries, contracts, field_contracts, scalar_pre, globals,
        prov_grants, global_fn_ptrs, analysis_in,
    )
}

/// As [`discharge_function`], with explicit limits and no summaries.
///
/// Loops are handled by *cutting* back-edges and replacing each loop header's
/// parameters with fresh symbols constrained by the sound interval invariant at
/// that header (from `csolver-absint`). One symbolic pass over the loop body —
/// under that invariant plus the loop guard (a path condition) — therefore
/// covers every iteration.
pub fn discharge_with(f: &Function, limits: ExecLimits) -> SymbolicReport {
    discharge_inner(f, limits, &HashMap::new(), &HashMap::new(), &[], &[], &[], &HashMap::new(), &HashMap::new(), &HashMap::new(), None)
}

/// Every symbol name referenced by an operand of `f` (`Const::Symbol` /
/// `Const::SymbolOffset`), for seeding the referenced-globals regions.
fn referenced_symbols(f: &Function) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut op = |o: &Operand| match o {
        Operand::Const(Const::Symbol(n)) | Operand::Const(Const::SymbolOffset(n, _)) => {
            out.push(n.clone())
        }
        _ => {}
    };
    for b in &f.blocks {
        for inst in &b.insts {
            match inst {
                Inst::Alloc { count, .. } => op(count),
                Inst::Load { ptr, .. } => op(ptr),
                Inst::Store { ptr, value, .. } => {
                    op(ptr);
                    op(value);
                }
                Inst::PtrOffset { base, index, .. } => {
                    op(base);
                    op(index);
                }
                Inst::FieldPtr { base, .. } => op(base),
                Inst::RefWitness { src, .. } => {
                    if let Some(s) = src {
                        op(s);
                    }
                }
                Inst::Assign { value, .. } => match value {
                    RValue::Use(o) => op(o),
                    RValue::Bin { lhs, rhs, .. } | RValue::Cmp { lhs, rhs, .. } => {
                        op(lhs);
                        op(rhs);
                    }
                    RValue::Cast { operand, .. } => op(operand),
                    RValue::Select { cond, then_val, else_val } => {
                        op(cond);
                        op(then_val);
                        op(else_val);
                    }
                },
                Inst::Call { args, .. } | Inst::Intrinsic { args, .. } => {
                    args.iter().for_each(&mut op)
                }
                Inst::MemIntrinsic { dst, src, len, .. } => {
                    op(dst);
                    if let Some(sp) = src {
                        op(sp);
                    }
                    op(len);
                }
                Inst::Dealloc { ptr, .. } => op(ptr),
                Inst::ProvLabel { ptr, .. } | Inst::CapRequire { ptr, .. } => op(ptr),
                Inst::ProvPropagate { dst, src } => { op(dst); op(src); }
                Inst::CapRequireIfAlias { a, b, .. } => { op(a); op(b); }
                Inst::CapRequireIfAliasFields { obj, .. } => op(obj),
                Inst::TaintSource { val, .. }
                | Inst::TaintCheck { val, .. }
                | Inst::TaintClear { val, .. }
                | Inst::TypestateSet { val, .. }
                | Inst::TypestateRequire { val, .. }
                | Inst::Refcount { val, .. }
                | Inst::SecretCheck { val, .. } => op(val),
                Inst::TypestateLeakCheck { escaping, .. } => {
                    if let Some(e) = escaping {
                        op(e);
                    }
                }
                Inst::TypestateYield { .. } => {}
                Inst::SafetyCheck { .. } | Inst::Asm { .. } => {}
            }
        }
        match &b.term {
            Terminator::Return(Some(o)) => op(o),
            Terminator::CondBr { cond, then_args, else_args, .. } => {
                op(cond);
                then_args.iter().for_each(&mut op);
                else_args.iter().for_each(&mut op);
            }
            Terminator::Br { args, .. } => args.iter().for_each(&mut op),
            Terminator::Switch { value, .. } => op(value),
            Terminator::Return(None) | Terminator::Unreachable => {}
        }
    }
    out
}

#[allow(clippy::too_many_arguments)]
fn discharge_inner(
    f: &Function,
    limits: ExecLimits,
    summaries: &HashMap<FuncId, Summary>,
    name_summaries: &HashMap<String, Summary>,
    contracts: &[Option<PtrContract>],
    field_contracts: &[Vec<FieldContract>],
    scalar_pre: &[Option<(i128, i128)>],
    globals: &HashMap<String, GlobalDef>,
    prov_grants: &HashMap<u32, HashSet<u32>>,
    global_fn_ptrs: &HashMap<String, Vec<(u64, FuncId)>>,
    analysis_in: Option<&IntervalAnalysis>,
) -> SymbolicReport {
    // Reuse the caller's interval analysis when supplied (the verifier already
    // computes it for interval-based discharge), so it is not recomputed here —
    // a single clone instead of a second fixpoint. Falls back to computing it.
    let analysis = match analysis_in {
        Some(a) => a.clone(),
        None => analyze_intervals(f),
    };
    let zones = analyze_zones(f);
    let inductions = analyze_induction(f);
    let dominators = Dominators::new(analysis.cfg());
    let loops = Loops::detect(analysis.cfg(), &dominators);

    // Per loop header: the set of registers the loop body may redefine (so they
    // can be havoc'd — not just the header's own parameters), and whether the
    // body may free memory (so region lifetimes can be invalidated). These are
    // what make a single body pass a *sound* over-approximation of all
    // iterations.
    let mut headers: HashSet<BlockId> = HashSet::new();
    let mut loop_modified: HashMap<BlockId, Vec<RegId>> = HashMap::new();
    let mut loop_frees: HashMap<BlockId, bool> = HashMap::new();
    let mut loop_bodies: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for l in loops.all() {
        let header = analysis.cfg().block_id(l.header);
        headers.insert(header);
        let mut modified: HashSet<RegId> = HashSet::new();
        let mut frees = false;
        let mut body: Vec<BlockId> = Vec::new();
        for &node in &l.body {
            let bid = analysis.cfg().block_id(node);
            body.push(bid);
            if let Some(b) = f.block(bid) {
                modified.extend(b.params.iter().map(|(r, _)| *r));
                for inst in &b.insts {
                    if let Some(r) = inst.defined_reg() {
                        modified.insert(r);
                    }
                    if matches!(inst, Inst::Dealloc { .. }) {
                        frees = true;
                    }
                }
            }
        }
        // Deterministic order: the havoc assigns fresh symbol ids in this order, and
        // a witness names induction symbols (`ind…`), so a `HashSet`'s arbitrary order
        // would make the reported counterexample non-deterministic.
        let mut modified: Vec<RegId> = modified.into_iter().collect();
        modified.sort_unstable_by_key(|r| r.0);
        loop_modified.insert(header, modified);
        loop_frees.insert(header, frees);
        loop_bodies.insert(header, body);
    }

    let mut ex = Explorer {
        ctx: ExprCtx::new(),
        fresh: 0,
        prov_ids: 0,
        bug_finding: limits.bug_finding,
        exported: limits.exported,
        assume_valid_params: limits.assume_valid_params,
        visits: 0,
        truncated: false,
        limits,
        deadline: limits.time_budget.map(|b| std::time::Instant::now() + b),
        scalar: HashMap::new(),
        mem: HashMap::new(),
        assumptions: HashSet::new(),
        analysis,
        zones,
        inductions,
        dominators,
        headers,
        loop_modified,
        loop_frees,
        loop_bodies,
        summaries: summaries.clone(),
        name_summaries: name_summaries.clone(),
        prov_grants: prov_grants.clone(),
        field_offsets: HashMap::new(),
        field_frontier: HashMap::new(),
        scalar_ptr_cause: classify_scalar_ptr_defs(f),
        global_rids: HashMap::new(),
        global_fnptrs: HashMap::new(),
        prove_cache: HashMap::new(),
        lock_classes: crate::lockclass::resolve_lock_classes(f),
        lock_edges: HashSet::new(),
        race_accesses: HashSet::new(),
        race_trace: Vec::new(),
        f,
    };

    let mut env: HashMap<RegId, SymValue> = HashMap::new();
    let mut regions: Vec<SymRegion> = Vec::new();
    let mut facts: Vec<ExprId> = Vec::new();
    // Pass 1: every parameter without a pointer contract (so length parameters
    // a slice contract refers to are available in pass 2).
    for (i, (reg, ty)) in f.params.iter().enumerate() {
        if contracts.get(i).and_then(|c| c.as_ref()).is_none() {
            // Name scalar parameters `arg{i}` so a counterexample model is
            // readable; pointer parameters get the usual opaque placeholder.
            let v = if ty.is_ptr() {
                ex.fresh_value(ty, POrigin::Param)
            } else {
                let width = type_width(ty);
                let sym = ex.ctx.symbol(format!("arg{i}"), width);
                // Interprocedural scalar precondition: a NON-entry function's integer
                // parameter is bounded by the union of the ranges its (all visible) callers
                // pass — so an index derived from it is proven in bounds instead of flagged
                // at a value no caller can produce. Not applied to an adversarial entry,
                // whose parameters are attacker-controlled. Prove-only (a `caller-range`
                // assumption), so an out-of-range witness is not a real counterexample.
                if !limits.exported {
                    if let Some(Some((lo, hi))) = scalar_pre.get(i) {
                        let mask = |v: i128| if width >= 128 { v as u128 } else { (v as u128) & ((1u128 << width) - 1) };
                        let lo_e = ex.ctx.int(width, mask(*lo));
                        let hi_e = ex.ctx.int(width, mask(*hi));
                        let ge = ex.ctx.cmp(SCmp::Sle, lo_e, sym);
                        let le = ex.ctx.cmp(SCmp::Sle, sym, hi_e);
                        facts.push(ge);
                        facts.push(le);
                        ex.assumptions.insert(SCALAR_PRECONDITION);
                    }
                }
                SymValue::Scalar(sym)
            };
            env.insert(*reg, v);
        }
    }
    // Member-provenance seed stores, filled alongside the param regions below and
    // installed as the path's initial heap so the first load of each seeded field
    // reads back a valid pointer.
    let mut initial_heap: Vec<StoreRecord> = Vec::new();
    // Pass 2: contracted pointer parameters become known live regions.
    for (i, (reg, _ty)) in f.params.iter().enumerate() {
        let Some(c) = contracts.get(i).and_then(|c| c.as_ref()) else {
            continue;
        };
        let (size, assumption, nowrap) = match c.size {
            // A concrete byte size cannot wrap; nothing extra is needed (`true`).
            SizeSpec::Bytes(n) => {
                let truth = ex.ctx.boolean(true);
                (ex.ctx.int(PTR_WIDTH, n as u128), PARAM_CONTRACTS, Some(truth))
            }
            SizeSpec::ParamElements { len_param, elem_size } => {
                let len_reg = f.params[len_param as usize].0;
                let len_e = match env.get(&len_reg) {
                    Some(SymValue::Scalar(e)) => *e,
                    _ => ex.fresh_scalar(PTR_WIDTH),
                };
                let es = ex.ctx.int(PTR_WIDTH, elem_size as u128);
                let size = ex.ctx.bin(BvOp::Mul, len_e, es);
                // A valid slice has `len * size_of::<T>() <= isize::MAX`, so the
                // length times the element size does not wrap (`slice-abi`).
                let nowrap = ex.size_no_wrap_fact(len_e, elem_size);
                (size, SLICE_ABI, Some(nowrap))
            }
            // An aggregate of unknown layout: a fresh symbolic size. Field accesses
            // are proved in bounds by construction (`struct-abi`), so the region is
            // prove-only (no refutation — `size_nowrap = None`).
            SizeSpec::Opaque => (ex.fresh_scalar(PTR_WIDTH), STRUCT_ABI, None),
        };
        // A precondition-style contract (internal function / closure /
        // synthesized minimum) proves but never refutes: `size_nowrap = None`
        // switches the in-bounds obligation to prove-only.
        let nowrap = if c.refutable { nowrap } else { None };
        let zero = ex.ctx.int(PTR_WIDTH, 0);
        let nonneg = ex.ctx.cmp(SCmp::Sle, zero, size);
        facts.push(nonneg);
        let rid = regions.len();
        regions.push(SymRegion {
            kind: RegionKind::Heap,
            size,
            state: LifetimeState::Live,
            perms: Permissions {
                read: c.readable,
                write: c.writable,
                exec: false,
            },
            // A synthesized contract names its own trust basis (e.g. the
            // internal-call-site derivation) instead of the declared-attribute
            // assumption its `SizeSpec` would imply.
            contract: Some(c.assumption.unwrap_or(assumption)),
            size_nowrap: nowrap,
            sentinel: c.sentinel,
            user_controlled: false,
            assumed: false,
            prov_labels: HashSet::new(),
        });
        env.insert(
            *reg,
            SymValue::Ptr(SymPointer {
                prov: Prov::Region(rid),
                offset: zero,
                align: c.align.max(1) as u64,
            }),
        );
        // Member-provenance: seed every field this parameter's call sites all fill
        // with a valid pointer. The pointee is a fresh live region; its address is
        // stored at the field's byte offset within this parameter's region — the
        // very offset the callee's `PtrOffset` field access computes — so the
        // load of the field reads back a pointer with provenance. Prove-only (a
        // precondition), so the seeded region never refutes.
        for fc in field_contracts.get(i).map(Vec::as_slice).unwrap_or(&[]) {
            let SizeSpec::Bytes(psize) = fc.pointee.size else { continue };
            let psize_e = ex.ctx.int(PTR_WIDTH, psize as u128);
            let prid = regions.len();
            regions.push(SymRegion {
                kind: RegionKind::Heap,
                size: psize_e,
                state: LifetimeState::Live,
                perms: Permissions {
                    read: fc.pointee.readable,
                    write: fc.pointee.writable,
                    exec: false,
                },
                contract: Some(fc.pointee.assumption.unwrap_or(PARAM_CONTRACTS)),
                size_nowrap: None,
                sentinel: None,
                user_controlled: false,
                assumed: false,
                prov_labels: HashSet::new(),
            });
            let palign = fc.pointee.align.max(1) as u64;
            let off_e = ex.ctx.int(PTR_WIDTH, fc.offset as u128);
            initial_heap.push(StoreRecord {
                target: SymPointer { prov: Prov::Region(rid), offset: off_e, align: palign },
                value: SymValue::Ptr(SymPointer {
                    prov: Prov::Region(prid),
                    offset: zero,
                    align: palign,
                }),
                size: PTR_WIDTH as u64 / 8,
            });
        }
    }
    // Referenced global/static definitions become regions that live for the
    // whole program: never freed, readable, writable iff not `constant`, with
    // an initializer (so a load from one is *not* an uninitialized read).
    // Sorted by name so region ids — and therefore every downstream id — are
    // deterministic.
    let mut names: Vec<String> = referenced_symbols(f)
        .into_iter()
        .filter(|n| globals.contains_key(n))
        .collect();
    names.sort();
    names.dedup();
    for name in names {
        let g = globals[&name];
        let rid = regions.len();
        let size = ex.ctx.int(PTR_WIDTH, g.size as u128);
        let truth = ex.ctx.boolean(true);
        regions.push(SymRegion {
            kind: RegionKind::Global,
            size,
            state: LifetimeState::Live,
            perms: Permissions { read: true, write: g.writable, exec: false },
            contract: Some(GLOBAL_MEMORY),
            size_nowrap: Some(truth),
            sentinel: None,
            user_controlled: false,
            assumed: false,
            prov_labels: HashSet::new(),
        });
        // A constant ops-struct/vtable global carries a devirtualisation table:
        // record it against the region id so a field load can resolve its target.
        if let Some(table) = global_fn_ptrs.get(&name) {
            ex.global_fnptrs.insert(rid, table.iter().copied().collect());
        }
        ex.global_rids.insert(name, (rid, g.align.max(1) as u64));
    }

    let state = PathState {
        env,
        regions,
        pathcond: Vec::new(),
        facts,
        heap: initial_heap,
        unwritten_reads: HashMap::new(),
        ref_regions: HashMap::new(),
            opaque_labels: HashMap::new(),
        tainted: HashMap::new(),
        typestates: HashMap::new(),
        refcounts: HashMap::new(),
        fn_ptrs: HashMap::new(),
        locks_held: HashSet::new(),
        spin_held: HashSet::new(),
        held_classes: HashMap::new(),
        user_fetches: HashSet::new(),
        freed_bases: HashSet::new(),
        exact: true,
    };
    ex.run_merged(state);

    if ex.truncated {
        return SymbolicReport {
            truncated: true,
            ..Default::default()
        };
    }

    let decided = ex
        .scalar
        .into_iter()
        .map(|(k, agg)| {
            let outcome = match agg.refutation {
                Some(model) => SymOutcome::Refuted(model),
                None if agg.all_proven => SymOutcome::Proven,
                None => SymOutcome::Unknown,
            };
            (k, outcome)
        })
        .collect();
    let mem = ex
        .mem
        .into_iter()
        .map(|(k, agg)| {
            (
                k,
                MemDecision {
                    proven: agg.all_proven,
                    refutation: agg.refutation,
                    predicate: agg.predicate,
                    residual: if agg.all_proven { String::new() } else { agg.residual },
                },
            )
        })
        .collect();
    let mut assumptions: Vec<String> = ex.assumptions.into_iter().map(String::from).collect();
    assumptions.sort();
    let mut lock_edges: Vec<(String, String)> = ex.lock_edges.into_iter().collect();
    lock_edges.sort();
    let mut race_accesses: Vec<(String, bool, Vec<String>)> = ex.race_accesses.into_iter().collect();
    race_accesses.sort();

    SymbolicReport {
        decided,
        mem,
        assumptions,
        lock_edges,
        race_accesses,
        race_trace: ex.race_trace,
        truncated: false,
    }
}

/// The base a materialised field region is keyed by: a tracked region, or an opaque
/// provenance identity (so `obj->field` off an *opaque* object also gets a stable region).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum RefBase {
    Region(usize),
    Opaque(u32),
}

/// The identity a **typestate resource** is keyed by: a pointer handle's base (a `FILE*`,
/// a lock, a struct) or a scalar value's identity (an `fd` integer — the same SSA value
/// denotes the same fd). General over both pointer and non-pointer resources.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ResKey {
    Ptr(RefBase),
    Val(ExprId),
}

/// Provenance of a symbolic pointer.
#[derive(Debug, Clone)]
enum Prov {
    Null,
    Region(usize),
    /// A **join of two provenances** at a `select`/PHI, under a discriminator: the
    /// pointer is `then` when `cond` holds and `else` otherwise (each a full
    /// `SymPointer`, so nested joins compose). Instead of collapsing a `select`
    /// of two regions to opaque, this keeps both, so an access through it is proved
    /// in bounds for *each* alternative under its guard — the `va_arg`
    /// register/overflow select, or any `cond ? &a[i] : &b[j]`. Language-agnostic.
    Select { cond: ExprId, then_ptr: Box<SymPointer>, else_ptr: Box<SymPointer> },
    /// No tracked provenance, tagged with *why* — purely diagnostic (it does not
    /// affect equality or any verdict; see the manual `PartialEq`), so the scaling
    /// sweep can split the "requires known provenance" residual by origin and
    /// separate the sound-extensible cases (provenance through memory) from the
    /// assumption-needed ones (raw-pointer call results, int→ptr).
    ///
    /// The `Option<u32>` is a **provenance identity**: a unique id minted for an opaque
    /// pointer (a raw-pointer parameter and anything derived from it by `gep`/copy, which
    /// carry the id through `prov.clone()`), or `None`. It is used *only* by the provenance
    /// machinery — labelling an opaque pointer, recognising two derived pointers as sharing
    /// a base, and materialised-field identity — and is **deliberately excluded from
    /// `PartialEq`** (see below), so aliasing, merging, and every existing verdict stay
    /// byte-identical: two opaque pointers remain interchangeable for the memory model.
    Unknown(POrigin, Option<u32>),
}

/// Why a pointer has no tracked provenance. Diagnostic only.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum POrigin {
    /// A pointer parameter with no derivable contract (a raw-pointer param, or an
    /// opaque-generic reference the front end could not contract).
    Param,
    /// An opaque pointer returned by a call with no return summary — a reference
    /// returned by `Index::index`/an internal fn (provenance exists in the source,
    /// recoverable by a `PtrFromArg` summary), or a raw pointer from
    /// `slice::from_raw_parts`/`<*T>::as_ptr` (assumption-needed). The two are not
    /// distinguished here without inspecting the callee; both stay `UNKNOWN`.
    Call,
    /// Loaded from memory with no provenance carried through the store. The
    /// sound-extensible case: store→load provenance (M3) would recover it.
    Load,
    /// An `int → ptr` cast. Provenance is fundamentally destroyed (strict
    /// provenance); stays `UNKNOWN` by design.
    IntToPtr,
    /// Havocked across a loop back-edge (a loop-modified pointer, conservatively
    /// opaque).
    Loop,
    // The merge/join family — kept as distinct origins rather than one "Merge"
    // catch-all, so a dominant join-loss is not mistaken for path merges in
    // general (the same don't-trust-a-coarse-bucket discipline, one level down).
    /// Joining two pointers of differing provenance at a `select`/PHI.
    SelectJoin,
    /// A region index that fell out of range when path-states were merged.
    RegionDrop,
    /// A block parameter / merged value with no incoming argument to evaluate.
    PhiFallback,
    /// A scalar value used where a pointer was expected (a pointer that was
    /// scalarised earlier and read back as an address). Carries *how* the scalar
    /// arose — the split that decides whether M3 can recover provenance soundly
    /// (the source had a pointer) or must leave it `UNKNOWN` (genuinely
    /// integer-derived).
    ScalarAsPtr(ScalarPtrCause),
}

/// How the integer value used as a pointer was computed — the proximate defining
/// instruction of the pointer operand. Diagnostic only.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScalarPtrCause {
    /// `ptr as usize` (`PtrToInt`) — the value *was* a pointer; provenance existed
    /// in the source and was cast away. Recoverable.
    PtrToInt,
    /// `Add`/`Sub`/… with a pointer-typed operand — offset arithmetic done as a
    /// scalar `Bin` instead of `PtrOffset`. The base carries provenance.
    /// Recoverable.
    PtrArith,
    /// A copy/reinterpret (`Use`/`Bitcast`) of a pointer-typed value. Recoverable.
    PtrCopy,
    /// `And`/`Or`/`Xor`/shift — bit manipulation of an address (alignment masking
    /// `ptr & !7`, tag bits). Provenance is genuinely ambiguous → stays `UNKNOWN`.
    BitMask,
    /// `Add`/`Sub`/… over operands with no pointer among them — pure integer
    /// arithmetic. Ambiguous → stays `UNKNOWN`.
    IntArith,
    /// A non-pointer value loaded from memory and used as an address (its
    /// provenance, if any, depends on store→load tracking).
    LoadedScalar,
    /// A call/index result the IR typed as non-pointer — e.g. `Index::index`
    /// returning `&T`, or an internal direct call returning a reference. The
    /// reference carries provenance in the source; the IR lost the pointer *type*.
    /// Recoverable via lowering type-fidelity / a pointer-return summary.
    CallResult,
    /// A block parameter (a PHI / loop-carried value): the pointer is threaded
    /// through a CFG join, where a scalarised incoming edge value loses the
    /// pointer representation. The store→load and merge machinery, not arithmetic.
    BlockParam,
    /// The result of a `PtrOffset`/`FieldPtr`/`Alloc` that nonetheless reached
    /// `eval_pointer` as a scalar — would indicate a representation leak in those
    /// (expected near-zero).
    PtrResult,
    /// A `Use`-copy chain that roots in a pointer-typed value — the type was erased
    /// by a copy into a non-pointer register. Provenance existed. Recoverable.
    PtrRoot,
    /// A `Use`-copy chain that roots in a scalar function parameter used as an
    /// address (an integer/`usize` parameter — provenance is the caller's, opaque).
    ScalarParam,
    /// A `Use`-copy chain that roots in `Const::Undef` — the MIR front end could
    /// not lower the pointer's computation and emitted `undef`. A *front-end*
    /// lowering gap, not an engine provenance gap.
    ConstUndef,
    /// Roots in `Const::Symbol` — the address of a named global/function. Has
    /// static provenance; recoverable by modelling it as a region.
    ConstSymbol,
    /// Roots in `Const::Int` — a literal integer used as an address. Genuinely
    /// ambiguous (strict-provenance int→ptr); stays `UNKNOWN`.
    ConstInt,
    /// Roots in `Const::Null`.
    ConstNull,
    /// Internal placeholder for an as-yet-unresolved `Use`-copy (never emitted: the
    /// resolution pass rewrites every `Copy` to its chain root).
    Copy,
    /// A chain root the resolver could not classify (an intrinsic/asm def, or a
    /// chain longer than the bound). Kept distinct so it is not silently folded
    /// into a recoverable category.
    Other,
}

impl ScalarPtrCause {
    fn residual(self) -> &'static str {
        match self {
            ScalarPtrCause::PtrToInt => {
                "pointer provenance is not tracked: scalar-as-pointer (ptr-to-int cast; recoverable)"
            }
            ScalarPtrCause::PtrArith => {
                "pointer provenance is not tracked: scalar-as-pointer (pointer arithmetic; recoverable)"
            }
            ScalarPtrCause::PtrCopy => {
                "pointer provenance is not tracked: scalar-as-pointer (pointer copy/reinterpret; recoverable)"
            }
            ScalarPtrCause::BitMask => {
                "pointer provenance is not tracked: scalar-as-pointer (bit-mask of an address; ambiguous)"
            }
            ScalarPtrCause::IntArith => {
                "pointer provenance is not tracked: scalar-as-pointer (integer arithmetic; ambiguous)"
            }
            ScalarPtrCause::LoadedScalar => {
                "pointer provenance is not tracked: scalar-as-pointer (loaded scalar; store-load dependent)"
            }
            ScalarPtrCause::CallResult => {
                "pointer provenance is not tracked: scalar-as-pointer (call/index result typed non-pointer; recoverable)"
            }
            ScalarPtrCause::BlockParam => {
                "pointer provenance is not tracked: scalar-as-pointer (block param / PHI; loop-carried)"
            }
            ScalarPtrCause::PtrResult => {
                "pointer provenance is not tracked: scalar-as-pointer (ptroffset/field/alloc leak)"
            }
            ScalarPtrCause::PtrRoot => {
                "pointer provenance is not tracked: scalar-as-pointer (copy rooted in a pointer value; recoverable)"
            }
            ScalarPtrCause::ScalarParam => {
                "pointer provenance is not tracked: scalar-as-pointer (copy rooted in a scalar parameter; opaque)"
            }
            ScalarPtrCause::ConstUndef => {
                "pointer provenance is not tracked: scalar-as-pointer (rooted in undef; FRONTEND lowering gap)"
            }
            ScalarPtrCause::ConstSymbol => {
                "pointer provenance is not tracked: scalar-as-pointer (rooted in a symbol address; recoverable)"
            }
            ScalarPtrCause::ConstInt => {
                "pointer provenance is not tracked: scalar-as-pointer (rooted in an integer constant; ambiguous)"
            }
            ScalarPtrCause::ConstNull => {
                "pointer provenance is not tracked: scalar-as-pointer (rooted in null)"
            }
            ScalarPtrCause::Copy => {
                "pointer provenance is not tracked: scalar-as-pointer (unresolved copy)"
            }
            ScalarPtrCause::Other => {
                "pointer provenance is not tracked: scalar-as-pointer (copy root unclassified: intrinsic/asm/deep)"
            }
        }
    }
}

/// Classify, per register, how a scalar value later used as a pointer was computed
/// — the proximate defining instruction. Built once per function and read at the
/// `eval_pointer` scalar fallback. Two passes: first an `is_ptr` map over every
/// defined register, then the cause, using it to tell offset-on-a-pointer
/// (`PtrArith`, recoverable) from pure integer arithmetic (`IntArith`, ambiguous).
fn classify_scalar_ptr_defs(f: &Function) -> HashMap<RegId, ScalarPtrCause> {
    let mut is_ptr: HashMap<RegId, bool> = HashMap::new();
    let mut note = |r: &RegId, p: bool| {
        is_ptr.insert(*r, p);
    };
    for (r, ty) in &f.params {
        note(r, ty.is_ptr());
    }
    for b in &f.blocks {
        for (r, ty) in &b.params {
            note(r, ty.is_ptr());
        }
        for inst in &b.insts {
            match inst {
                Inst::Assign { dst, ty, .. } | Inst::Load { dst, ty, .. } => note(dst, ty.is_ptr()),
                Inst::PtrOffset { dst, .. }
                | Inst::FieldPtr { dst, .. }
                | Inst::Alloc { dst, .. } => note(dst, true),
                Inst::Call { dst: Some(dst), ret_ty, .. } => note(dst, ret_ty.is_ptr()),
                _ => {}
            }
        }
    }
    let op_is_ptr = |op: &Operand| matches!(op, Operand::Reg(r) if is_ptr.get(r) == Some(&true));

    // First pass: a concrete root cause for each defining instruction. A scalar
    // `Use(reg)` copy gets a `Copy` placeholder + a `copy_of` edge, resolved to its
    // chain root in the second pass; `Use(const)` roots immediately. Scalar params
    // are seeded so a copy chain that bottoms out at one is attributed, not lost.
    let mut cause: HashMap<RegId, ScalarPtrCause> = HashMap::new();
    let mut copy_of: HashMap<RegId, RegId> = HashMap::new();
    for (r, ty) in &f.params {
        if !ty.is_ptr() {
            cause.insert(*r, ScalarPtrCause::ScalarParam);
        }
    }
    for b in &f.blocks {
        for (r, _) in &b.params {
            cause.insert(*r, ScalarPtrCause::BlockParam);
        }
        for inst in &b.insts {
            let (dst, c) = match inst {
                Inst::Load { dst, .. } => (*dst, ScalarPtrCause::LoadedScalar),
                Inst::Call { dst: Some(dst), .. } => (*dst, ScalarPtrCause::CallResult),
                Inst::PtrOffset { dst, .. }
                | Inst::FieldPtr { dst, .. }
                | Inst::Alloc { dst, .. } => (*dst, ScalarPtrCause::PtrResult),
                Inst::Assign { dst, value, .. } => {
                    let c = match value {
                        RValue::Cast { op: CastOp::PtrToInt, .. } => ScalarPtrCause::PtrToInt,
                        RValue::Cast { operand, .. } => {
                            if op_is_ptr(operand) {
                                ScalarPtrCause::PtrCopy
                            } else {
                                ScalarPtrCause::IntArith
                            }
                        }
                        RValue::Use(Operand::Reg(src)) => {
                            if is_ptr.get(src) == Some(&true) {
                                ScalarPtrCause::PtrCopy
                            } else {
                                copy_of.insert(*dst, *src);
                                ScalarPtrCause::Copy
                            }
                        }
                        RValue::Use(Operand::Const(c)) => match c {
                            Const::Undef => ScalarPtrCause::ConstUndef,
                            Const::Symbol(_) | Const::SymbolOffset(..) => {
                                ScalarPtrCause::ConstSymbol
                            }
                            Const::Int(_) => ScalarPtrCause::ConstInt,
                            Const::Null => ScalarPtrCause::ConstNull,
                        },
                        RValue::Bin { op, lhs, rhs } => match op {
                            BinOp::And | BinOp::Or | BinOp::Xor | BinOp::Shl | BinOp::LShr
                            | BinOp::AShr => ScalarPtrCause::BitMask,
                            _ if op_is_ptr(lhs) || op_is_ptr(rhs) => ScalarPtrCause::PtrArith,
                            _ => ScalarPtrCause::IntArith,
                        },
                        RValue::Cmp { .. } => ScalarPtrCause::IntArith,
                        RValue::Select { then_val, else_val, .. } => {
                            if op_is_ptr(then_val) || op_is_ptr(else_val) {
                                ScalarPtrCause::PtrArith
                            } else {
                                ScalarPtrCause::IntArith
                            }
                        }
                    };
                    (*dst, c)
                }
                _ => continue,
            };
            cause.insert(dst, c);
        }
    }

    // Second pass: rewrite every `Copy` to the cause at its chain root, following
    // `copy_of` exhaustively (depth-guarded). A chain rooting in a pointer-typed
    // register is `PtrRoot` (the copy erased the pointer type — provenance existed);
    // one rooting in an unclassifiable def (intrinsic/asm) or past the bound is
    // `Other`. No `Copy` survives into the result, so nothing is left at a
    // not-resolved-to-root catch-all.
    let copiers: Vec<RegId> = copy_of.keys().copied().collect();
    for start in copiers {
        let mut cur = start;
        let mut resolved = ScalarPtrCause::Other;
        for _ in 0..1024 {
            let Some(&src) = copy_of.get(&cur) else {
                // `cur` is the root (not a tracked copy): its own cause, or PtrRoot
                // if it is a pointer-typed value whose type the copy erased.
                resolved = match cause.get(&cur) {
                    Some(&ScalarPtrCause::Copy) | None if is_ptr.get(&cur) == Some(&true) => {
                        ScalarPtrCause::PtrRoot
                    }
                    Some(&ScalarPtrCause::Copy) | None => ScalarPtrCause::Other,
                    Some(&c) => c,
                };
                break;
            };
            if is_ptr.get(&src) == Some(&true) {
                resolved = ScalarPtrCause::PtrRoot; // provenance existed at the root
                break;
            }
            match cause.get(&src) {
                Some(&ScalarPtrCause::Copy) | None => cur = src, // keep following
                Some(&c) => {
                    resolved = c;
                    break;
                }
            }
        }
        cause.insert(start, resolved);
    }
    cause
}

impl POrigin {
    /// The residual reason string (the bucket key the sweep aggregates on).
    fn residual(self) -> &'static str {
        match self {
            POrigin::Param => "pointer provenance is not tracked: uncontracted pointer parameter",
            POrigin::Call => "pointer provenance is not tracked: opaque call result (no return summary)",
            POrigin::Load => "pointer provenance is not tracked: loaded value (no store-load provenance)",
            POrigin::IntToPtr => "pointer provenance is not tracked: int-to-pointer cast",
            POrigin::Loop => "pointer provenance is not tracked: loop-havocked pointer",
            POrigin::SelectJoin => "pointer provenance is not tracked: select/PHI join of differing provenance",
            POrigin::RegionDrop => "pointer provenance is not tracked: region dropped at path merge",
            POrigin::PhiFallback => "pointer provenance is not tracked: PHI fallback (no incoming arg)",
            POrigin::ScalarAsPtr(cause) => cause.residual(),
        }
    }
}

impl Prov {
    /// Residual reason for a `requires known provenance` obligation, naming the
    /// origin when known so the bucket splits by sub-case.
    fn provenance_residual(&self) -> &'static str {
        match self {
            // A null (or integer-derived) pointer reaching a provenance check.
            Prov::Null => "pointer provenance is not tracked: null or integer-derived pointer",
            Prov::Unknown(o, _) => o.residual(),
            // Unreachable at the emission sites (they fire on the non-Region else),
            // but a total function is cheaper to keep correct than a panic.
            Prov::Region(_) | Prov::Select { .. } => "pointer provenance is not tracked",
        }
    }
}

// Provenance equality is purely structural over the *kind*: two opaque pointers
// are interchangeable regardless of *why* they are opaque, so the diagnostic
// `POrigin` is deliberately excluded. This keeps `select`/merge behaviour (and
// every verdict) byte-identical to before the origin tag was added.
impl PartialEq for Prov {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Prov::Null, Prov::Null) => true,
            (Prov::Region(a), Prov::Region(b)) => a == b,
            (Prov::Unknown(..), Prov::Unknown(..)) => true,
            (
                Prov::Select { cond: c1, then_ptr: t1, else_ptr: e1 },
                Prov::Select { cond: c2, then_ptr: t2, else_ptr: e2 },
            ) => c1 == c2 && t1 == t2 && e1 == e2,
            _ => false,
        }
    }
}
impl Eq for Prov {}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SymPointer {
    prov: Prov,
    offset: ExprId,
    align: u64,
}

#[derive(Debug, Clone)]
struct SymRegion {
    kind: RegionKind,
    size: ExprId,
    state: LifetimeState,
    perms: Permissions,
    /// If this region models a caller-guaranteed pointer parameter, the named
    /// assumption its validity rests on (`param-contracts` / `slice-abi`);
    /// `None` for a freshly-allocated region (which rests on `alloc-succeeds`).
    contract: Option<&'static str>,
    /// `Some(fact)` when the byte size is known not to wrap (`fact` is the
    /// `count <= isize::MAX/stride` premise, trivially `true` for a concrete
    /// size). Then a memory-OOB obligation over the region is **refutable** with
    /// a faithful witness, with `fact` added to the refutation query only (not to
    /// the proving assumptions, to keep proofs cheap). `None` ⇒ not refutable.
    size_nowrap: Option<ExprId>,
    /// `Some(elem_bytes)` if the region is **sentinel-terminated**: a zero element
    /// of that width lies before its end. A sequential `while (p[n] != 0)` scan
    /// over it is then bounded (it must stop at the sentinel), which lets a
    /// `strlen`-shaped loop be proved. `None` for an ordinary region.
    sentinel: Option<u64>,
    /// `true` if the region has been filled with untrusted **user data** (via a
    /// `copy_from_user`-style `MemIntrinsic::UserFill`). A value later loaded from
    /// it is a *genuine adversarial input* — refutable like a parameter — so a
    /// length read back from a user-copied struct can drive an out-of-bounds FAIL.
    user_controlled: bool,
    /// `true` if this region models a raw pointer only **assumed** valid under the
    /// `--assume-valid-params` opt-in (a `RefWitness { assumed }`), so its byte size
    /// is a caller-supplied *guess* (e.g. from DWARF), not a proven allocation bound.
    /// A constant-offset "OOB" against such a region — the pervasive `container_of`
    /// backward step, or a fixed field past the guessed size — is an artifact of the
    /// guess, not a real bug: refuting it would be a false FAIL. Only an OOB the code
    /// drives with a *genuine input* offset is reported (see `check_access`).
    assumed: bool,
    /// The region's **provenance labels** (interned ids), set by [`Inst::ProvLabel`] and
    /// accumulated by [`Inst::ProvPropagate`] (a container unions in each element's labels).
    /// Empty = unlabelled, which grants every capability (the sound default). An
    /// [`Inst::CapRequire`] refutes iff **some** label in the set provably lacks the cap —
    /// a container is only as capable as its least-capable member.
    prov_labels: HashSet<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SymValue {
    Scalar(ExprId),
    Ptr(SymPointer),
}

/// Captured data for asserting a pointer equality-exit induction's offset bound
/// (`iter != end`), taken before the loop header havoc clobbers `iter`.
struct PtrIndCapture {
    /// The induction pointer register (a header block-parameter).
    reg: RegId,
    /// The allocation `iter` walks within.
    region: usize,
    /// `iter`'s start offset (its preheader value's offset).
    b0: ExprId,
    /// `iter`'s start alignment.
    align: u64,
    /// The end pointer's offset within the same allocation.
    end_off: ExprId,
    /// The allocation's byte size.
    size: ExprId,
    /// The per-iteration byte stride (`elem size × element step`).
    stride_bytes: u64,
    /// `true` for the rotated form (load precedes the `next == end` check): the
    /// bound is `o + stride ≤ end_off` and its base case is proved from the
    /// preheader guard. `false` for the header-test form (`o ≤ end_off`).
    bottom_test: bool,
}

/// Where a loaded value comes from, per the store log (most-recent-first scan).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LoadOrigin {
    /// A prior store definitely determines the value (`Must` alias).
    Stored,
    /// A prior store *might* determine it (`May` alias) — value is unknown.
    Uncertain,
    /// No store reaches this location (every record is `No` alias): the bytes
    /// are whatever the region held at allocation. For a freshly-allocated
    /// region that is *uninitialized* memory.
    Unwritten,
}

/// A recorded store: "`size` bytes equal to `value` were written through
/// `target`". Most-recent-last.
#[derive(Clone, PartialEq, Eq)]
struct StoreRecord {
    target: SymPointer,
    value: SymValue,
    size: u64,
}

#[derive(Clone)]
struct PathState {
    env: HashMap<RegId, SymValue>,
    regions: Vec<SymRegion>,
    pathcond: Vec<ExprId>,
    facts: Vec<ExprId>,
    /// The symbolic store, in program order (for read-your-writes).
    heap: Vec<StoreRecord>,
    /// **Read-consistency** cache for *unwritten* locations: the value first materialized
    /// for a load from `(region, concrete byte offset, access width)` that no store aliases,
    /// so two reads of the same never-written field agree (the correct memory semantics —
    /// unwritten memory holds one fixed unknown value). Populated only for concrete offsets;
    /// consulted only in `load_value`'s unwritten fallback (a store always wins first).
    /// Cleared on every heap havoc (an opaque call may have written the location), so it can
    /// never return a stale post-write value — sound.
    unwritten_reads: HashMap<(usize, u128, u32), SymValue>,
    /// **Materialised-field region identity**: the region a `RefWitness` materialised for a
    /// raw-pointer field at `(base region, concrete offset)`, so two loads of the *same* field
    /// yield the *same* tracked region (an in-place `src == dst` through field loads is then
    /// recognised). Keyed by the base's identity — a materialised region or an opaque
    /// provenance id — and the field offset. Cleared on every heap havoc (a call may have
    /// reassigned the field) — sound.
    ref_regions: HashMap<(RefBase, u128), usize>,
    /// Provenance labels attached to an **opaque pointer** by its provenance identity
    /// (`Prov::Unknown`'s id — see there), which flows through `gep`/copy so a field address
    /// off a labelled object carries the object's labels. A raw-pointer parameter is opaque
    /// provenance, not a region, so it has no `prov_labels` of its own. Decoupled from the
    /// region/safety model entirely — an opaque label affects **only** the provenance checks
    /// (`CapRequire`/`CapRequireIfAlias`), never null-deref, bounds, liveness, or permissions —
    /// so it cannot introduce a false PASS. Persistent (a fact about the SSA value, not memory),
    /// so not cleared on havoc.
    opaque_labels: HashMap<u32, HashSet<u32>>,
    /// **Scalar taint labels** per SSA register (the directional taint lattice, G6-family J/F/D):
    /// interned taint-label ids a register's value carries, sourced by a `taint-source` contract
    /// or a load from a labelled region, propagated through arithmetic/casts, checked by a
    /// `taint-sink` (`Inst::TaintCheck`) and cleared by a `taint-sanitize`. Pointer/region taint
    /// reuses `prov_labels`; this map is the scalar complement. Meet-joined at merges (a value is
    /// "definitely tainted" only if tainted on every incoming path — no false FAIL under a
    /// partly-tainted phi). A fact about the SSA value, not memory (not cleared on havoc).
    tainted: HashMap<RegId, HashSet<u32>>,
    /// **Typestate per resource per protocol** (the generalised protocol tracker, roadmap #4):
    /// `(resource identity, protocol id) → current state id`. Advanced by `Inst::TypestateSet`
    /// transitions and checked by `Inst::TypestateRequire` obligations (both contract-driven).
    /// Generalises the lifetime/lock/taint typestates to any contract-defined finite-state
    /// protocol. Meet-joined at merges (a resource is "definitely in state S" only if it is S
    /// on every incoming path — so a require refutes with no false FAIL under a partial state).
    /// A fact about the resource, not memory (not cleared on havoc).
    typestates: HashMap<(ResKey, u32), u32>,
    /// **Reference counts per resource per protocol** (G8): `(resource, protocol) → count`.
    /// Raised by an `inc` and lowered by a `dec` (`Inst::Refcount`); a `dec` below zero is an
    /// underflow (premature free → UAF). Meet-joined at merges (kept only if all incoming
    /// paths agree on the count — so an underflow refutes only when definite; no false FAIL).
    refcounts: HashMap<(ResKey, u32), i64>,
    /// **Resolved function-pointer values**: a register holding a function address
    /// devirtualised from a constant ops-struct load (see `global_fnptrs`) maps to
    /// its target `FuncId`, so an indirect call through that register is analysed
    /// with the callee's summary rather than an opaque havoc. Persistent (a fact
    /// about the SSA value, not memory).
    fn_ptrs: HashMap<RegId, FuncId>,
    /// **Locks held** on this path, by the identity of the lock pointer's base object
    /// (`spin_lock`/`mutex_lock`/… acquired and not yet released). Re-acquiring a base
    /// already here is an AA self-deadlock. Structural per-path state (not memory), so
    /// not cleared on a heap havoc; joined by meet at control-flow merges.
    locks_held: HashSet<RefBase>,
    /// **Spinning locks held** on this path (the atomic-context subset of `locks_held`:
    /// `spin_lock`/`read_lock`/`write_lock` families, not sleepable `mutex`/`down`). A
    /// blocking call while this is non-empty is a sleep-in-atomic bug. Meet-joined at merges
    /// like `locks_held`, and conservatively dropped when the lock base is passed to any call.
    spin_held: HashSet<RefBase>,
    /// **Lock class held per lock base** on this path — the static cross-function name
    /// (see `lockclass`) of every lock currently held, keyed by its runtime base. Used to
    /// emit lock-order edges (held-class → newly-acquired-class) for ABBA cycle detection.
    /// Meet-joined at merges (only a lock held on every incoming path stays), and dropped
    /// alongside `locks_held`/`spin_held` when the base is passed to any call.
    held_classes: HashMap<RefBase, String>,
    /// **User-memory addresses fetched** on this path, by `(source base, concrete byte
    /// offset)` — one entry per `copy_from_user`/`get_user` from a concrete user address.
    /// Re-fetching an address already here is a **double-fetch** (a TOCTOU on adversary-
    /// controlled user memory). Structural per-path state (not cleared on a heap havoc);
    /// joined by meet at merges, so a re-fetch is flagged only when the first fetch is
    /// definite on every incoming path — sound (a partial fetch never fabricates one).
    user_fetches: HashSet<(RefBase, u128)>,
    /// **Bases freed by an attributed freeing call** (`Summary.frees_arg`) on this path —
    /// so a second freeing-wrapper call on the same pointer is a definite double-free
    /// (which the coarse `frees` region havoc cannot attribute). Joined by meet at merges
    /// (only a base freed on *every* incoming path counts). Structural, not memory.
    freed_bases: HashSet<RefBase>,
    /// Whether this path is *exact*: no over-approximation (loop-header havoc,
    /// opaque call, or non-determined load) has been introduced. A symbolic
    /// **refutation** (sound `FAIL` + counterexample) is only emitted on an
    /// exact path, where the path condition characterizes genuinely reachable
    /// states, so a violating model is a real execution. Proofs (`PASS`) do not
    /// need this — over-approximation is sound for proving.
    exact: bool,
}

/// One incoming control-flow edge into a block, queued during the reverse-
/// postorder walk: the predecessor's post-state, the edge's guard (the branch
/// condition under which it is taken; `None` for an unconditional `Br`), and the
/// block-parameter arguments it supplies.
struct EdgeState {
    pred_state: PathState,
    guard: Option<ExprId>,
    args: Vec<Operand>,
}

/// Per-obligation aggregation across paths.
struct MemAgg {
    all_proven: bool,
    /// A counterexample from any path that definitely violated the obligation.
    refutation: Option<Model>,
    predicate: String,
    residual: String,
}

/// Per scalar-check aggregation across paths.
struct ScalarAgg {
    /// Proved on every path so far.
    all_proven: bool,
    /// A counterexample from any path that definitely violated the check.
    refutation: Option<Model>,
}

/// The outcome of deciding a safety goal on one path.
enum Decision {
    /// Proved to hold.
    Proven,
    /// Neither proved nor (soundly) refuted.
    Unknown,
    /// Violated on this exact path, witnessed by the model.
    Refuted(Model),
}

/// How aggressively a goal may be refuted (see [`Explorer::try_refute`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RefuteMode {
    /// Never refute (prove-only).
    Off,
    /// Refute only a goal that is *always* violated on the path.
    Definite,
    /// Refute a goal violated by *some* reaching input (the operation executes,
    /// so any such input is a real runtime violation).
    Possible,
}

struct Explorer<'f> {
    ctx: ExprCtx,
    fresh: u32,
    /// A monotone counter for opaque-pointer provenance ids (see `Prov::Unknown`); separate
    /// from `fresh` so symbol numbering — and hence witnesses/determinism — is unchanged.
    prov_ids: u32,
    /// Bug-finding mode: relax the memory-refutation gate so a spatial violation
    /// whose offset/size depend only on genuine inputs (parameters) is reported
    /// even on a globally-inexact path (e.g. after an init loop). Off by default
    /// (verification stays strict — refute only on an exact path). See `decide`.
    bug_finding: bool,
    /// Whether this function is exported (externally reachable). In bug-finding mode
    /// only an exported function's `arg…` parameters count as genuine adversarial
    /// inputs (see `goal_is_genuine`); an internal function's are caller-constrained.
    exported: bool,
    /// Honour `RefWitness { assumed }` (a raw pointer field valid under the opt-in).
    assume_valid_params: bool,
    visits: usize,
    truncated: bool,
    limits: ExecLimits,
    /// When exploration must stop (from `limits.time_budget`); `None` ⇒ no clock.
    deadline: Option<std::time::Instant>,
    /// Scalar `SafetyCheck` aggregation, keyed by (block, idx).
    scalar: HashMap<(BlockId, usize), ScalarAgg>,
    mem: HashMap<(BlockId, usize, SafetyProperty), MemAgg>,
    assumptions: HashSet<&'static str>,
    /// Sound interval invariants (the source of loop invariants).
    analysis: IntervalAnalysis,
    /// Relational (zone) invariants — difference constraints between registers
    /// that the per-register interval domain cannot express.
    zones: ZoneAnalysis,
    /// Equality-exit induction variables (`while i != n`), whose `start ≤ i ≤ n`
    /// bound the interval domain cannot derive from a `!=` guard.
    inductions: InductionAnalysis,
    dominators: Dominators,
    /// Block ids that are loop headers.
    headers: HashSet<BlockId>,
    /// Per loop header: registers the loop body may redefine (havoc set).
    loop_modified: HashMap<BlockId, Vec<RegId>>,
    /// Per loop header: whether the loop body may free memory.
    loop_frees: HashMap<BlockId, bool>,
    /// Per loop header: the blocks forming the loop body (for pattern analyses).
    loop_bodies: HashMap<BlockId, Vec<BlockId>>,
    /// Interprocedural summaries, by callee id (empty = havoc all calls).
    summaries: HashMap<FuncId, Summary>,
    /// Whole-program summaries by callee **name**, for resolving a cross-file
    /// `Callee::Symbol(name)` call that has no in-module id — so a caller sees a
    /// remote callee's effects (writes/frees/return) instead of an opaque havoc.
    /// Empty in the ordinary per-module path (every such call stays opaque).
    name_summaries: HashMap<String, Summary>,
    /// The provenance lattice (label id → granted capability ids), from the module's
    /// contracts. An [`Inst::CapRequire`] checks it; a label absent here grants all
    /// capabilities (sound default). Empty ⇒ the capability mechanism is inert.
    prov_grants: HashMap<u32, HashSet<u32>>,
    /// A deterministic synthetic field layout per region: the byte offset assigned
    /// to each `(region, field index)` the first time it is accessed, and the
    /// running frontier per region. Fields are packed sequentially so distinct
    /// fields occupy disjoint ranges (an exact field-sensitive heap), while the
    /// same field always reuses its offset (so a store then load round-trips). The
    /// real layout is irrelevant — only `offset + size <= region size` is asserted.
    field_offsets: HashMap<(usize, u32), u64>,
    field_frontier: HashMap<usize, u64>,
    /// Per-register classification of how a scalar-used-as-pointer was computed
    /// (diagnostic; tags the `ScalarAsPtr` provenance residual at scale).
    scalar_ptr_cause: HashMap<RegId, ScalarPtrCause>,
    /// Referenced global definitions: symbol name → (region id, alignment).
    /// The regions are created once at state initialization (sorted by name for
    /// determinism) and are `Live` forever — globals are never freed.
    global_rids: HashMap<String, (usize, u64)>,
    /// **Devirtualisation tables** keyed by the *region id* of a constant
    /// ops-struct/vtable global: byte offset → target function. A load of a
    /// pointer field at a matching offset resolves the loaded function pointer,
    /// so an indirect call through it uses the callee's summary (see `step_call`).
    global_fnptrs: HashMap<usize, HashMap<u64, FuncId>>,
    /// **Prove-result cache** over the function's single `ExprCtx`: a memo from
    /// `(assumptions, goal)` to the proof method (or `None`). Sound because the
    /// `ExprCtx` is append-only — an `ExprId` denotes the same formula for the
    /// whole discharge — so `prove_implies_method` is a pure function of the key.
    /// Repeated identical bounds/alias queries (loops, many accesses under one
    /// path condition) then skip re-bit-blasting. The `linear-no-overflow` side
    /// effect is re-applied on a hit.
    prove_cache: HashMap<(Box<[ExprId]>, ExprId), Option<ProofMethod>>,
    /// Static **lock-class map** for this function: register → the cross-function name
    /// of the lock it designates (see `lockclass`). Consulted at each lock-acquire to
    /// name the acquired lock for ABBA lock-order edges.
    lock_classes: HashMap<RegId, String>,
    /// **Lock-order edges** collected on this function: `(held-class, then-acquired-class)`
    /// pairs observed on some path. Streamed out for whole-program cycle detection (an
    /// A→B here plus a B→A elsewhere is a potential ABBA deadlock).
    lock_edges: HashSet<(String, String)>,
    /// **Shared-memory access records** for the lockset data-race check (G1): per access to a
    /// *shareable* location (a global, or an object reached through a parameter — not a stack
    /// local), the location's class, whether it is a write, and the set of lock *classes* held
    /// at the access. Streamed whole-program: a location whose accesses share no common lock,
    /// include a write, and span ≥2 functions is a candidate race (the Eraser lockset signal).
    /// `(access-class, is_write, sorted lock-classes held)`.
    race_accesses: HashSet<(String, bool, Vec<String>)>,
    /// **Ordered event trace** for the two-thread interleaving check (subsystem 4): the
    /// sequence of lock acquires/releases and shared reads/writes in execution order, as
    /// `(kind, class)` with kind `0`=acquire, `1`=release, `2`=read, `3`=write. Consumed by
    /// `csolver_verifier::interleave` to find atomicity violations (a split-critical-section
    /// read-modify-write a foreign write can interrupt) with an interleaving witness.
    race_trace: Vec<(u8, String)>,
    f: &'f Function,
}

impl Explorer<'_> {
    fn fresh_scalar(&mut self, width: u32) -> ExprId {
        let name = format!("?{}", self.fresh);
        self.fresh += 1;
        self.ctx.symbol(name, width)
    }

    /// The synthetic byte offset of `(region, field)`: cached on first access, else
    /// the region's current frontier, which is then advanced by the field size so
    /// the next new field lands in a disjoint range. Deterministic across paths
    /// (the executor processes each block once), so merges stay consistent.
    fn field_offset(&mut self, rid: usize, field: u32, size: u64) -> u64 {
        if let Some(&o) = self.field_offsets.get(&(rid, field)) {
            return o;
        }
        let frontier = self.field_frontier.entry(rid).or_insert(0);
        let off = *frontier;
        *frontier += size.max(1);
        self.field_offsets.insert((rid, field), off);
        off
    }

    fn fresh_value(&mut self, ty: &Type, origin: POrigin) -> SymValue {
        if ty.is_ptr() {
            // Mint a fresh provenance identity for this opaque pointer (see `Prov::Unknown`).
            // A separate counter keeps symbol numbering (and thus witnesses / determinism)
            // byte-identical to before the id existed.
            let id = self.prov_ids;
            self.prov_ids += 1;
            SymValue::Ptr(SymPointer {
                prov: Prov::Unknown(origin, Some(id)),
                offset: self.ctx.int(PTR_WIDTH, 0),
                align: 1,
            })
        } else {
            SymValue::Scalar(self.fresh_scalar(type_width(ty)))
        }
    }

    /// Drive the analysis over the (back-edge-cut) CFG in **reverse postorder**,
    /// processing **each block exactly once**. Every non-back-edge predecessor is
    /// processed before a block, so its incoming edge-states are all available and
    /// **merged** into one entry state (see [`Explorer::merge_edges`]). This
    /// collapses the per-path explosion of the old recursive walk: a join with N
    /// predecessors is analysed once instead of once per path, so wide CFGs no
    /// longer blow up the path count (or trip the visit budget into truncation).
    fn run_merged(&mut self, entry_state: PathState) {
        let rpo: Vec<BlockId> = {
            let cfg = self.analysis.cfg();
            cfg.reverse_postorder().into_iter().map(|n| cfg.block_id(n)).collect()
        };
        let mut incoming: HashMap<BlockId, Vec<EdgeState>> = HashMap::new();
        incoming.insert(
            self.f.entry,
            vec![EdgeState { pred_state: entry_state, guard: None, args: Vec::new() }],
        );

        for block in rpo {
            if self.truncated {
                return;
            }
            let Some(edges) = incoming.remove(&block) else {
                continue; // unreachable in the DAG (or all incoming edges pruned)
            };
            if edges.is_empty() {
                continue;
            }
            self.visits += 1;
            // Truncate on the visit budget, or on the wall-clock budget (checked
            // here, between block visits, so the overrun is bounded by one block's
            // work plus the 250 ms per-solve valve). Both set `truncated`, which
            // discards every decision → non-`PASS`. See `ExecLimits::time_budget`.
            if self.visits > self.limits.max_visits
                || self.deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
            {
                self.truncated = true;
                return;
            }

            let mut state = self.merge_edges(block, edges);
            // At a loop header, over-approximate every iteration by replacing the
            // loop-carried parameters with fresh symbols constrained by the sound
            // interval invariant.
            if self.headers.contains(&block) {
                self.havoc_header(block, &mut state);
            }
            let Some(b) = self.f.block(block) else {
                continue;
            };
            for (idx, inst) in b.insts.iter().enumerate() {
                self.step(block, idx, inst, &mut state);
            }
            self.propagate_edges(block, b, state, &mut incoming);
        }
    }

    /// Push the out-edges of `block` (with their guards / block-parameter args) to
    /// the successors' incoming sets. Back-edges are cut; a branch whose guard is
    /// bit-precisely unreachable is pruned (see [`Explorer::branch_infeasible`]).
    fn propagate_edges(
        &mut self,
        block: BlockId,
        b: &BasicBlock,
        state: PathState,
        incoming: &mut HashMap<BlockId, Vec<EdgeState>>,
    ) {
        match &b.term {
            Terminator::Return(_) | Terminator::Unreachable => {}
            Terminator::Br { target, args } => {
                if !self.is_back_edge(block, *target) {
                    incoming.entry(*target).or_default().push(EdgeState {
                        pred_state: state,
                        guard: None,
                        args: args.clone(),
                    });
                }
            }
            Terminator::CondBr { cond, then_blk, then_args, else_blk, else_args } => {
                let mut ce = self.eval_scalar(cond, &state);
                // Coerce a non-boolean condition to `c != 0` (LLVM truthiness). A wider
                // value can reach here — an `i1` register that holds a widened expression,
                // or a loop-havoc'd condition — and using it directly as a boolean guard is
                // unencodable, which spuriously makes the whole path condition UNSAT (so a
                // real violation on that path is recorded UNKNOWN instead of refuted).
                if self.ctx.width(ce) != 1 {
                    let zero = self.ctx.int(self.ctx.width(ce), 0);
                    ce = self.ctx.cmp(SCmp::Ne, ce, zero);
                }
                let nce = self.ctx.not(ce);
                if !self.is_back_edge(block, *then_blk) && !self.branch_infeasible(ce, &state) {
                    incoming.entry(*then_blk).or_default().push(EdgeState {
                        pred_state: state.clone(),
                        guard: Some(ce),
                        args: then_args.clone(),
                    });
                }
                if !self.is_back_edge(block, *else_blk) && !self.branch_infeasible(nce, &state) {
                    incoming.entry(*else_blk).or_default().push(EdgeState {
                        pred_state: state,
                        guard: Some(nce),
                        args: else_args.clone(),
                    });
                }
            }
            Terminator::Switch { value, cases, default } => {
                let ve = self.eval_scalar(value, &state);
                for (cv, target) in cases {
                    if self.is_back_edge(block, *target) {
                        continue;
                    }
                    let k = self.ctx.constant(*cv);
                    let eq = self.ctx.cmp(SCmp::Eq, ve, k);
                    if self.branch_infeasible(eq, &state) {
                        continue;
                    }
                    incoming.entry(*target).or_default().push(EdgeState {
                        pred_state: state.clone(),
                        guard: Some(eq),
                        args: Vec::new(),
                    });
                }
                if !self.is_back_edge(block, *default) {
                    // The default edge carries `value != k` for every case.
                    // Omitting it was sound for proofs (over-approximation) but
                    // let a *refutation* on the default path pick a case value —
                    // an infeasible witness, i.e. a false FAIL (seen on rustc's
                    // jump-threaded slice-length switches).
                    let ne: Vec<ExprId> = cases
                        .iter()
                        .map(|(cv, _)| {
                            let k = self.ctx.constant(*cv);
                            let eq = self.ctx.cmp(SCmp::Eq, ve, k);
                            self.ctx.not(eq)
                        })
                        .collect();
                    let guard = self.ctx.and(ne);
                    if !self.branch_infeasible(guard, &state) {
                        incoming.entry(*default).or_default().push(EdgeState {
                            pred_state: state,
                            guard: Some(guard),
                            args: Vec::new(),
                        });
                    }
                }
            }
        }
    }

    /// Merge the incoming edge-states of a block into one entry state. A single
    /// predecessor is applied precisely (its guard and block-param args); multiple
    /// predecessors are joined by [`Explorer::merge_multi`].
    fn merge_edges(&mut self, block: BlockId, mut edges: Vec<EdgeState>) -> PathState {
        if edges.len() == 1 {
            let e = edges.swap_remove(0);
            let mut s = e.pred_state;
            if let Some(g) = e.guard {
                s.pathcond.push(g);
            }
            self.bind_params_into(block, &e.args, &mut s);
            return s;
        }
        self.merge_multi(block, edges)
    }

    /// Bind a block's parameters from the incoming `args`, evaluated in `s`.
    fn bind_params_into(&mut self, block: BlockId, args: &[Operand], s: &mut PathState) {
        let params = self.f.block(block).map(|b| b.params.clone()).unwrap_or_default();
        let vals: Vec<SymValue> = (0..params.len())
            .map(|j| match args.get(j) {
                Some(a) => self.eval_value(a, s),
                None => self.fresh_value(&params[j].1, POrigin::PhiFallback),
            })
            .collect();
        for ((preg, _), v) in params.iter().zip(vals) {
            s.env.insert(*preg, v);
        }
    }

    /// Join several incoming edge-states. Block parameters (PHIs) are merged with
    /// an `ITE` keyed on each edge's discriminating condition (its full path
    /// condition); the rest is over-approximated by [`Explorer::merge_core`].
    fn merge_multi(&mut self, block: BlockId, edges: Vec<EdgeState>) -> PathState {
        // Each edge's discriminator: the conjunction of its path condition (plus
        // its branch guard) — the condition under which control arrives by it.
        let discs: Vec<ExprId> = edges
            .iter()
            .map(|e| {
                let mut conds = e.pred_state.pathcond.clone();
                if let Some(g) = e.guard {
                    conds.push(g);
                }
                self.ctx.and(conds)
            })
            .collect();

        let mut merged = self.merge_core(&edges);
        merged.heap = self.merge_heap(&edges, &discs, merged.regions.len());

        let params = self.f.block(block).map(|b| b.params.clone()).unwrap_or_default();
        for (j, (preg, pty)) in params.iter().enumerate() {
            let vals: Vec<(ExprId, SymValue)> = edges
                .iter()
                .zip(&discs)
                .map(|(e, &d)| {
                    let v = match e.args.get(j) {
                        Some(a) => self.eval_value(a, &e.pred_state),
                        None => self.fresh_value(pty, POrigin::PhiFallback),
                    };
                    (d, v)
                })
                .collect();
            let mv = self.merge_values(&vals, pty);
            merged.env.insert(*preg, mv);
        }
        merged
    }

    /// The merged heap. A store to an address survives only if that address has a
    /// *last* store on **every** incoming edge (else it is ambiguous — dropped).
    /// Identical values are kept as-is; differing values are **joined** into a
    /// `select` guarded by the edge discriminators (the same construction as a
    /// PHI), so e.g. a `va_list` cursor advanced differently per branch stays a
    /// known — if multi-region — pointer instead of being forgotten. Records whose
    /// address or joined value points into a dropped region are sanitized out.
    fn merge_heap(&mut self, edges: &[EdgeState], discs: &[ExprId], rcount: usize) -> Vec<StoreRecord> {
        let region_kept = |p: &Prov| !matches!(p, Prov::Region(rid) if *rid >= rcount);
        let same_addr = |a: &SymPointer, b: &SymPointer| a.prov == b.prov && a.offset == b.offset;
        let last_for = |heap: &[StoreRecord], t: &SymPointer| -> Option<StoreRecord> {
            heap.iter().rev().find(|r| same_addr(&r.target, t)).cloned()
        };
        let ptr_ty = Type::Ptr { pointee: Box::new(Type::int(8)) };

        // Candidate addresses: the last store to each distinct target on edge 0.
        let mut done: Vec<SymPointer> = Vec::new();
        let mut out: Vec<StoreRecord> = Vec::new();
        for rec in edges[0].pred_state.heap.iter().rev() {
            let t = rec.target.clone();
            if done.iter().any(|d| same_addr(d, &t)) {
                continue;
            }
            done.push(t.clone());
            if !region_kept(&t.prov) {
                continue;
            }
            // The last store to `t` on every edge, with a consistent size.
            let mut per_edge: Vec<(ExprId, SymValue)> = Vec::with_capacity(edges.len());
            let mut ok = true;
            for (e, &d) in edges.iter().zip(discs) {
                match last_for(&e.pred_state.heap, &t) {
                    Some(r) if r.size == rec.size => per_edge.push((d, r.value)),
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                continue;
            }
            let value = self.merge_values(&per_edge, &ptr_ty);
            // Drop if the joined value points into a region the merge dropped.
            if let SymValue::Ptr(vp) = &value {
                if !self.pointer_regions_kept(&vp.prov, rcount) {
                    continue;
                }
            }
            out.push(StoreRecord { target: t, value, size: rec.size });
        }
        out
    }

    /// Whether every region a (possibly `Select`) provenance can denote survives a
    /// merge that kept `rcount` regions.
    fn pointer_regions_kept(&self, prov: &Prov, rcount: usize) -> bool {
        match prov {
            Prov::Region(rid) => *rid < rcount,
            Prov::Select { then_ptr, else_ptr, .. } => {
                self.pointer_regions_kept(&then_ptr.prov, rcount)
                    && self.pointer_regions_kept(&else_ptr.prov, rcount)
            }
            _ => true,
        }
    }

    /// The non-parameter part of a multi-predecessor merge: a sound
    /// over-approximation of all incoming states. Regions keep the common prefix
    /// (identical byte size) with a conservative lifetime (`Live` only if live on
    /// every edge); the register environment is taken from the first edge (in SSA
    /// the registers live past a join are defined before the split, hence equal),
    /// sanitizing any pointer into a dropped region; the path condition is the
    /// longest common prefix and the facts their intersection (both sound,
    /// weaker); the heap is **intersected** — a store identical on every incoming
    /// edge definitely holds after the merge, so it is kept (a value written before
    /// the branch and read after it, e.g. a `va_list`'s fields); anything the paths
    /// disagree on is dropped. The path is no longer `exact`.
    fn merge_core(&self, edges: &[EdgeState]) -> PathState {
        let first = &edges[0].pred_state;

        let mut regions = Vec::new();
        'prefix: for i in 0..first.regions.len() {
            let size = first.regions[i].size;
            for e in edges {
                match e.pred_state.regions.get(i) {
                    Some(r) if r.size == size => {}
                    _ => break 'prefix,
                }
            }
            let live_all = edges
                .iter()
                .all(|e| e.pred_state.regions[i].state == LifetimeState::Live);
            let mut r = first.regions[i].clone();
            r.state = if live_all { LifetimeState::Live } else { LifetimeState::Freed };
            // Intersect provenance labels across edges: a label survives the join only if it
            // holds on EVERY incoming path (the meet), so it is never attributed to a path that
            // did not set it — sound (no false FAIL); an entry-set label (on all paths) survives.
            r.prov_labels = first.regions[i]
                .prov_labels
                .iter()
                .copied()
                .filter(|l| edges.iter().all(|e| e.pred_state.regions[i].prov_labels.contains(l)))
                .collect();
            regions.push(r);
        }
        let rcount = regions.len();

        let mut env = first.env.clone();
        for v in env.values_mut() {
            if let SymValue::Ptr(p) = v {
                if let Prov::Region(rid) = p.prov {
                    if rid >= rcount {
                        p.prov = Prov::Unknown(POrigin::RegionDrop, None);
                    }
                }
            }
        }

        let mut pathcond = Vec::new();
        for k in 0..first.pathcond.len() {
            let c = first.pathcond[k];
            if edges.iter().all(|e| e.pred_state.pathcond.get(k) == Some(&c)) {
                pathcond.push(c);
            } else {
                break;
            }
        }

        let facts: Vec<ExprId> = first
            .facts
            .iter()
            .copied()
            .filter(|f| edges.iter().all(|e| e.pred_state.facts.contains(f)))
            .collect();

        // Opaque-pointer labels survive the join by the same **meet** as regions/facts: an id
        // keeps a label only if every incoming edge has it — sound (never attributed to a path
        // that did not set it), and an entry-seed (set before any branch) survives on all paths.
        let opaque_labels: HashMap<u32, HashSet<u32>> = first
            .opaque_labels
            .iter()
            .filter_map(|(id, labels)| {
                let common: HashSet<u32> = labels
                    .iter()
                    .copied()
                    .filter(|l| {
                        edges
                            .iter()
                            .all(|e| e.pred_state.opaque_labels.get(id).is_some_and(|s| s.contains(l)))
                    })
                    .collect();
                (!common.is_empty()).then_some((*id, common))
            })
            .collect();

        // Scalar taint survives the join by the same **meet**: a register keeps a taint label
        // only if every incoming edge has it — so a sink refutes only on a *definitely*-tainted
        // value (no false FAIL under a partly-tainted phi). Under-taints (a value tainted on one
        // branch only is dropped) — sound, recall-only loss.
        let tainted: HashMap<RegId, HashSet<u32>> = first
            .tainted
            .iter()
            .filter_map(|(reg, labels)| {
                let common: HashSet<u32> = labels
                    .iter()
                    .copied()
                    .filter(|l| {
                        edges
                            .iter()
                            .all(|e| e.pred_state.tainted.get(reg).is_some_and(|s| s.contains(l)))
                    })
                    .collect();
                (!common.is_empty()).then_some((*reg, common))
            })
            .collect();

        // Typestate survives the join by the same **meet**: a `(resource, protocol)` keeps its
        // state only if every incoming edge agrees on the *same* state — so a require refutes
        // only on a resource *definitely* in the forbidden state (no false FAIL under a partial
        // state; a disagreement drops the entry, conservatively "unknown").
        let typestates: HashMap<(ResKey, u32), u32> = first
            .typestates
            .iter()
            .filter(|(k, st)| edges.iter().all(|e| e.pred_state.typestates.get(k) == Some(*st)))
            .map(|(k, st)| (*k, *st))
            .collect();
        // Refcounts survive the join by the same meet: keep a count only if every incoming
        // edge agrees, so an underflow refutes only when the count is definite.
        let refcounts: HashMap<(ResKey, u32), i64> = first
            .refcounts
            .iter()
            .filter(|(k, c)| edges.iter().all(|e| e.pred_state.refcounts.get(k) == Some(*c)))
            .map(|(k, c)| (*k, *c))
            .collect();

        // Resolved function-pointer identities survive the join by the same meet:
        // a register keeps its target only if every incoming edge resolved it to
        // the *same* function (an SSA value dominating the merge does; a phi does
        // not appear here). Sound — a disagreement drops back to opaque dispatch.
        let fn_ptrs: HashMap<RegId, FuncId> = first
            .fn_ptrs
            .iter()
            .filter(|(r, fid)| edges.iter().all(|e| e.pred_state.fn_ptrs.get(r) == Some(fid)))
            .map(|(r, fid)| (*r, *fid))
            .collect();

        // A lock counts as held after the join only if held on *every* incoming edge
        // (meet), so a subsequent re-acquire is flagged only when it is a definite
        // double-lock on all paths — sound (a partial hold never fabricates one).
        let locks_held: HashSet<RefBase> = first
            .locks_held
            .iter()
            .copied()
            .filter(|b| edges.iter().all(|e| e.pred_state.locks_held.contains(b)))
            .collect();
        let spin_held: HashSet<RefBase> = first
            .spin_held
            .iter()
            .copied()
            .filter(|b| edges.iter().all(|e| e.pred_state.spin_held.contains(b)))
            .collect();
        // Same meet for held lock classes: keep a base's class only if held (with the
        // same class) on every incoming path.
        let held_classes: HashMap<RefBase, String> = first
            .held_classes
            .iter()
            .filter(|(b, c)| edges.iter().all(|e| e.pred_state.held_classes.get(b) == Some(*c)))
            .map(|(b, c)| (*b, c.clone()))
            .collect();
        // Same meet for freed bases: a base counts as freed after the join only if it was
        // freed on every incoming path, so a re-free is flagged only when it is a definite
        // double-free on all paths.
        let freed_bases: HashSet<RefBase> = first
            .freed_bases
            .iter()
            .copied()
            .filter(|b| edges.iter().all(|e| e.pred_state.freed_bases.contains(b)))
            .collect();
        // Same meet for fetched user addresses: an address counts as fetched after the
        // join only if fetched on every incoming path, so a re-fetch is flagged as a
        // double-fetch only when it is definite on all paths.
        let user_fetches: HashSet<(RefBase, u128)> = first
            .user_fetches
            .iter()
            .copied()
            .filter(|k| edges.iter().all(|e| e.pred_state.user_fetches.contains(k)))
            .collect();

        // The heap is computed by `merge_multi` (it needs the edge discriminators
        // to *join* differing stores); leave it empty here.
        PathState {
            env,
            regions,
            pathcond,
            facts,
            heap: Vec::new(),
            unwritten_reads: HashMap::new(),
            ref_regions: HashMap::new(),
            opaque_labels,
            tainted,
            typestates,
            refcounts,
            fn_ptrs,
            locks_held,
            spin_held,
            held_classes,
            user_fetches,
            freed_bases,
            exact: false,
        }
    }

    /// Merge per-edge values into one, as a right-folded `ITE` over the edge
    /// discriminators (the last edge is the final `else`).
    fn merge_values(&mut self, vals: &[(ExprId, SymValue)], ty: &Type) -> SymValue {
        let Some((_, last)) = vals.last().cloned() else {
            return self.fresh_value(ty, POrigin::PhiFallback);
        };
        let mut acc = last;
        for (d, v) in vals[..vals.len() - 1].iter().rev() {
            acc = self.select(*d, v.clone(), acc, ty);
        }
        acc
    }

    /// `select(d, a, b)` = `if d then a else b`, structurally: `ITE` on scalars
    /// and on same-provenance pointer offsets; differing provenance degrades to an
    /// opaque pointer (sound over-approximation).
    fn select(&mut self, d: ExprId, a: SymValue, b: SymValue, ty: &Type) -> SymValue {
        match (a, b) {
            (SymValue::Scalar(ea), SymValue::Scalar(eb)) => SymValue::Scalar(self.ctx.ite(d, ea, eb)),
            (SymValue::Ptr(pa), SymValue::Ptr(pb)) if pa.prov == pb.prov => SymValue::Ptr(SymPointer {
                prov: pa.prov,
                offset: self.ctx.ite(d, pa.offset, pb.offset),
                align: gcd(pa.align, pb.align),
            }),
            // Two different regions: keep both as a `Select` join (bounded depth,
            // so a pathological chain of distinct selects degrades to opaque rather
            // than growing without limit). An access through it is proved for each
            // alternative under its guard (see `check_access`).
            (SymValue::Ptr(pa), SymValue::Ptr(pb)) => {
                if prov_select_depth(&pa.prov).max(prov_select_depth(&pb.prov)) >= 8 {
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Unknown(POrigin::SelectJoin, None),
                        offset: self.ctx.int(PTR_WIDTH, 0),
                        align: 1,
                    })
                } else {
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Select {
                            cond: d,
                            then_ptr: Box::new(pa.clone()),
                            else_ptr: Box::new(pb.clone()),
                        },
                        offset: self.ctx.int(PTR_WIDTH, 0),
                        align: gcd(pa.align, pb.align),
                    })
                }
            }
            _ => self.fresh_value(ty, POrigin::SelectJoin),
        }
    }

    /// Whether `cond` is **bit-precisely** unsatisfiable under the current path,
    /// i.e. `pathcond ∧ facts ⟹ ¬cond` holds *exactly*. Then the branch guarded
    /// by `cond` has no concrete execution and is soundly pruned.
    ///
    /// The check is deliberately **bit-precise**, not linear: pruning on a
    /// `linear-no-overflow`-dependent implication could discard a branch that is
    /// actually reachable only through wraparound and so hide a real violation
    /// (a false PASS). A bit-precise `⟹ ¬cond` holds for *every* machine value,
    /// so the branch is genuinely dead. Missing a (linear-only) infeasibility
    /// just keeps a redundant path — never unsound.
    fn branch_infeasible(&mut self, cond: ExprId, state: &PathState) -> bool {
        let not_cond = self.ctx.not(cond);
        let mut assumptions = state.pathcond.clone();
        assumptions.extend_from_slice(&state.facts);
        bitprecise::prove_implies(&self.ctx, &assumptions, not_cond)
    }

    /// Whether the edge `from -> to` is a loop back-edge (cut during
    /// exploration). A back-edge targets a loop header that dominates its
    /// source.
    fn is_back_edge(&self, from: BlockId, to: BlockId) -> bool {
        if !self.headers.contains(&to) {
            return false;
        }
        let cfg = self.analysis.cfg();
        let (Some(fi), Some(ti)) = (cfg.index_of(from), cfg.index_of(to)) else {
            return false;
        };
        self.dominators.dominates(ti, fi)
    }

    /// Replace a loop header's parameters with fresh symbols constrained by the
    /// interval invariant that holds at the header on every iteration.
    fn havoc_header(&mut self, header: BlockId, state: &mut PathState) {
        // Havocking introduces over-approximation, so this path is no longer
        // exact: it may stand for unreachable states, so we must not refute on it.
        state.exact = false;
        // The loop may have written arbitrary memory across iterations, so the
        // stored-value knowledge is no longer reliable: forget it (sound
        // over-approximation; loads then return fresh unknowns).
        state.heap.clear();
        state.unwritten_reads.clear();
        state.ref_regions.clear();

        // Equality-exit induction variables (`while i != n { … i += c }`): capture
        // each one's start (its pre-havoc value) and bound now, before the havoc
        // below replaces it with a fresh symbol. The sound bound is asserted after
        // the havoc (see `assert_eq_exit_bound`).
        let inductions: Vec<(EqExitIndVar, ExprId, ExprId)> = self
            .inductions
            .eq_exit_indvars(header)
            .to_vec()
            .into_iter()
            .filter_map(|iv| {
                let start = match state.env.get(&iv.reg) {
                    Some(SymValue::Scalar(e)) => *e,
                    _ => return None,
                };
                let bound = self.eval_scalar(&iv.bound, state);
                Some((iv, start, bound))
            })
            .collect();

        // Pointer equality-exit induction (`iter != end`): capture each one's
        // base region/offset/alignment, the end pointer's offset in that same
        // region, and the region byte size — all before the havoc clobbers
        // `iter`. The bounded offset is installed after the havoc (see
        // `assert_ptr_walk_bound`).
        let ptr_inductions: Vec<PtrIndCapture> = self
            .inductions
            .eq_exit_ptr_indvars(header)
            .to_vec()
            .into_iter()
            .filter_map(|iv: PtrIndVar| {
                let SymValue::Ptr(base) = state.env.get(&iv.reg)?.clone() else { return None };
                let Prov::Region(region) = base.prov else { return None };
                let size = state.regions.get(region)?.size;
                let SymValue::Ptr(end) = self.eval_value(&iv.end, state) else { return None };
                let Prov::Region(end_region) = end.prov else { return None };
                if end_region != region {
                    return None; // end is in a different allocation: cannot relate
                }
                let elem_stride = iv.elem.stride_bytes(&LAYOUT).unwrap_or(1).max(1);
                let stride_bytes = u64::try_from(iv.stride_elems).ok()?.checked_mul(elem_stride)?;
                Some(PtrIndCapture {
                    reg: iv.reg,
                    region,
                    b0: base.offset,
                    align: base.align,
                    end_off: end.offset,
                    size,
                    stride_bytes,
                    bottom_test: iv.bottom_test,
                })
            })
            .collect();

        // If the loop body may free memory, then on any iteration after the
        // first a region could already be freed — so no region's liveness can
        // be proved inside (or after) the loop. Invalidate liveness
        // conservatively. (Loops that never free are unaffected.) Only *owned
        // heap* regions can be legitimately freed: a free of a borrowed or
        // stack/global region is flagged by `check_dealloc` (or the callee's own
        // verification), leaving the function non-PASS on that path anyway.
        if self.loop_frees.get(&header).copied().unwrap_or(false) {
            for r in &mut state.regions {
                if r.state == LifetimeState::Live
                    && r.contract.is_none()
                    && matches!(r.kind, RegionKind::Heap)
                {
                    r.state = LifetimeState::Freed;
                }
            }
        }

        // Havoc *every* register the loop body may redefine — not just the
        // header's own parameters. In strict SSA the loop-carried values are
        // header parameters and the rest are recomputed before use, so this is
        // usually redundant; but it makes the analysis robust to non-SSA input
        // (a register reassigned in the body keeps no stale pre-loop value).
        let modified = self
            .loop_modified
            .get(&header)
            .cloned()
            .unwrap_or_default();
        let modified_set: HashSet<RegId> = modified.iter().copied().collect();
        for reg in modified {
            match state.env.get(&reg).cloned() {
                Some(SymValue::Ptr(pre)) => {
                    // A loop-modified pointer loses its *region/bounds* provenance
                    // (conservative — it becomes opaque). But it **keeps its provenance
                    // labels**: an iterator walking a `foreign` container (a `list_for_each`
                    // over a foreign scatterlist) stays foreign. Sound — labels only feed the
                    // gated capability sink, never a memory-safety check — and it is what lets
                    // the taint reach the sink through the real worker's list traversal.
                    let labels = match pre.prov {
                        Prov::Region(rid) => {
                            state.regions.get(rid).map(|r| r.prov_labels.clone()).unwrap_or_default()
                        }
                        Prov::Unknown(_, Some(id)) => {
                            state.opaque_labels.get(&id).cloned().unwrap_or_default()
                        }
                        _ => HashSet::new(),
                    };
                    let offset = self.ctx.int(PTR_WIDTH, 0);
                    let id = self.prov_ids;
                    self.prov_ids += 1;
                    if !labels.is_empty() {
                        state.opaque_labels.insert(id, labels);
                    }
                    state.env.insert(
                        reg,
                        SymValue::Ptr(SymPointer {
                            prov: Prov::Unknown(POrigin::Loop, Some(id)),
                            offset,
                            align: 1,
                        }),
                    );
                }
                Some(SymValue::Scalar(_)) => {
                    // A unit-stride, single-exit counting induction reaches every value
                    // its body guard admits, so model it as a GENUINE symbol (`ind…`):
                    // the body path condition's guard on it is then an exact reachable
                    // range, and an access it indexes can be refuted (an OOB there is a
                    // real bug). Otherwise a plain over-approximated `?` symbol.
                    let s = if self.sound_counting_induction(header, reg) {
                        self.fresh_induction_scalar(PTR_WIDTH)
                    } else {
                        self.fresh_scalar(PTR_WIDTH)
                    };
                    // Constrain by the sound interval invariant at the header
                    // (only faithfully-encodable, non-negative bounds).
                    let iv = self.analysis.entry_interval(header, reg);
                    if let Some(Bound::Fin(lo)) = iv.lower() {
                        if lo >= 0 {
                            let k = self.ctx.int(PTR_WIDTH, lo as u128);
                            let fact = self.ctx.cmp(SCmp::Sge, s, k);
                            state.facts.push(fact);
                        }
                    }
                    if let Some(Bound::Fin(hi)) = iv.upper() {
                        if hi >= 0 {
                            let k = self.ctx.int(PTR_WIDTH, hi as u128);
                            let fact = self.ctx.cmp(SCmp::Sle, s, k);
                            state.facts.push(fact);
                        }
                    }
                    state.env.insert(reg, SymValue::Scalar(s));
                }
                None => {} // not live at the header; defined fresh in the body
            }
        }

        // A register live at the header but *not* modified by the loop (a bound
        // computed before it — e.g. a clamped length `n = min(n, cap)`) keeps its
        // symbolic value, so it is not havoc'd above; but its sound interval bound
        // at the header still holds every iteration. Assert it, so a body access
        // guarded by it (`i < n`, with `n <= cap` known only to the interval
        // domain after guard refinement) can be proved. Deterministic order.
        let live_scalars: Vec<RegId> = {
            let mut v: Vec<RegId> = state
                .env
                .iter()
                .filter(|(r, val)| !modified_set.contains(r) && matches!(val, SymValue::Scalar(_)))
                .map(|(r, _)| *r)
                .collect();
            v.sort_unstable_by_key(|r| r.0);
            v
        };
        for reg in live_scalars {
            let Some(&SymValue::Scalar(s)) = state.env.get(&reg) else { continue };
            // Constrain at the *value's own width* — an `i1` (a boolean like
            // `buf == end`) carries no useful numeric bound and comparing it to a
            // 64-bit constant is ill-typed, so skip narrow values.
            let w = self.ctx.width(s);
            if w <= 1 {
                continue;
            }
            let iv = self.analysis.entry_interval(header, reg);
            if let Some(Bound::Fin(lo)) = iv.lower() {
                if lo >= 0 {
                    let k = self.ctx.int(w, lo as u128);
                    let fact = self.ctx.cmp(SCmp::Sge, s, k);
                    state.facts.push(fact);
                }
            }
            if let Some(Bound::Fin(hi)) = iv.upper() {
                if hi >= 0 {
                    let k = self.ctx.int(w, hi as u128);
                    let fact = self.ctx.cmp(SCmp::Sle, s, k);
                    state.facts.push(fact);
                }
            }
        }

        // Relational (zone) invariants: difference constraints `a - b <= c`
        // between the freshly-havoc'd register values that hold on every header
        // visit (e.g. `j <= i`). These are exactly what the per-register interval
        // bounds above cannot express, so they let a loop whose safety is a
        // *relation* between variables (a second induction variable, `buf[j]`
        // with `j <= i < n`) be proved. Sound under the same `linear-no-overflow`
        // assumption as the interval facts.
        let diffs: Vec<(ExprId, ExprId, i128)> = self
            .zones
            .entry_diffs(header)
            .into_iter()
            .filter_map(|(a, b, c)| match (state.env.get(&a), state.env.get(&b)) {
                (Some(SymValue::Scalar(ea)), Some(SymValue::Scalar(eb))) => Some((*ea, *eb, c)),
                _ => None,
            })
            .collect();
        for (ea, eb, c) in diffs {
            // The zone invariant `a - b <= c`, encoded as `a <=s b + c`. A *wrapping*
            // `b + c` makes the naive fact unsound: if the add signed-overflows, the
            // wrapped sum is wrong and the fact can read FALSE on a state where the
            // invariant genuinely holds — excluding a reachable state, which could
            // license a false PASS. Guard it to be vacuously true exactly when the
            // add overflows: then the fact is sound *bit-precisely* (no
            // linear-no-overflow tax on its consumers), and on the common no-overflow
            // path it collapses to the same strong `a <=s b + c` as before.
            //
            // `c` is a compile-time constant, so (a) skip bounds that do not fit the
            // blastable signed width — `const_expr` would misrepresent them — and
            // (b) its sign picks the overflow direction.
            if i64::try_from(c).is_err() {
                continue;
            }
            let cexpr = self.const_expr(c);
            let sum = self.ctx.bin(BvOp::Add, eb, cexpr);
            let le = self.ctx.cmp(SCmp::Sle, ea, sum); // a <=s b + c
            let fact = if c == 0 {
                le // b + 0 = b: never overflows
            } else if c > 0 {
                // adding c > 0 overflowed iff the sum dropped below b
                let overflow = self.ctx.cmp(SCmp::Slt, sum, eb);
                self.ctx.or(vec![overflow, le])
            } else {
                // adding c < 0 underflowed iff the sum rose above b
                let underflow = self.ctx.cmp(SCmp::Sgt, sum, eb);
                self.ctx.or(vec![underflow, le])
            };
            state.facts.push(fact);
        }

        // Equality-exit induction bounds: for each `while v != bound { … v += c }`
        // recognized at this header, assert `start ≤ v ≤ bound` on the now-havoc'd
        // `v` — after solver-checking the soundness side-conditions.
        for (iv, start_e, bound_e) in inductions {
            if let Some(SymValue::Scalar(v)) = state.env.get(&iv.reg).cloned() {
                self.assert_eq_exit_bound(state, v, start_e, bound_e, iv.stride);
            }
        }

        // Pointer-walk (`iter != end`) bounds: install the region-bounded offset
        // for each recognized pointer induction, replacing the conservative
        // opaque pointer the generic havoc produced.
        for cap in ptr_inductions {
            self.assert_ptr_walk_bound(state, cap);
        }

        // Sentinel-scan (`while (p[n] != 0) n++`) bound: if this loop sequentially
        // scans a sentinel-terminated region for its zero terminator, its index
        // cannot pass that terminator, which lies before the end.
        self.install_sentinel_scan_bound(header, state);
    }

    /// If `header`'s loop is a **sentinel scan** over a sentinel-terminated region
    /// — an index `n` starting at 0 and stepping by one element, a load of
    /// `base[n]`, and a loop exit taken exactly when that load is zero — bound the
    /// index by the region so every `base[n]` access is in bounds. Sound because a
    /// zero element is guaranteed before the end and the unit stride visits every
    /// element, so the scan stops at or before it: `n < element_count`, hence
    /// `(n+1)·E ≤ size`. Every side-condition below is checked; if any fails,
    /// nothing is installed.
    /// Is `reg` a **unit-stride, single-exit counting induction** at `header`? Such a
    /// loop reaches *every* value its governing guard admits, so the guard that the
    /// loop body's path condition already carries (entering the body requires it) is
    /// the induction's *exact* reachable range — not an over-approximation. Then a
    /// memory access indexed by the induction may be refuted: a witness value the
    /// guard admits is genuinely reached, so an out-of-bounds there is a real bug
    /// (e.g. an inclusive `for (i = 0; i <= N; i++) a[i]` writing `a[N]`).
    ///
    /// Requires, structurally: `reg` is a header parameter; its entry value is a
    /// constant and its back-edge value is `reg + 1` (unit stride up); the header's
    /// own branch is the loop's **only** exit and is governed by an upper-bound
    /// comparison on `reg` (`reg < B` / `reg <= B`, signed or unsigned) that gates
    /// entry to the body — so the body path condition bounds `reg` to the reached set.
    fn sound_counting_induction(&self, header: BlockId, reg: RegId) -> bool {
        let Some(hdr) = self.f.block(header) else { return false };
        let Some(pos) = hdr.params.iter().position(|(r, _)| *r == reg) else { return false };
        let mut def: HashMap<RegId, &Inst> = HashMap::new();
        for b in &self.f.blocks {
            for inst in &b.insts {
                if let Some(d) = inst.defined_reg() {
                    def.insert(d, inst);
                }
            }
        }
        // Unit-stride up: const entry, `reg + 1` back-edge.
        let preds: Vec<BlockId> = self
            .analysis
            .cfg()
            .predecessors(self.analysis.cfg().index_of(header).unwrap_or(usize::MAX))
            .iter()
            .map(|&p| self.analysis.cfg().block_id(p))
            .collect();
        let (mut const_entry, mut unit_backedge) = (false, false);
        for &pred in &preds {
            let Some(args) = edge_args(self.f, pred, header) else { continue };
            let Some(arg) = args.get(pos) else { continue };
            if self.is_back_edge(pred, header) {
                if let Operand::Reg(m) = arg {
                    if let Some(Inst::Assign { value: RValue::Bin { op: BinOp::Add, lhs, rhs }, .. }) =
                        def.get(&resolve_copy(*m, &def))
                    {
                        let one = |o: &Operand| matches!(o, Operand::Const(Const::Int(bv)) if bv.unsigned() == 1);
                        let is_r = |o: &Operand| matches!(o, Operand::Reg(r) if resolve_copy(*r, &def) == reg);
                        unit_backedge = (is_r(lhs) && one(rhs)) || (is_r(rhs) && one(lhs));
                    }
                }
            } else if matches!(arg, Operand::Const(Const::Int(_))) {
                const_entry = true;
            }
        }
        if !(const_entry && unit_backedge) {
            return false;
        }
        // The header's branch is an upper-bound guard on `reg` gating body entry.
        let Terminator::CondBr { cond: Operand::Reg(c), then_blk, else_blk, .. } = &hdr.term else {
            return false;
        };
        let body = self.loop_bodies.get(&header).map(|b| b.as_slice()).unwrap_or(&[]);
        let in_body = |b: &BlockId| body.contains(b);
        let upper_on_reg = matches!(
            def.get(&resolve_copy(*c, &def)),
            Some(Inst::Assign { value: RValue::Cmp { op: CmpOp::Slt | CmpOp::Sle | CmpOp::Ult | CmpOp::Ule, lhs, rhs }, .. })
                if matches!(lhs, Operand::Reg(r) if resolve_copy(*r, &def) == reg)
                    && !matches!(rhs, Operand::Reg(r) if resolve_copy(*r, &def) == reg)
        );
        // The true edge must enter the loop (else the guard is inverted and the body
        // pathcond would carry its negation — not a clean upper bound).
        if !(upper_on_reg && in_body(then_blk) && !in_body(else_blk)) {
            return false;
        }
        // Single exit: the header's guard is the loop's only way out. Any other
        // body→outside edge (a `break`) means an iteration can be skipped, so a
        // guard-admitted index is no longer guaranteed reached.
        let body_set: HashSet<BlockId> = body.iter().copied().collect();
        for &bid in body {
            if bid == header {
                continue;
            }
            let Some(b) = self.f.block(bid) else { continue };
            let exits = match &b.term {
                Terminator::Br { target, .. } => !body_set.contains(target),
                Terminator::CondBr { then_blk, else_blk, .. } => {
                    !body_set.contains(then_blk) || !body_set.contains(else_blk)
                }
                _ => true, // a return/unreachable inside the body is another exit
            };
            if exits {
                return false;
            }
        }
        true
    }

    /// A fresh **genuine induction** symbol (named `ind…`, accepted by
    /// [`Explorer::goal_is_genuine`]): a unit-stride counter that reaches every value
    /// its body guard admits, so an access it indexes is refutable within that range.
    fn fresh_induction_scalar(&mut self, width: u32) -> ExprId {
        let name = format!("ind{}", self.fresh);
        self.fresh += 1;
        self.ctx.symbol(name, width)
    }

    fn install_sentinel_scan_bound(&mut self, header: BlockId, state: &mut PathState) {
        let Some(body) = self.loop_bodies.get(&header).cloned() else { return };
        let body_set: HashSet<BlockId> = body.iter().copied().collect();
        let Some(hdr) = self.f.block(header) else { return };

        // Definition of every register (for the increment / gep / cmp checks).
        let mut def: HashMap<RegId, &Inst> = HashMap::new();
        for b in &self.f.blocks {
            for inst in &b.insts {
                if let Some(d) = inst.defined_reg() {
                    def.insert(d, inst);
                }
            }
        }

        // 1. A counting induction `n`: a header parameter whose value is 0 on the
        //    entry edge and `n + 1` on the back-edge (unit stride, so it visits
        //    every element and cannot step over the sentinel).
        let preds: Vec<BlockId> = self
            .analysis
            .cfg()
            .predecessors(self.analysis.cfg().index_of(header).unwrap_or(usize::MAX))
            .iter()
            .map(|&p| self.analysis.cfg().block_id(p))
            .collect();
        for (pos, &(n, _)) in hdr.params.iter().enumerate() {
            let mut zero_entry = false;
            let mut unit_backedge = false;
            for &pred in &preds {
                let Some(args) = edge_args(self.f, pred, header) else { continue };
                let Some(arg) = args.get(pos) else { continue };
                if self.is_back_edge(pred, header) {
                    // back-edge arg must be `n + 1`.
                    if let Operand::Reg(m) = arg {
                        if let Some(Inst::Assign { value: RValue::Bin { op: BinOp::Add, lhs, rhs }, .. }) =
                            def.get(&resolve_copy(*m, &def))
                        {
                            let one = |o: &Operand| matches!(o, Operand::Const(Const::Int(bv)) if bv.unsigned() == 1);
                            // The increment operand may be a copy of `n`.
                            let is_n = |o: &Operand| matches!(o, Operand::Reg(r) if resolve_copy(*r, &def) == n);
                            unit_backedge = (is_n(lhs) && one(rhs)) || (is_n(rhs) && one(lhs));
                        }
                    }
                } else if matches!(arg, Operand::Const(Const::Int(bv)) if bv.unsigned() == 0) {
                    zero_entry = true;
                }
            }
            if !(zero_entry && unit_backedge) {
                continue;
            }

            // 2. In the body, a load `v = base[n]` of an `E`-byte element, where
            //    `base` evaluates to a sentinel-terminated region of element `E`.
            for &bid in &body {
                let Some(blk) = self.f.block(bid) else { continue };
                for inst in &blk.insts {
                    let Inst::Load { dst: v, ty, ptr: Operand::Reg(q), .. } = inst else { continue };
                    let Some(Inst::PtrOffset { base: Operand::Reg(b), index: Operand::Reg(idx), elem, .. }) =
                        def.get(q)
                    else {
                        continue;
                    };
                    // mem2reg leaves the base/index as copies of the parameter and
                    // the induction (`%b = base`, `%i = n`); follow those chains,
                    // and at -O0 the index is a `sext`/`zext` of the counter.
                    if resolve_index(*idx, &def) != n {
                        continue;
                    }
                    let base_reg = resolve_copy(*b, &def);
                    let Some(e) = elem.size_bytes(&LAYOUT) else { continue };
                    if ty.size_bytes(&LAYOUT) != Some(e) {
                        continue;
                    }
                    // The base must be a live sentinel region of matching element.
                    let Some(SymValue::Ptr(bp)) = state.env.get(&base_reg) else { continue };
                    let Prov::Region(rid) = bp.prov else { continue };
                    let Some(region) = state.regions.get(rid) else { continue };
                    if region.sentinel != Some(e) {
                        continue;
                    }
                    // 3. The loaded value must gate the loop exit: a `v == 0` /
                    //    `v != 0` comparison feeding a branch that leaves the loop.
                    if !self.loaded_value_gates_exit(*v, &body_set, &def) {
                        continue;
                    }
                    // All side-conditions hold. The induction value `n` is what the
                    // access offset uses — directly at -O1, and at -O0 through a
                    // `sext`/`zext` the executor models as a width-preserving no-op
                    // on the same expression (so `base[sext(n)]` reuses `n`'s value).
                    // Install `0 <= n` and `(n + 1)·E ≤ size`, so the access
                    // `base[n]` (offset `n·E`, span `E`) is in bounds.
                    let size = region.size;
                    let Some(&SymValue::Scalar(n_e)) = state.env.get(&n) else { continue };
                    if self.ctx.width(n_e) != PTR_WIDTH {
                        continue;
                    }
                    let zero = self.ctx.int(PTR_WIDTH, 0);
                    let nonneg = self.ctx.cmp(SCmp::Sle, zero, n_e);
                    let one = self.ctx.int(PTR_WIDTH, 1);
                    let np1 = self.ctx.bin(BvOp::Add, n_e, one);
                    let e_e = self.ctx.int(PTR_WIDTH, e as u128);
                    let bytes = self.ctx.bin(BvOp::Mul, np1, e_e);
                    let fact = self.ctx.cmp(SCmp::Sle, bytes, size);
                    state.facts.push(nonneg);
                    state.facts.push(fact);
                    return;
                }
            }
        }
    }

    /// Whether `v` (a loaded value) feeds a comparison to zero that governs a
    /// branch leaving the loop body — the sentinel test of a scan.
    fn loaded_value_gates_exit(
        &self,
        v: RegId,
        body: &HashSet<BlockId>,
        def: &HashMap<RegId, &Inst>,
    ) -> bool {
        // Registers equal to `v`'s zero-test: `icmp eq/ne v, 0`.
        let mut tests: HashSet<RegId> = HashSet::new();
        for (d, inst) in def {
            if let Inst::Assign { value: RValue::Cmp { op: CmpOp::Eq | CmpOp::Ne, lhs, rhs }, .. } = inst {
                let is_v = |o: &Operand| matches!(o, Operand::Reg(r) if *r == v);
                let is_zero = |o: &Operand| matches!(o, Operand::Const(Const::Int(bv)) if bv.unsigned() == 0);
                if (is_v(lhs) && is_zero(rhs)) || (is_v(rhs) && is_zero(lhs)) {
                    tests.insert(*d);
                }
            }
        }
        if tests.is_empty() {
            return false;
        }
        // A `CondBr` on such a test with a target outside the loop = the exit.
        for &bid in body {
            let Some(blk) = self.f.block(bid) else { continue };
            if let Terminator::CondBr { cond: Operand::Reg(c), then_blk, else_blk, .. } = &blk.term {
                if tests.contains(c) && (!body.contains(then_blk) || !body.contains(else_blk)) {
                    return true;
                }
            }
        }
        false
    }

    /// Install the sound offset bound for a pointer equality-exit induction. The
    /// generic havoc made `iter` opaque; here — only after **proving** the
    /// side-conditions — we restore its region provenance with a fresh offset `o`
    /// constrained by `b0 ≤ o`, the congruence `o ≡ b0 (mod stride)`, and an upper
    /// bound that depends on the loop form:
    ///   - **header-test** (`bottom_test == false`): `o ≤ end_off`. The load is
    ///     guarded, so with the guard `iter != end` (`o != end_off`) the
    ///     congruence gives `o ≤ end_off − stride`, hence `o + stride ≤ end_off`.
    ///   - **bottom-test / rotated** (`bottom_test == true`): `o + stride ≤
    ///     end_off`. The load is unconditional, so this stronger invariant is
    ///     needed directly; its base case (`b0 + stride ≤ end_off`) is provable
    ///     only when the loop is entered non-empty — i.e. from the preheader
    ///     guard `base != end`, which sits in this header's path condition.
    ///
    /// The common side-conditions: `0 ≤ b0`, `end_off ≤ size ≤ isize::MAX`, and
    /// `stride | (end_off − b0)` (so `end` lies on the walk's grid — otherwise the
    /// pointer steps over `end`, never satisfies the `== end` exit, and the bound
    /// would be unsound). Only power-of-two strides (the element sizes that arise)
    /// get the exact bit-precise divisibility; others are skipped.
    fn assert_ptr_walk_bound(&mut self, state: &mut PathState, cap: PtrIndCapture) {
        let stride = cap.stride_bytes;
        if stride == 0 || !(stride as u128).is_power_of_two() {
            return;
        }
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let isize_max = self.ctx.int(PTR_WIDTH, i64::MAX as u128);
        let mask = self.ctx.int(PTR_WIDTH, (stride as u128) - 1);
        // `lo + d` is the largest accessed offset's lower witness: for the rotated
        // form the load happens at the unincremented pointer, so the invariant is
        // shifted by one stride (`d = stride`); the header-test form has `d = 0`.
        let plus_d = |s: &mut Self, e: ExprId| -> ExprId {
            if cap.bottom_test {
                let d = s.ctx.int(PTR_WIDTH, stride as u128);
                s.ctx.bin(BvOp::Add, e, d)
            } else {
                e
            }
        };
        // (end_off − b0) & mask == 0: end is on the walk's grid.
        let ediff = self.ctx.bin(BvOp::Sub, cap.end_off, cap.b0);
        let emask = self.ctx.bin(BvOp::And, ediff, mask);
        let end_on_grid = self.ctx.cmp(SCmp::Eq, emask, zero);
        let b0_upper = plus_d(self, cap.b0);
        let gate = [
            self.ctx.cmp(SCmp::Sle, zero, cap.b0),           // 0 ≤ b0
            self.ctx.cmp(SCmp::Sle, b0_upper, cap.end_off),  // b0 (+ stride) ≤ end_off
            self.ctx.cmp(SCmp::Sle, cap.end_off, cap.size),  // end_off ≤ size
            self.ctx.cmp(SCmp::Sle, cap.size, isize_max),    // size ≤ isize::MAX
            end_on_grid,
        ];
        // The region's no-wrap premise (`size = count·stride ≤ isize::MAX`) lets
        // `size ≤ isize::MAX` be proved for a *symbolic* slice length, and the
        // preheader guard (already in `pathcond`) is what makes the rotated form's
        // `b0 + stride ≤ end_off` provable. Both are read from the current state.
        let nowrap = state.regions.get(cap.region).and_then(|r| r.size_nowrap);
        let restore = state.facts.len();
        if let Some(nw) = nowrap {
            state.facts.push(nw);
        }
        let proved = gate.into_iter().all(|g| self.prove(g, state));
        state.facts.truncate(restore);
        if !proved {
            return;
        }
        // Sound: a region pointer at a fresh, grid-aligned, in-range offset.
        let o = self.fresh_scalar(PTR_WIDTH);
        state.env.insert(
            cap.reg,
            SymValue::Ptr(SymPointer {
                prov: Prov::Region(cap.region),
                offset: o,
                align: gcd(cap.align, stride),
            }),
        );
        let o_upper = plus_d(self, o);
        let odiff = self.ctx.bin(BvOp::Sub, o, cap.b0);
        let omask = self.ctx.bin(BvOp::And, odiff, mask);
        let ediff2 = self.ctx.bin(BvOp::Sub, cap.end_off, cap.b0);
        let emask2 = self.ctx.bin(BvOp::And, ediff2, mask);
        let facts = [
            self.ctx.cmp(SCmp::Sle, zero, cap.b0),          // 0 ≤ b0
            self.ctx.cmp(SCmp::Sle, cap.b0, o),             // b0 ≤ o
            self.ctx.cmp(SCmp::Sle, zero, o_upper),         // 0 ≤ o (+ stride) (no wrap)
            self.ctx.cmp(SCmp::Sle, o_upper, cap.end_off),  // o (+ stride) ≤ end_off
            self.ctx.cmp(SCmp::Sle, o_upper, cap.size),     // o (+ stride) ≤ size
            self.ctx.cmp(SCmp::Sle, cap.end_off, cap.size), // end_off ≤ size
            self.ctx.cmp(SCmp::Sle, cap.size, isize_max),   // size ≤ isize::MAX (no wrap)
            self.ctx.cmp(SCmp::Eq, omask, zero),            // o ≡ b0 (mod stride)
            self.ctx.cmp(SCmp::Eq, emask2, zero),           // end_off ≡ b0 (mod stride)
        ];
        state.facts.extend(facts);
    }

    /// Assert the sound bound `start ≤ v ≤ bound` for an equality-exit induction
    /// variable, but only after **proving** the side-conditions that make it a
    /// true loop invariant: `0 ≤ start ≤ bound ≤ isize::MAX` (the counter starts
    /// in range and the bound does not wrap), and `stride | (bound − start)` so
    /// `bound` lies on the grid `{start + k·stride}` — otherwise `v` steps *over*
    /// `bound`, never satisfies the `v == bound` exit, and could exceed `bound`
    /// (making the bound unsound). If any condition is not proved, nothing is
    /// asserted (sound fallback). The divisibility check is exact only for
    /// power-of-two strides (the element sizes that arise); other strides are
    /// skipped.
    fn assert_eq_exit_bound(
        &mut self,
        state: &mut PathState,
        v: ExprId,
        start: ExprId,
        bound: ExprId,
        stride: i128,
    ) {
        if stride <= 0 {
            return;
        }
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let isize_max = self.ctx.int(PTR_WIDTH, i64::MAX as u128);
        let mut gate = vec![
            self.ctx.cmp(SCmp::Sle, zero, start),     // 0 ≤ start
            self.ctx.cmp(SCmp::Sle, start, bound),    // start ≤ bound
            self.ctx.cmp(SCmp::Sle, bound, isize_max), // bound ≤ isize::MAX
        ];
        if stride > 1 {
            if !(stride as u128).is_power_of_two() {
                return; // non-power-of-two stride: divisibility not encodable exactly
            }
            // (bound − start) & (stride − 1) == 0  ⟺  stride | (bound − start).
            let mask = self.ctx.int(PTR_WIDTH, (stride as u128) - 1);
            let diff = self.ctx.bin(BvOp::Sub, bound, start);
            let masked = self.ctx.bin(BvOp::And, diff, mask);
            gate.push(self.ctx.cmp(SCmp::Eq, masked, zero));
        }
        if !gate.into_iter().all(|g| self.prove(g, state)) {
            return;
        }
        let f_lo = self.ctx.cmp(SCmp::Sle, start, v);
        let f_hi = self.ctx.cmp(SCmp::Sle, v, bound);
        state.facts.push(f_lo);
        state.facts.push(f_hi);
    }

    fn step(&mut self, block: BlockId, idx: usize, inst: &Inst, state: &mut PathState) {
        match inst {
            Inst::Assign { dst, ty, value } => {
                // A generically-bound **pointer** call result (`Assign(dst, Undef)` for a
                // modelled call with no return summary — e.g. `fopen`'s handle) must get a
                // *stable opaque pointer identity*, not a scalar `undef`: otherwise the same
                // SSA value is a scalar here and an opaque pointer once used as one, so a
                // `ret`-typestate/taint target and a later use disagree on the resource key.
                let v = match value {
                    RValue::Use(Operand::Const(Const::Undef)) if ty.is_ptr() => {
                        self.fresh_value(ty, POrigin::Call)
                    }
                    _ => self.eval_rvalue(value, state),
                };
                state.env.insert(*dst, v);
                // Taint propagation: the result carries the union of its operands' taint.
                let t = self.rvalue_taint(value, state);
                if t.is_empty() {
                    state.tainted.remove(dst);
                } else {
                    state.tainted.insert(*dst, t);
                }
            }
            Inst::Alloc { dst, region, elem, count, align } => {
                let stride = elem.stride_bytes(&LAYOUT).unwrap_or(1).max(1);
                let count_e = self.eval_scalar(count, state);
                let stride_e = self.ctx.int(PTR_WIDTH, stride as u128);
                let size = self.ctx.bin(BvOp::Mul, count_e, stride_e);
                let perms = if *region == RegionKind::Global {
                    Permissions::READ_ONLY
                } else {
                    Permissions::READ_WRITE
                };
                // A successful allocation has size <= isize::MAX, so the element
                // count times the stride does not wrap (`alloc-succeeds`). Kept
                // off `facts` (it would slow every proof) and used only to make a
                // memory-OOB counterexample faithful.
                let nowrap = self.size_no_wrap_fact(count_e, stride);
                let rid = state.regions.len();
                state.regions.push(SymRegion {
                    kind: *region,
                    size,
                    state: LifetimeState::Live,
                    perms,
                    contract: None,
                    size_nowrap: Some(nowrap),
                    sentinel: None,
                    user_controlled: false,
                    assumed: false,
                    prov_labels: HashSet::new(),
                });
                // Bug-finding: an attacker-controlled `count * sizeof(T)` size that can
                // wrap the pointer width under-allocates — a heap overflow at the root.
                // When the size is a variable factor times a constant element size `c`,
                // overflow is exactly `var > (UINT_MAX / c)` — a constant-bound check the
                // solver discharges cheaply (no wide multiply). A feasible genuine
                // overflow is refuted with a witness; a bounded (guarded) count proves.
                // Only run in bug-finding mode; sound `verify` does not enumerate this
                // obligation, so allocation sizes stay non-wrapping under `alloc-succeeds`.
                if self.bug_finding {
                    match self.size_overflow_goal(size) {
                        Some(goal) => {
                            let decision = self.decide(&[goal], state, RefuteMode::Possible, &[]);
                            self.record_mem(block, idx, SafetyProperty::NoSizeOverflow, decision, "allocation size does not overflow", "the size product may overflow and under-allocate");
                        }
                        None => self.record(block, idx, SafetyProperty::NoSizeOverflow, true, "allocation size does not overflow", ""),
                    }
                } else {
                    self.record(block, idx, SafetyProperty::NoSizeOverflow, true, "allocation size does not overflow", "");
                }
                // The byte size is non-negative by construction.
                let zero = self.ctx.int(PTR_WIDTH, 0);
                let nonneg = self.ctx.cmp(SCmp::Sle, zero, size);
                state.facts.push(nonneg);
                state.env.insert(
                    *dst,
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Region(rid),
                        offset: zero,
                        align: *align as u64,
                    }),
                );
            }
            Inst::PtrOffset { dst, base, index, elem } => {
                let stride = elem.stride_bytes(&LAYOUT).unwrap_or(1).max(1);
                let base_ptr = self.eval_pointer(base, state);
                // Widen a narrower index to pointer width — a `zext i32 %i to i64`
                // the executor kept at its source width (the common `arr[unsigned]`
                // form), else the offset arithmetic mixes widths and no bound holds.
                let index_e = self.eval_scalar(index, state);
                let index_e = self.widen_to_ptr(index_e);
                let stride_e = self.ctx.int(PTR_WIDTH, stride as u128);
                let delta = self.ctx.bin(BvOp::Mul, index_e, stride_e);
                let new_off = self.ctx.bin(BvOp::Add, base_ptr.offset, delta);
                // Alignment after the offset: for a *constant* index use the
                // concrete byte delta (so `buf(16-aligned) + 16` stays
                // 16-aligned); for a symbolic index fall back to the stride.
                let new_align = match self.ctx.as_const(index_e) {
                    Some(c) => {
                        let d = c.signed().wrapping_mul(stride as i128).unsigned_abs() as u64;
                        gcd(base_ptr.align, d)
                    }
                    None => gcd(base_ptr.align, stride),
                };
                let result = SymPointer {
                    prov: base_ptr.prov.clone(),
                    offset: new_off,
                    align: new_align,
                };
                self.check_ptr_arith(block, idx, &result, state);
                state.env.insert(*dst, SymValue::Ptr(result));
            }
            Inst::FieldPtr { dst, base, field, size, align } => {
                let base_ptr = self.eval_pointer(base, state);
                let result = match &base_ptr.prov {
                    // Guard against a stale (dropped-region) id — fall through to the
                    // unknown-provenance arm below rather than indexing out of bounds.
                    Prov::Region(r) if state.regions.get(*r).is_some() => {
                        // A typed field of a valid aggregate lies within it. Place
                        // it at its synthetic offset (concrete, so distinct fields
                        // are disjoint and the same field round-trips), assert
                        // `offset + size <= region size` (the field fits), and
                        // inherit the field's alignment (a field is aligned within
                        // its struct). The following Load/Store is then in bounds
                        // and aligned by construction — no real layout is needed.
                        let rid = *r;
                        let region_size = state.regions[rid].size;
                        let off = self.field_offset(rid, *field, *size);
                        let off_e = self.ctx.int(PTR_WIDTH, off as u128);
                        let end = self.ctx.int(PTR_WIDTH, (off + *size) as u128);
                        let hi = self.ctx.cmp(SCmp::Sle, end, region_size);
                        state.facts.push(hi);
                        SymPointer { prov: Prov::Region(rid), offset: off_e, align: (*align).max(1) }
                    }
                    // Not a known region (null/unknown provenance): the field
                    // pointer inherits it, so a later access is soundly unproven.
                    _ => SymPointer {
                        prov: base_ptr.prov.clone(),
                        offset: base_ptr.offset,
                        align: (*align).max(1),
                    },
                };
                state.env.insert(*dst, SymValue::Ptr(result));
            }
            Inst::Load { dst, ty, ptr, align } => {
                let p = self.eval_pointer(ptr, state);
                let asize = ty.size_bytes(&LAYOUT).unwrap_or(1);
                self.check_access((block, idx), &p, asize, *align as u64, SafetyProperty::ValidRead, state);
                self.record_shared_access(ptr, false, &p, state);
                let exact_before = state.exact;
                let (value, origin) = self.load_value(&p, asize, ty, state);
                match origin {
                    LoadOrigin::Stored => {}
                    LoadOrigin::Uncertain => state.exact = false,
                    LoadOrigin::Unwritten => {
                        // No store reaches this location. For a freshly-allocated
                        // region that is a read of uninitialized memory (UB). On
                        // an exact path it is a definite violation, refutable with
                        // a faithful witness. (Compute the witness before dropping
                        // `exact` for the unknown value below.)
                        if exact_before && self.is_fresh_alloc(&p, state) {
                            if let Some(model) = self.feasibility_witness(state) {
                                self.record_uninit_read(block, idx, model);
                            }
                        }
                        state.exact = false;
                    }
                }
                // Taint-on-read: a pointer loaded from a labelled object inherits its
                // provenance — a pointer stored in a `foreign` scatterlist/socket is itself
                // foreign. Only ADDS labels, and a label causes a FAIL only through a (gated)
                // capability requirement (`require-if-alias` never fires off the safe
                // out-of-place path), so this can introduce neither a false PASS nor a false
                // FAIL. Flows provenance through the plain pointer-field loads the real crypto
                // worker uses (`sk → ctx → tsgl_src`), complementing the RefWitness path.
                if ty.is_ptr() {
                    let src_labels = match p.prov {
                        Prov::Region(rid) => {
                            state.regions.get(rid).map(|r| r.prov_labels.clone()).unwrap_or_default()
                        }
                        Prov::Unknown(_, Some(id)) => {
                            state.opaque_labels.get(&id).cloned().unwrap_or_default()
                        }
                        _ => HashSet::new(),
                    };
                    if !src_labels.is_empty() {
                        match &value {
                            SymValue::Ptr(SymPointer { prov: Prov::Region(rid), .. }) => {
                                if let Some(r) = state.regions.get_mut(*rid) {
                                    r.prov_labels.extend(src_labels);
                                }
                            }
                            SymValue::Ptr(SymPointer { prov: Prov::Unknown(_, Some(vid)), .. }) => {
                                state.opaque_labels.entry(*vid).or_default().extend(src_labels);
                            }
                            _ => {}
                        }
                    }
                }
                // Devirtualisation: a pointer load from a constant ops-struct global
                // at a concrete offset with a known function-pointer field resolves the
                // loaded value to a specific callee, so a later indirect call through
                // `dst` uses that summary instead of an opaque havoc.
                if ty.is_ptr() {
                    if let Prov::Region(rid) = p.prov {
                        if let Some(table) = self.global_fnptrs.get(&rid) {
                            if let Some(off) = self.ctx.as_const(p.offset).map(|bv| bv.unsigned()) {
                                if let Some(&fid) = table.get(&(off as u64)) {
                                    state.fn_ptrs.insert(*dst, fid);
                                }
                            }
                        }
                    }
                }
                // Taint-on-read for **scalars**: a scalar loaded from a tainted region (a
                // `taint-source`-labelled buffer — e.g. a `copy_from_user` destination)
                // inherits the region's taint labels. (The pointer case is handled above.)
                if !ty.is_ptr() {
                    let src_labels = match p.prov {
                        Prov::Region(rid) => {
                            state.regions.get(rid).map(|r| r.prov_labels.clone()).unwrap_or_default()
                        }
                        Prov::Unknown(_, Some(id)) => {
                            state.opaque_labels.get(&id).cloned().unwrap_or_default()
                        }
                        _ => HashSet::new(),
                    };
                    if !src_labels.is_empty() {
                        state.tainted.entry(*dst).or_default().extend(src_labels);
                    }
                }
                state.env.insert(*dst, value);
            }
            Inst::Store { ty, ptr, value, align } => {
                let p = self.eval_pointer(ptr, state);
                let asize = ty.size_bytes(&LAYOUT).unwrap_or(1);
                self.check_access((block, idx), &p, asize, *align as u64, SafetyProperty::ValidWrite, state);
                self.record_shared_access(ptr, true, &p, state);
                let v = self.eval_value(value, state);
                // Taint through memory: storing a tainted scalar into a region taints the
                // region, so a value later loaded from it stays tainted (a `user`-tainted
                // length written into a descriptor field and read back at a sink).
                if let Operand::Reg(r) = value {
                    if let Some(labels) = state.tainted.get(r).cloned() {
                        match &p.prov {
                            Prov::Region(rid) => {
                                if let Some(reg) = state.regions.get_mut(*rid) {
                                    reg.prov_labels.extend(labels);
                                }
                            }
                            Prov::Unknown(_, Some(id)) => {
                                state.opaque_labels.entry(*id).or_default().extend(labels);
                            }
                            _ => {}
                        }
                    }
                }
                state.heap.push(StoreRecord { target: p, value: v, size: asize });
                // A store may reassign a raw-pointer field, so the region a later `RefWitness`
                // load of that field should materialise is now a *different* object. Drop the
                // materialised-field cache (which the RefWitness path consults instead of the
                // store) — else two loads straddling the store would be treated as the *same*
                // region and `require-if-alias` could fire spuriously (a false FAIL).
                state.ref_regions.clear();
            }
            Inst::Dealloc { ptr, .. } => {
                let p = self.eval_pointer(ptr, state);
                self.check_dealloc(block, idx, &p, state);
            }
            Inst::Call { dst, callee, args, ret_ty, ret_ref } => {
                self.check_lock_call((block, idx), callee, args, state);
                self.step_call((block, idx), dst.as_ref(), callee, args, ret_ty, *ret_ref, state);
            }
            Inst::Intrinsic { dst: Some(d), .. } => {
                let s = self.fresh_scalar(PTR_WIDTH);
                state.env.insert(*d, SymValue::Scalar(s));
            }
            Inst::SafetyCheck { condition, .. } => {
                let goal = self.eval_condition(condition, state);
                let decision = self.decide(&[goal], state, RefuteMode::Definite, &[]);
                self.record_scalar(block, idx, decision);
            }
            // Attach a provenance label (a contract `label`) — to the pointed-to region, or,
            // for an opaque pointer (a raw-pointer parameter), to its holding SSA register.
            Inst::ProvLabel { ptr, label } => {
                self.add_ptr_label(ptr, *label, state);
            }
            // Propagate provenance: `dst` absorbs `src`'s labels (a contract `propagate` — a
            // container taking in an element). A foreign element thus makes the container only
            // as capable as its least-capable member.
            Inst::ProvPropagate { dst, src } => {
                let src_labels = self.ptr_labels(src, state);
                for l in src_labels {
                    self.add_ptr_label(dst, l, state);
                }
            }
            // Require the pointed-to region/pointer to grant `cap` (a contract `require`). A
            // provenance set containing a label that provably lacks the capability is a
            // definite violation — refuted with the path-feasibility witness (a FAIL on an
            // exact / bug-finding path, else UNKNOWN). An unlabelled pointer grants everything
            // (sound: no false FAIL). Mirrors `record_temporal`.
            Inst::CapRequire { ptr, cap } => {
                let labels = self.ptr_labels(ptr, state);
                let lacks = self.labels_lack_cap(&labels, *cap);
                self.record_temporal(
                    (block, idx),
                    SafetyProperty::WriteCapability,
                    lacks,
                    state,
                    "the access target's provenance grants the required capability",
                    "the access target's provenance may not grant the required capability",
                );
            }
            // Conditional capability: fire ONLY when `a` and `b` have the SAME provenance
            // identity (an in-place `src == dst` op — same region or same opaque register) and
            // that provenance lacks `cap`. When they are distinct (the safe out-of-place path)
            // it never fires — the precise gate that catches in-place-write-to-foreign without
            // false-FAILing the copy.
            Inst::CapRequireIfAlias { a, b, cap } => {
                let (pa, pb) = (self.eval_pointer(a, state), self.eval_pointer(b, state));
                let lacks = self.alias_lacks_cap(&pa, &pb, *cap, state);
                self.record_temporal(
                    (block, idx),
                    SafetyProperty::WriteCapability,
                    lacks,
                    state,
                    "an in-place operation's aliased region grants the required capability",
                    "an in-place operation writes a region whose provenance may not grant it",
                );
            }
            // The inlined-request form: read the two field pointers back from the object
            // INTERNALLY (via read-your-writes, no safety obligation on these analyzer reads),
            // then apply the same in-place-alias check. Fires iff both fields hold the same
            // region and it lacks the capability.
            Inst::CapRequireIfAliasFields { obj, off_a, off_b, cap } => {
                let base = self.eval_pointer(obj, state);
                let field = |ex: &mut Self, off: u64, st: &mut PathState| -> SymValue {
                    let off_e = ex.ctx.int(PTR_WIDTH, off as u128);
                    let field_ptr = SymPointer {
                        prov: base.prov.clone(),
                        offset: ex.ctx.bin(BvOp::Add, base.offset, off_e),
                        align: 1,
                    };
                    ex.load_value(&field_ptr, PTR_WIDTH as u64 / 8, &Type::ptr(Type::int(8)), st).0
                };
                let (sv, dv) = (field(self, *off_a, state), field(self, *off_b, state));
                let lacks = match (&sv, &dv) {
                    (SymValue::Ptr(sp), SymValue::Ptr(dp)) => {
                        self.alias_lacks_cap(sp, dp, *cap, state)
                    }
                    _ => false,
                };
                self.record_temporal(
                    (block, idx),
                    SafetyProperty::WriteCapability,
                    lacks,
                    state,
                    "an in-place operation's aliased field region grants the required capability",
                    "an in-place operation writes a field region whose provenance may not grant it",
                );
            }
            // Directional taint (injection J / tainted-length F / info-flow D).
            Inst::TaintSource { val, taint } => {
                self.taint_add(val, *taint, state);
            }
            Inst::TaintClear { val, taint } => {
                self.taint_remove(val, *taint, state);
            }
            // A tainted value reaching a sink is refuted (a definite taint on this path — the
            // taint map is meet-joined, so no false FAIL under a partly-tainted phi). An
            // untainted / sanitised value passes. Mirrors `CapRequire`.
            Inst::TaintCheck { val, taint } => {
                let tainted = self.taint_has(val, *taint, state);
                self.record_temporal(
                    (block, idx),
                    SafetyProperty::TaintedSink,
                    tainted,
                    state,
                    "no untrusted (tainted) value reaches this sink",
                    "an untrusted (tainted) value reaches an unsafe sink (injection / tainted length)",
                );
            }
            // Typestate transition: move the named resource into `state` within `protocol`.
            Inst::TypestateSet { val, protocol, state: st } => {
                if let Some(key) = self.res_key(val, state) {
                    state.typestates.insert((key, *protocol), *st);
                }
            }
            // Typestate obligation: the resource must (not) be in `state`. A definite match
            // to the forbidden state on this path is refuted (use-after-close, missing-check).
            // An untracked resource (`None`, or no recorded state) is treated as *not* in any
            // named state — so `require-not` never false-FAILs an unseen handle, and `require`
            // (must-be-in-state) fires when the state was never established. Sound for bug-
            // finding; the meet-join guarantees a refutation is on a definite path.
            Inst::TypestateRequire { val, protocol, state: st, negate } => {
                let cur = self
                    .res_key(val, state)
                    .and_then(|key| state.typestates.get(&(key, *protocol)).copied());
                let in_state = cur == Some(*st);
                let violated = if *negate { in_state } else { !in_state };
                self.record_temporal(
                    (block, idx),
                    SafetyProperty::TypestateViolation,
                    violated,
                    state,
                    "the resource is in a protocol state this operation allows",
                    "the resource is used in a state its protocol forbids (use-after-close / missing-check)",
                );
            }
            // Protocol-wide yield (TOCTOU): every resource of `protocol` in state `from`
            // moves to `to` — a `check` invalidated by an intervening yield.
            Inst::TypestateYield { protocol, from, to } => {
                let hits: Vec<(ResKey, u32)> = state
                    .typestates
                    .iter()
                    .filter(|((_, p), s)| p == protocol && *s == from)
                    .map(|((k, p), _)| (*k, *p))
                    .collect();
                for key in hits {
                    state.typestates.insert(key, *to);
                }
            }
            // Reference-count change: inc/dec the resource's count; a `dec` below zero is an
            // underflow (premature free → UAF), refuted on a definite path.
            Inst::Refcount { val, protocol, dec } => {
                if let Some(key) = self.res_key(val, state) {
                    let entry = state.refcounts.entry((key, *protocol)).or_insert(0);
                    if *dec {
                        let underflow = *entry <= 0;
                        *entry -= 1;
                        self.record_temporal(
                            (block, idx),
                            SafetyProperty::TypestateViolation,
                            underflow,
                            state,
                            "the reference count stays non-negative",
                            "a reference-count decrement underflows (premature free / use-after-free)",
                        );
                    } else {
                        *entry += 1;
                        self.record(block, idx, SafetyProperty::TypestateViolation, true, "the reference count stays non-negative", "");
                    }
                }
            }
            // Leak check at return: a resource still in the leak `state` that did not escape
            // via the returned value is a resource leak.
            Inst::TypestateLeakCheck { protocol, state: st, escaping } => {
                let escapes = escaping
                    .as_ref()
                    .and_then(|op| self.res_key(op, state));
                let leaked = state.typestates.iter().any(|((k, p), s)| {
                    p == protocol && s == st && Some(*k) != escapes
                });
                self.record_temporal(
                    (block, idx),
                    SafetyProperty::TypestateViolation,
                    leaked,
                    state,
                    "every acquired resource is released or returned",
                    "a resource acquired on this path is neither released nor returned (leak)",
                );
            }
            // Constant-time: a secret-tainted value must not decide a branch or index memory.
            Inst::SecretCheck { val, taint } => {
                let secret = self.taint_has(val, *taint, state);
                self.record_temporal(
                    (block, idx),
                    SafetyProperty::SecretDependent,
                    secret,
                    state,
                    "no secret-dependent branch or memory index",
                    "a secret-tainted value decides a branch or memory index (timing/cache side channel)",
                );
            }
            Inst::RefWitness { dst, size, align, writable, assumed, src } => {
                // A raw-pointer field (`assumed`) is a valid reference only under the
                // `assume_valid_params` opt-in; otherwise leave the loaded pointer with
                // its opaque provenance (sound — accesses through it stay UNKNOWN).
                if *assumed && !self.assume_valid_params {
                    return;
                }
                if *assumed {
                    self.assumptions.insert("param-valid");
                }
                // Field identity: if the reference was loaded from a known field address that
                // resolves to a concrete `(base, offset)` — a tracked region OR an opaque
                // provenance id — reuse the region materialised for that field on an earlier
                // load, so two loads of the same field alias (an in-place `src == dst` through
                // field loads is then recognised). Cleared on heap havoc, so a reassigned
                // field re-materialises.
                let key = src.as_ref().and_then(|s| {
                    let p = self.eval_pointer(s, state);
                    let base = match p.prov {
                        Prov::Region(rid) => RefBase::Region(rid),
                        Prov::Unknown(_, Some(id)) => RefBase::Opaque(id),
                        _ => return None,
                    };
                    self.ctx.as_const(p.offset).map(|o| (base, o.unsigned()))
                });
                // The base object's provenance labels, so a field materialised from a
                // `foreign` object is itself foreign (taint-on-read).
                let src_labels =
                    src.as_ref().map(|s| self.ptr_labels(s, state)).unwrap_or_default();
                // A valid reference to a fresh live region (see `materialize_ref_region`): a
                // known size is refutable, an unknown size (slice/`str`) prove-only.
                let rid = match key.and_then(|k| state.ref_regions.get(&k).copied()) {
                    Some(rid) => rid,
                    None => {
                        let rid = self.materialize_ref_region(*size, *writable, *assumed, state);
                        state.regions[rid].prov_labels.extend(src_labels);
                        if let Some(k) = key {
                            state.ref_regions.insert(k, rid);
                        }
                        rid
                    }
                };
                let zero = self.ctx.int(PTR_WIDTH, 0);
                state.env.insert(
                    *dst,
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Region(rid),
                        offset: zero,
                        align: (*align).max(1) as u64,
                    }),
                );
            }
            Inst::MemIntrinsic { kind, dst, src, len } => {
                self.check_mem_intrinsic((block, idx), *kind, dst, src.as_ref(), len, state);
                // `copy_from_user` fills the destination with untrusted data: mark
                // that region user-controlled, so values later loaded from it are
                // genuine adversarial inputs (a length read back can drive an OOB).
                if matches!(kind, MemKind::UserFill) {
                    if let Prov::Region(rid) = self.eval_pointer(dst, state).prov {
                        if let Some(r) = state.regions.get_mut(rid) {
                            r.user_controlled = true;
                        }
                    }
                    // Double-fetch (TOCTOU): key the USER source address by `(base, concrete
                    // offset)`; a re-fetch of an address already read on this path is a
                    // definite double-fetch — refuted (a value validated on the first read
                    // can differ on the second, since user memory is adversary-controlled).
                    // A symbolic source (no concrete key) cannot be proven must-aliasing, so
                    // no re-fetch is established there — sound (proved, no false FAIL).
                    let dfkey = src.as_ref().and_then(|s| {
                        let sp = self.eval_pointer(s, state);
                        let base = Self::ptr_base_key(&SymValue::Ptr(sp.clone()))?;
                        self.ctx.as_const(sp.offset).map(|o| (base, o.unsigned()))
                    });
                    match dfkey {
                        Some(key) => {
                            let dup = state.user_fetches.contains(&key);
                            self.record_temporal(
                                (block, idx),
                                SafetyProperty::DoubleFetch,
                                dup,
                                state,
                                "no user address is fetched twice on this path",
                                "re-fetches a user address already read on this path (double-fetch TOCTOU)",
                            );
                            state.user_fetches.insert(key);
                        }
                        None => self.record(
                            block,
                            idx,
                            SafetyProperty::DoubleFetch,
                            true,
                            "no user address is fetched twice on this path",
                            "",
                        ),
                    }
                    // The written bytes are untrusted user data; a load from the
                    // now-user-controlled region yields a genuine symbol (see
                    // `load_value`). Leave no stored value to intercept that read,
                    // and keep the path exact — the value is genuinely free, not an
                    // over-approximation. (Just invalidate stale stored values.)
                    state.heap.clear();
        state.unwritten_reads.clear();
        state.ref_regions.clear();
                    return;
                }
                // `copy_to_user` discloses the source buffer to userspace: if it is a
                // freshly-allocated kernel buffer whose copied bytes were never written,
                // that is an information leak (uninitialized heap/stack disclosed). Uses
                // the same unwritten-read machinery as a scalar uninit read: an exact path
                // where the source range has no aliasing store is a definite leak, witnessed.
                if matches!(kind, MemKind::UserDrain) {
                    let exact_before = state.exact;
                    let srcp = self.eval_pointer(dst, state);
                    if exact_before && self.is_fresh_alloc(&srcp, state) {
                        let n = match len {
                            Operand::Const(Const::Int(bv)) => u64::try_from(bv.unsigned()).ok(),
                            _ => None,
                        };
                        if let Some(n) = n.filter(|n| *n > 0) {
                            // Scan the WHOLE copied range (not just the first word): a leak
                            // fires if any chunk is definitely never-written — so a buffer
                            // whose head is written but whose tail is uninitialized (a
                            // too-large `copy_to_user`) is caught, not only a wholly-fresh one.
                            if self.range_has_unwritten_bytes(&srcp, n, state) {
                                if let Some(model) = self.feasibility_witness(state) {
                                    self.record_info_leak(block, idx, model);
                                }
                            }
                        }
                    }
                    // A pure read: nothing to model on the (kernel) side beyond the
                    // obligations already recorded by `check_mem_intrinsic`.
                    return;
                }
                // Model the bulk *write*. Clearing the heap alone is not enough:
                // the destination bytes are now written, and forgetting that made
                // every later load from a fresh alloca a "definite uninitialized
                // read" — a false FAIL on rustc's pervasive aggregate-copy pattern
                // (`store; memcpy; load`).
                let concrete_len = match len {
                    Operand::Const(Const::Int(bv)) => u64::try_from(bv.unsigned()).ok(),
                    _ => None,
                };
                // For a concrete-length copy, forward the source value (read
                // *before* the heap is invalidated): a `Must`-aliasing source
                // store supplies the actually-copied value, keeping the path
                // exact. Anything else yields a fresh unknown.
                let value_ty = Type::int(concrete_len.map_or(64, |n| (n * 8).clamp(8, 128) as u32));
                let forwarded = match (kind, src, concrete_len) {
                    (MemKind::Copy | MemKind::Move, Some(s), Some(n)) => {
                        let sp = self.eval_pointer(s, state);
                        let (v, origin) = self.load_value(&sp, n, &value_ty, state);
                        Some((v, matches!(origin, LoadOrigin::Stored)))
                    }
                    _ => None,
                };
                // A bulk write invalidates the symbolic heap's stored values.
                state.heap.clear();
        state.unwritten_reads.clear();
        state.ref_regions.clear();
                match concrete_len {
                    Some(n) => {
                        let dstp = self.eval_pointer(dst, state);
                        let (value, exact) = forwarded.unwrap_or_else(|| {
                            (self.fresh_value(&value_ty, POrigin::Load), false)
                        });
                        // A fresh stand-in for the written bytes must not feed an
                        // "exact" counterexample witness.
                        if !exact {
                            state.exact = false;
                        }
                        state.heap.push(StoreRecord { target: dstp, value, size: n });
                    }
                    // Unknown extent: the destination is written but no record can
                    // size it soundly — no definite (witnessed) verdicts past here.
                    None => state.exact = false,
                }
            }
            Inst::Intrinsic { dst: None, .. } | Inst::Asm { .. } => {}
        }
    }

    /// Check a `memcpy`/`memmove`/`memset`: the destination must be writable and
    /// in bounds for `len` bytes, and (for copy/move) the source readable and in
    /// bounds for `len` bytes. Each property is recorded as the conjunction over
    /// the touched pointers.
    fn check_mem_intrinsic(
        &mut self,
        at: (BlockId, usize),
        kind: MemKind,
        dst_op: &Operand,
        src_op: Option<&Operand>,
        len_op: &Operand,
        state: &PathState,
    ) {
        use SafetyProperty::*;
        let (block, idx) = at;
        let dst = self.eval_pointer(dst_op, state);
        let len_e = self.eval_scalar(len_op, state);
        let need_src = matches!(kind, MemKind::Copy | MemKind::Move);
        let src = if need_src {
            src_op.map(|s| self.eval_pointer(s, state))
        } else {
            None
        };

        // Snapshot region facts (copied out, so no borrow is held).
        let dst_facts = region_facts(&dst, state);
        let src_facts = src.as_ref().and_then(|p| region_facts(p, state));

        let dst_nn = dst_facts.is_some();
        let src_nn = !need_src || src_facts.is_some();
        self.record(block, idx, NoNullDeref, dst_nn && src_nn, "memcpy pointers are non-null", "a memcpy pointer may be null or have opaque provenance");

        let dst_live = dst_facts.is_some_and(|f| f.live);
        let src_live = !need_src || src_facts.is_some_and(|f| f.live);
        self.record(block, idx, NoUseAfterFree, dst_live && src_live, "memcpy regions are live", "a memcpy region may be freed");

        // In-bounds for the bulk length. Refutable (like `check_access`): on a region
        // whose size cannot wrap, a satisfying `off + len > size` is a genuine OOB, so
        // a user-controlled length overrunning a `copy_from_user`/`memcpy` buffer is a
        // FAIL with a witness. The source (if any) is checked prove-only — a `Refuted`
        // on it would need its own region's no-wrap premise; the destination write is
        // the dominant overflow class and carries the refutation.
        // A narrower length (a `zext i32 %n to i64` the executor kept at its source
        // width) is zero-extended to pointer width, so the bounds arithmetic is
        // width-consistent and the guard on the narrow value still applies.
        let len_e = self.widen_to_ptr(len_e);
        let src_inb = match (need_src, &src, src_facts) {
            (false, _, _) => true,
            (true, Some(p), Some(f)) => self.prove_in_bounds_len(p.offset, len_e, f.size, state),
            _ => false,
        };
        let dst_decision = match dst_region_nowrap(&dst, state) {
            Some((size, nowrap)) if src_inb => {
                let conj = self.in_bounds_len_conjuncts(dst.offset, len_e, size);
                self.decide(&conj, state, RefuteMode::Possible, &[nowrap])
            }
            _ => {
                let ok = dst_facts.is_some_and(|f| self.prove_in_bounds_len(dst.offset, len_e, f.size, state));
                if ok && src_inb { Decision::Proven } else { Decision::Unknown }
            }
        };
        self.record_mem(block, idx, InBounds, dst_decision, "the copy stays within both regions", "could not prove the copy stays in bounds");

        let dst_w = dst_facts.is_some_and(|f| f.perms.write);
        self.record(block, idx, ValidWrite, dst_w, "destination is writable", "destination is not writable");
        if need_src {
            let src_r = src_facts.is_some_and(|f| f.perms.read);
            self.record(block, idx, ValidRead, src_r, "source is readable", "source is not readable");
        }

        // Surface the assumptions the touched regions rest on.
        if dst_nn && src_nn && dst_live && src_live {
            for f in [dst_facts, src_facts].into_iter().flatten() {
                self.assumptions.insert(f.contract.unwrap_or(ALLOC_SUCCEEDS));
            }
        }
    }

    /// Prove `0 <= offset && offset + len <= size` (a `len`-byte access).
    fn prove_in_bounds_len(&mut self, offset: ExprId, len: ExprId, size: ExprId, state: &PathState) -> bool {
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let end = self.ctx.bin(BvOp::Add, offset, len);
        let lower = self.ctx.cmp(SCmp::Sle, zero, offset);
        // No-overflow: the extent `offset + len` must not wrap past 2^63. Without
        // this, a wrapped (negative) `end` satisfies `end <=s size` vacuously, so a
        // pathological huge offset/len would prove "in bounds" — a false PASS. With
        // `offset <=s end` and `end <=s size` (size a real, sub-2^63 region size),
        // `end` is pinned to the non-wrapped range, so it equals the true sum.
        let no_overflow = self.ctx.cmp(SCmp::Sle, offset, end);
        let upper = self.ctx.cmp(SCmp::Sle, end, size);
        self.prove(lower, state) && self.prove(no_overflow, state) && self.prove(upper, state)
    }

    /// Handle a call using the callee's summary: effect-aware heap handling and
    /// a provenance-preserving return binding.
    /// Apply a callee's derived provenance-transfer summary to the actual argument
    /// regions: add each `(arg, label)` to that argument's region, then union each
    /// `(dst, src)` source's labels into the destination's. Mirrors the direct
    /// `ProvLabel`/`ProvPropagate` semantics, one interprocedural step removed.
    fn apply_prov_transfer(&self, prov: &ProvTransfer, argvals: &[SymValue], state: &mut PathState) {
        let region = |i: usize| match argvals.get(i) {
            Some(SymValue::Ptr(p)) => match p.prov {
                Prov::Region(rid) => Some(rid),
                _ => None,
            },
            _ => None,
        };
        for &(a, label) in &prov.labels {
            if let Some(rid) = region(a) {
                if let Some(r) = state.regions.get_mut(rid) {
                    r.prov_labels.insert(label);
                }
            }
        }
        for &(d, s) in &prov.transfers {
            let Some(src) = region(s) else { continue };
            let Some(src_region) = state.regions.get(src) else { continue };
            let src_labels = src_region.prov_labels.clone();
            if src_labels.is_empty() {
                continue;
            }
            if let Some(rid) = region(d) {
                if let Some(r) = state.regions.get_mut(rid) {
                    r.prov_labels.extend(src_labels);
                }
            }
        }
    }

    /// The provenance labels attached to a pointer operand: a materialised region's own
    /// labels, or — for an **opaque pointer** — the labels on its provenance identity
    /// (`Prov::Unknown`'s id, which flows through `gep`/copy). Unifies both channels.
    fn ptr_labels(&mut self, ptr: &Operand, state: &PathState) -> HashSet<u32> {
        match self.eval_pointer(ptr, state).prov {
            Prov::Region(rid) => state.regions.get(rid).map(|r| r.prov_labels.clone()).unwrap_or_default(),
            Prov::Unknown(_, Some(id)) => state.opaque_labels.get(&id).cloned().unwrap_or_default(),
            _ => HashSet::new(),
        }
    }

    /// Attach a provenance label to a pointer operand: its region if it has one, else its
    /// opaque provenance identity (so an opaque parameter — and any field address derived
    /// from it — becomes labelable without being modelled as a region; sound: `opaque_labels`
    /// touch no safety check but the provenance ones).
    fn add_ptr_label(&mut self, ptr: &Operand, label: u32, state: &mut PathState) {
        match self.eval_pointer(ptr, state).prov {
            Prov::Region(rid) => {
                if let Some(r) = state.regions.get_mut(rid) {
                    r.prov_labels.insert(label);
                }
            }
            Prov::Unknown(_, Some(id)) => {
                state.opaque_labels.entry(id).or_default().insert(label);
            }
            _ => {}
        }
    }

    /// The taint labels an r-value's result carries: the **union** of its register operands'
    /// scalar taint (a `tainted` length + 1 is still tainted; a cast/compare of a tainted
    /// value is tainted). Constants are untainted. The propagation rule of the taint lattice.
    fn rvalue_taint(&self, rv: &RValue, state: &PathState) -> HashSet<u32> {
        let ops: Vec<&Operand> = match rv {
            RValue::Use(o) => vec![o],
            RValue::Bin { lhs, rhs, .. } | RValue::Cmp { lhs, rhs, .. } => vec![lhs, rhs],
            RValue::Cast { operand, .. } => vec![operand],
            RValue::Select { cond, then_val, else_val } => vec![cond, then_val, else_val],
        };
        let mut t = HashSet::new();
        for o in ops {
            if let Operand::Reg(r) = o {
                if let Some(s) = state.tainted.get(r) {
                    t.extend(s.iter().copied());
                }
            }
        }
        t
    }

    /// Mark a value operand tainted with `taint`: a pointer taints its region (so bytes read
    /// from it are tainted), a scalar taints its register.
    fn taint_add(&mut self, op: &Operand, taint: u32, state: &mut PathState) {
        if matches!(self.eval_value(op, state), SymValue::Ptr(_)) {
            self.add_ptr_label(op, taint, state);
        } else if let Operand::Reg(r) = op {
            state.tainted.entry(*r).or_default().insert(taint);
        }
    }

    /// Whether a value operand is definitely tainted with `taint` — a scalar register's taint
    /// set, or (for a pointer) its region/opaque provenance labels.
    fn taint_has(&mut self, op: &Operand, taint: u32, state: &PathState) -> bool {
        if let Operand::Reg(r) = op {
            if state.tainted.get(r).is_some_and(|s| s.contains(&taint)) {
                return true;
            }
        }
        matches!(self.eval_value(op, state), SymValue::Ptr(_))
            && match self.eval_pointer(op, state).prov {
                Prov::Region(rid) => {
                    state.regions.get(rid).is_some_and(|r| r.prov_labels.contains(&taint))
                }
                Prov::Unknown(_, Some(id)) => {
                    state.opaque_labels.get(&id).is_some_and(|s| s.contains(&taint))
                }
                _ => false,
            }
    }

    /// Clear `taint` from a value operand (a recognised sanitiser): both its scalar register
    /// taint and, for a pointer, its region/opaque provenance labels.
    fn taint_remove(&mut self, op: &Operand, taint: u32, state: &mut PathState) {
        if let Operand::Reg(r) = op {
            if let Some(s) = state.tainted.get_mut(r) {
                s.remove(&taint);
            }
        }
        if matches!(self.eval_value(op, state), SymValue::Ptr(_)) {
            match self.eval_pointer(op, state).prov {
                Prov::Region(rid) => {
                    if let Some(r) = state.regions.get_mut(rid) {
                        r.prov_labels.remove(&taint);
                    }
                }
                Prov::Unknown(_, Some(id)) => {
                    if let Some(s) = state.opaque_labels.get_mut(&id) {
                        s.remove(&taint);
                    }
                }
                _ => {}
            }
        }
    }


    /// Record a **shared-memory access** for the lockset data-race check (G1): if `ptr`
    /// designates a *shareable* location (a global, or an object reached through a parameter —
    /// a stack local is thread-local and skipped) with a resolvable access class, note
    /// `(class, is_write, lock-classes held)`. The whole-program pass then flags a location
    /// accessed under no common lock, with a write, from ≥2 functions.
    fn record_shared_access(&mut self, ptr: &Operand, is_write: bool, p: &SymPointer, state: &PathState) {
        // Sharedness: a global is definitionally shared; a param-derived opaque object may be
        // shared across threads. A stack/TLS/fresh-heap region is thread-local — skip it.
        let shared = match &p.prov {
            Prov::Region(rid) => {
                matches!(state.regions.get(*rid).map(|r| r.kind), Some(RegionKind::Global))
            }
            Prov::Unknown(_, Some(_)) => true,
            _ => false,
        };
        if !shared {
            return;
        }
        let Some(class) = crate::lockclass::lock_class_of_arg(&self.lock_classes, ptr) else {
            return;
        };
        let mut lockset: Vec<String> = state.held_classes.values().cloned().collect();
        lockset.sort();
        lockset.dedup();
        // Ordered trace for the interleaving check (read=2, write=3), bounded so a huge
        // function does not grow an unbounded trace.
        if self.race_trace.len() < RACE_TRACE_CAP {
            self.race_trace.push((if is_write { 3 } else { 2 }, class.clone()));
        }
        self.race_accesses.insert((class, is_write, lockset));
    }

    /// The identity a typestate resource operand is keyed by: a pointer handle by its base
    /// object, a scalar (an `fd`) by its symbolic value. `None` for a pointer with no tracked
    /// base (then the resource cannot be named — the transition/obligation is skipped, sound).
    fn res_key(&mut self, op: &Operand, state: &PathState) -> Option<ResKey> {
        match self.eval_value(op, state) {
            SymValue::Ptr(_) => Self::ptr_base_key(&self.eval_value(op, state)).map(ResKey::Ptr),
            SymValue::Scalar(e) => Some(ResKey::Val(e)),
        }
    }

    /// Whether two symbolic pointers **alias the same region/identity** and that region's
    /// provenance lacks `cap` — decomposing a `Prov::Select` (a PHI/`select` join) on either
    /// side into its alternatives. Firing on one alternative is sound: that alternative is a
    /// feasible reaching path (the refutation's feasibility witness confirms it) on which the
    /// in-place-foreign write genuinely holds. This is what lets an in-place op whose src is a
    /// PHI of the (in-place) dst and an out-of-place value still be caught on the in-place arm.
    fn alias_lacks_cap(&mut self, sp: &SymPointer, dp: &SymPointer, cap: u32, state: &PathState) -> bool {
        // Decompose a Select on either side (bounded by the finite pointer structure).
        if let Prov::Select { then_ptr, else_ptr, .. } = &sp.prov {
            let (then_ptr, else_ptr) = ((**then_ptr).clone(), (**else_ptr).clone());
            return self.alias_lacks_cap(&then_ptr, dp, cap, state)
                || self.alias_lacks_cap(&else_ptr, dp, cap, state);
        }
        if let Prov::Select { then_ptr, else_ptr, .. } = &dp.prov {
            let (then_ptr, else_ptr) = ((**then_ptr).clone(), (**else_ptr).clone());
            return self.alias_lacks_cap(sp, &then_ptr, cap, state)
                || self.alias_lacks_cap(sp, &else_ptr, cap, state);
        }
        let same = match (&sp.prov, &dp.prov) {
            (Prov::Region(ra), Prov::Region(rb)) => ra == rb,
            // Same opaque object identity, and the two field offsets CAN be equal. The offset
            // is compared by SATISFIABILITY, not structurally: a `req->src` set from a
            // `phi [in-place-dst, out-of-place]` carries an ITE offset that equals the dst
            // offset only on the in-place edge — a structural `==` misses it, but that edge is
            // a genuine reachable in-place write. `record_temporal` gates the FAIL on
            // bug-finding/exact, so this raises recall without a false PASS (and, in strict
            // mode on an inexact merged path, stays UNKNOWN rather than becoming a false FAIL).
            (Prov::Unknown(_, Some(ia)), Prov::Unknown(_, Some(ib))) => {
                ia == ib && self.offsets_can_be_equal(sp.offset, dp.offset, state)
            }
            _ => false,
        };
        if !same {
            return false;
        }
        let labels = match sp.prov {
            Prov::Region(rid) => {
                state.regions.get(rid).map(|r| r.prov_labels.clone()).unwrap_or_default()
            }
            Prov::Unknown(_, Some(id)) => state.opaque_labels.get(&id).cloned().unwrap_or_default(),
            _ => HashSet::new(),
        };
        self.labels_lack_cap(&labels, cap)
    }

    /// The object-identity key of a pointer value: the region or the opaque id it is based
    /// on. `None` for a non-pointer, a null/derived-from-int pointer, or a `Select` join
    /// (ambiguous base) — callers treat `None` conservatively (e.g. drop the store record).
    fn ptr_base_key(v: &SymValue) -> Option<RefBase> {
        match v {
            SymValue::Ptr(p) => match &p.prov {
                Prov::Region(r) => Some(RefBase::Region(*r)),
                Prov::Unknown(_, Some(id)) => Some(RefBase::Opaque(*id)),
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether two offset expressions **can** be equal under the current path (not provably
    /// distinct). A structural match is the fast path; otherwise we ask the solver whether
    /// `a != b` is *unprovable* — if we cannot prove them distinct, an in-place aliasing is a
    /// feasible reaching state. Used only for the in-place capability gate, whose FAIL is
    /// gated on bug-finding/exact by `record_temporal`.
    fn offsets_can_be_equal(&mut self, a: ExprId, b: ExprId, state: &PathState) -> bool {
        if a == b {
            return true;
        }
        let ne = self.ctx.cmp(SCmp::Ne, a, b);
        !self.prove(ne, state)
    }

    /// Whether `labels` contains one that the provenance lattice proves does **not** grant
    /// `cap` (a label absent from the lattice grants everything — the sound default).
    fn labels_lack_cap(&self, labels: &HashSet<u32>, cap: u32) -> bool {
        labels
            .iter()
            .any(|l| self.prov_grants.get(l).is_some_and(|caps| !caps.contains(&cap)))
    }

    /// AA self-deadlock detection (bug-finding). Maintains the per-path set of held
    /// locks by the identity of the lock pointer's base object; re-acquiring a base
    /// already held is a definite deadlock (refuted with a reachability witness). A
    /// release drops the base. Every call records a `DataRace` decision so the
    /// obligation the verifier enumerates (bug-finding only) is never left Open on a
    /// non-lock call. Only external `Callee::Symbol` locks are recognised (the kernel
    /// lock primitives are declarations, not in-TU definitions).
    fn check_lock_call(
        &mut self,
        at: (BlockId, usize),
        callee: &Callee,
        args: &[Operand],
        state: &mut PathState,
    ) {
        let (block, idx) = at;
        let name = match callee {
            Callee::Symbol(n) => n.as_str(),
            _ => {
                self.record(block, idx, SafetyProperty::DataRace, true, "no lock re-acquired while held", "");
                self.record(block, idx, SafetyProperty::SleepInAtomic, true, "no sleeping call while a spinlock is held", "");
                return;
            }
        };
        let base = args.first().map(|a| self.eval_value(a, state)).and_then(|v| Self::ptr_base_key(&v));
        // Sleep-in-atomic: a blocking/sleeping call while a spinlock is *definitely* held is a
        // deadlock/scheduler-corruption bug — refuted with a reachability witness. Every other
        // call records the obligation proven, so it is never left Open.
        if BLOCKING.contains(&name) && !state.spin_held.is_empty() {
            self.record_temporal(
                (block, idx),
                SafetyProperty::SleepInAtomic,
                true,
                state,
                "no sleeping call while a spinlock is held",
                "a call that may sleep runs while a spinlock is held (sleep-in-atomic)",
            );
        } else {
            self.record(block, idx, SafetyProperty::SleepInAtomic, true, "no sleeping call while a spinlock is held", "");
        }
        if LOCK_ACQUIRE.contains(&name) {
            // Lock-order edges (ABBA, G6): name the acquired lock's *class* from its
            // pointer argument, and for every distinct lock class already held on this
            // path emit an ordered edge (held → acquired). A B→A edge somewhere else in
            // the program then closes an ABBA cycle. The base's class is recorded below,
            // so a further nested acquire sees this lock as a predecessor.
            let newclass = args
                .first()
                .and_then(|a| crate::lockclass::lock_class_of_arg(&self.lock_classes, a));
            if let Some(nc) = &newclass {
                for held in state.held_classes.values() {
                    if held != nc {
                        self.lock_edges.insert((held.clone(), nc.clone()));
                    }
                }
                // Ordered interleaving trace: acquire = 0.
                if self.race_trace.len() < RACE_TRACE_CAP {
                    self.race_trace.push((0, nc.clone()));
                }
            }
            match base {
                // Re-acquiring a lock already held on this path: a definite AA deadlock.
                Some(b) if state.locks_held.contains(&b) => {
                    let model = self.feasibility_witness(state);
                    let entry = self.mem.entry((block, idx, SafetyProperty::DataRace)).or_insert(MemAgg {
                        all_proven: true,
                        refutation: None,
                        predicate: "no lock re-acquired while held".to_string(),
                        residual: String::new(),
                    });
                    entry.all_proven = false;
                    if let Some(m) = model {
                        entry.refutation.get_or_insert(m);
                    }
                    entry.residual = "re-acquires a lock already held on this path (AA self-deadlock)".to_string();
                }
                Some(b) => {
                    state.locks_held.insert(b);
                    self.record(block, idx, SafetyProperty::DataRace, true, "no lock re-acquired while held", "");
                }
                // Unknown lock identity: cannot decide — record as proven (a `None`
                // never fabricates a deadlock; it only omits the check). Sound.
                None => self.record(block, idx, SafetyProperty::DataRace, true, "no lock re-acquired while held", ""),
            }
            // Record this lock's class against its base so a nested acquire emits an edge
            // from it, and a matched release drops it.
            if let (Some(b), Some(nc)) = (base, newclass) {
                state.held_classes.insert(b, nc);
            }
            // A **spinning** lock also enters atomic context — track it separately, so a
            // later blocking call is caught (a sleepable `mutex`/`down` is not tracked here).
            if SPIN_ACQUIRE.contains(&name) {
                if let Some(b) = base {
                    state.spin_held.insert(b);
                }
            }
        } else {
            // Any other call: a call handed a held lock's base MAY release it — a matched
            // unlock (`spin_unlock`/`spin_unlock_irqrestore`/…), an unlock wrapper, or a
            // callee that unlocks internally. Conservatively drop every held base passed to
            // this call as a pointer argument, so a later re-acquire is NOT a false
            // double-lock. Sound: this only ever *forgets* a lock (lower recall), never
            // fabricates one — a genuine `lock(l); … lock(l)` with no intervening call
            // taking `l` still refutes.
            for a in args {
                if let Some(b) = Self::ptr_base_key(&self.eval_value(a, state)) {
                    state.locks_held.remove(&b);
                    state.spin_held.remove(&b);
                    // Ordered interleaving trace: release = 1 (recorded for the dropped class).
                    if let Some(cls) = state.held_classes.remove(&b) {
                        if self.race_trace.len() < RACE_TRACE_CAP {
                            self.race_trace.push((1, cls));
                        }
                    }
                }
            }
            self.record(block, idx, SafetyProperty::DataRace, true, "no lock re-acquired while held", "");
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn step_call(
        &mut self,
        at: (BlockId, usize),
        dst: Option<&RegId>,
        callee: &Callee,
        args: &[Operand],
        ret_ty: &Type,
        ret_ref: Option<RefResult>,
        state: &mut PathState,
    ) {
        let (block, idx) = at;
        let argvals: Vec<SymValue> = args.iter().map(|a| self.eval_value(a, state)).collect();
        // Resolve the callee. An indirect call whose target register was devirtualised
        // from a constant ops-struct load (see `global_fnptrs`) is treated as a direct
        // call to that function: its summary gives precise effects (writes/frees/return
        // provenance) instead of the opaque havoc an unknown call would force. Recorded
        // as an assumption — the resolution trusts the constant table's field layout.
        let resolved_fid = match callee {
            Callee::Direct(fid) => Some(*fid),
            Callee::Indirect(Operand::Reg(r)) => {
                let hit = state.fn_ptrs.get(r).copied();
                if hit.is_some() {
                    self.assumptions.insert("devirtualized-indirect-call");
                }
                hit
            }
            _ => None,
        };
        let summary = resolved_fid
            .and_then(|fid| self.summaries.get(&fid).cloned())
            // Whole-program: a cross-file `Symbol(name)` call resolves to the remote
            // callee's summary by name, so its effects are modelled precisely instead
            // of havoc'd. Sound: a name with no summary (a true external / unresolved)
            // still falls through to the opaque havoc below.
            .or_else(|| match callee {
                Callee::Symbol(name) => self.name_summaries.get(name).cloned(),
                _ => None,
            });

        // Double-free through a freeing *wrapper*: a callee that definitely frees its
        // parameter `k` (`Summary.frees_arg`) re-frees a base an earlier freeing call
        // already freed. Done BEFORE `state.exact` is cleared below, so it refutes with a
        // witness on an exact path exactly like a `Dealloc` double-free; then the freed
        // base is recorded. Every other call records `NoDoubleFree` proven, so the
        // per-call obligation is never left Open. (The coarse `frees` havoc below is
        // unchanged, so liveness/PASS is unaffected — this only *adds* a definite check.)
        match summary.as_ref().and_then(|s| s.frees_arg) {
            Some(k) => match argvals.get(k).and_then(Self::ptr_base_key) {
                Some(b) => {
                    let dup = state.freed_bases.contains(&b);
                    self.record_temporal((block, idx), SafetyProperty::NoDoubleFree, dup, state, "no double free through freeing calls", "re-frees a pointer an earlier freeing call already freed");
                    state.freed_bases.insert(b);
                }
                None => self.record(block, idx, SafetyProperty::NoDoubleFree, true, "no double free through freeing calls", ""),
            },
            None => self.record(block, idx, SafetyProperty::NoDoubleFree, true, "no double free through freeing calls", ""),
        }

        // A call is an over-approximation point (havoc'd heap/return unless a
        // precise summary applies); conservatively mark the path inexact so we
        // never refute through a call. Proofs are unaffected (this only gates
        // refutation, not PASS).
        state.exact = false;

        // Effects: a writing or freeing callee invalidates the symbolic heap;
        // a *freeing* callee additionally invalidates region liveness (we do
        // not know which region it freed, so no region's liveness can be proved
        // afterwards). Without this, a use after a freeing call would be a false
        // PASS. A **contracted reference region** (`&[T]`/`&T`/`&mut T`) is
        // *borrowed*, though: the caller holds the borrow for the call's whole
        // duration, so the callee cannot deallocate it — its liveness survives
        // the call. Only *owned* regions (a local `alloc`, `contract == None`)
        // can be moved into and freed by a callee. (Without this a `&[T]` passed
        // to any helper — e.g. `s.is_empty()` — would defeat every later access.)
        // Register-only inline asm (`<inline asm nomem>`, decided from its constraint
        // string by the frontend: no memory clobber, no output memory operand) writes and
        // frees no tracked memory — so it does NOT havoc the heap/provenance, unlike an
        // unknown call. Sound: a memory-clobbering asm keeps the `<inline asm>` marker and
        // the full havoc below.
        let nomem_asm = matches!(callee, Callee::Symbol(n) if n == "<inline asm nomem>");
        let (writes, frees) = if nomem_asm {
            (false, false)
        } else {
            summary.as_ref().map_or((true, true), |s| (s.writes, s.frees))
        };
        if writes || frees {
            // In BUG-FINDING mode, assume an opaque call writes only through the objects
            // reachable from its pointer arguments: preserve store records whose target
            // object is identity-disjoint from every argument (so field provenance set up
            // before an unrelated helper — a refcount warn / atomic-op asm on a *different*
            // object — survives to a later in-place check). This is a recall heuristic
            // (a callee could in principle reach an object via a global or a nested pointer),
            // surfaced as an assumption; strict `verify` keeps the fully-sound havoc.
            if self.bug_finding {
                let arg_bases: HashSet<RefBase> =
                    argvals.iter().filter_map(Self::ptr_base_key).collect();
                let before = state.heap.len();
                state
                    .heap
                    .retain(|rec| Self::ptr_base_key(&SymValue::Ptr(rec.target.clone()))
                        .is_some_and(|b| !arg_bases.contains(&b)));
                if state.heap.len() != before {
                    self.assumptions.insert("opaque-call-writes-through-args-only");
                }
            } else {
                state.heap.clear();
            }
            // The precision caches are conservatively dropped regardless (cheap to rebuild;
            // read-your-writes for the in-place check runs off the store list above).
            state.unwritten_reads.clear();
            state.ref_regions.clear();
        }
        if frees {
            for r in &mut state.regions {
                // A callee can only free *heap* memory it was handed ownership
                // of. Contracted regions are borrowed for the call's duration,
                // and freeing a stack region is UB in the callee — refuted there
                // by `check_dealloc`'s non-heap check (the guarantee this
                // assumption composes with). So a local alloca's liveness
                // survives every call.
                if r.state == LifetimeState::Live
                    && r.contract.is_none()
                    && matches!(r.kind, RegionKind::Heap)
                {
                    r.state = LifetimeState::Freed;
                }
            }
        }

        // Provenance transfer: the callee's summary records how a call moves provenance
        // labels between its pointer arguments (a wrapper around a `sg_set_page`-style
        // primitive, derived without a hand-written contract). Apply it to the actual
        // argument regions, so a foreign element propagates through the wrapper.
        if let Some(prov) = summary.as_ref().map(|s| s.prov.clone()) {
            self.apply_prov_transfer(&prov, &argvals, state);
        }

        if let Some(d) = dst {
            let value = match summary.as_ref().map(|s| &s.ret) {
                Some(RetSummary::PtrFromArg { arg, offset }) => {
                    self.instantiate_ptr(*arg, offset, &argvals, ret_ty)
                }
                Some(RetSummary::Scalar(aff)) => {
                    SymValue::Scalar(self.instantiate_affine(aff, &argvals))
                }
                // No precise summary, but the result type is a reference: it is
                // valid by Rust's type invariant (a safe callee cannot return a
                // dangling `&T`). Materialise a valid-reference region instead of
                // an opaque pointer — the interprocedural counterpart of the
                // by-value-aggregate `RefWitness`.
                None if ret_ref.is_some() => {
                    let RefResult { size, writable } = ret_ref.unwrap_or(RefResult {
                        size: None,
                        writable: false,
                    });
                    let rid = self.materialize_ref_region(size, writable, false, state);
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Region(rid),
                        offset: self.ctx.int(PTR_WIDTH, 0),
                        align: 1,
                    })
                }
                _ => self.fresh_value(ret_ty, POrigin::Call),
            };
            state.env.insert(*d, value);
        }
    }

    /// Create a fresh live region modelling a valid reference (`&T`/`&mut T`):
    /// exact pointee size (refutable) or unknown size (prove-only), readable and
    /// writable per mutability, resting on the `valid-reference` assumption. The
    /// same region shape [`Inst::RefWitness`] builds; returns the region id.
    fn materialize_ref_region(
        &mut self,
        size: Option<u64>,
        writable: bool,
        assumed: bool,
        state: &mut PathState,
    ) -> usize {
        let (size_e, nowrap) = match size {
            Some(n) => {
                let truth = self.ctx.boolean(true);
                (self.ctx.int(PTR_WIDTH, n as u128), Some(truth))
            }
            None => (self.fresh_scalar(PTR_WIDTH), None),
        };
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let nonneg = self.ctx.cmp(SCmp::Sle, zero, size_e);
        state.facts.push(nonneg);
        let rid = state.regions.len();
        state.regions.push(SymRegion {
            kind: RegionKind::Global,
            size: size_e,
            state: LifetimeState::Live,
            perms: Permissions { read: true, write: writable, exec: false },
            contract: Some(VALID_REFERENCE),
            size_nowrap: nowrap,
            sentinel: None,
            user_controlled: false,
            assumed,
            prov_labels: HashSet::new(),
        });
        rid
    }

    /// Rebuild a pointer return value `arg + offset(args)`, keeping `arg`'s
    /// provenance.
    fn instantiate_ptr(
        &mut self,
        arg: usize,
        offset: &Affine,
        argvals: &[SymValue],
        ret_ty: &Type,
    ) -> SymValue {
        match argvals.get(arg) {
            Some(SymValue::Ptr(base)) => {
                let delta = self.instantiate_affine(offset, argvals);
                let new_off = self.ctx.bin(BvOp::Add, base.offset, delta);
                SymValue::Ptr(SymPointer {
                    prov: base.prov.clone(),
                    offset: new_off,
                    align: base.align,
                })
            }
            _ => self.fresh_value(ret_ty, POrigin::Call),
        }
    }

    /// Build the expression `constant + Σ coeff_k · arg_k` in the solver context.
    fn instantiate_affine(&mut self, aff: &Affine, argvals: &[SymValue]) -> ExprId {
        let mut acc = self.const_expr(aff.constant);
        for (&k, &coeff) in &aff.terms {
            let arg = match argvals.get(k) {
                Some(SymValue::Scalar(e)) => *e,
                _ => self.fresh_scalar(PTR_WIDTH),
            };
            let c = self.const_expr(coeff);
            let term = self.ctx.bin(BvOp::Mul, arg, c);
            acc = self.ctx.bin(BvOp::Add, acc, term);
        }
        acc
    }

    /// A signed integer constant as a `PTR_WIDTH` expression (faithful for
    /// negatives via subtraction).
    fn const_expr(&mut self, v: i128) -> ExprId {
        if v >= 0 {
            self.ctx.int(PTR_WIDTH, v as u128)
        } else {
            let zero = self.ctx.int(PTR_WIDTH, 0);
            let mag = self.ctx.int(PTR_WIDTH, (-v) as u128);
            self.ctx.bin(BvOp::Sub, zero, mag)
        }
    }

    // --- obligation decisions ----------------------------------------------

    fn check_access(
        &mut self,
        at: (BlockId, usize),
        p: &SymPointer,
        asize: u64,
        aalign: u64,
        perm_prop: SafetyProperty,
        state: &PathState,
    ) {
        use SafetyProperty::*;
        let (block, idx) = at;

        // A `select`/PHI join: check each alternative under its guard and let the
        // per-obligation records conjoin (an access is safe iff safe on both). The
        // outer offset (any pointer arithmetic done on the join) adds to both.
        if let Prov::Select { cond, then_ptr, else_ptr } = &p.prov {
            let (cond, then_ptr, else_ptr) = (*cond, then_ptr.clone(), else_ptr.clone());
            let ncond = self.ctx.not(cond);
            let outer = p.offset;
            let branch = |ex: &mut Self, sub: &SymPointer| SymPointer {
                prov: sub.prov.clone(),
                offset: ex.ctx.bin(BvOp::Add, sub.offset, outer),
                align: sub.align,
            };
            let pa = branch(self, &then_ptr);
            let pb = branch(self, &else_ptr);
            let mut sa = state.clone();
            sa.pathcond.push(cond);
            let mut sb = state.clone();
            sb.pathcond.push(ncond);
            self.check_access(at, &pa, asize, aalign, perm_prop, &sa);
            self.check_access(at, &pb, asize, aalign, perm_prop, &sb);
            return;
        }

        // Null.
        let non_null = matches!(p.prov, Prov::Region(_));
        self.record(block, idx, NoNullDeref, non_null, "pointer is non-null", "pointer may be null or have opaque provenance");

        let Prov::Region(rid) = p.prov else {
            let residual = p.prov.provenance_residual();
            for prop in [NoUseAfterFree, InBounds, Alignment, perm_prop] {
                self.record(block, idx, prop, false, "requires known provenance", residual);
            }
            return;
        };
        // A stale region id (a dropped-region pointer that reached here via a heap
        // reload / block arg / select branch, past `eval_value`'s sanitization) is
        // treated as unknown provenance instead of indexing out of bounds — sound (the
        // access is left unproven, never a false PASS).
        let Some(region) = state.regions.get(rid) else {
            let residual = Prov::Unknown(POrigin::RegionDrop, None).provenance_residual();
            for prop in [NoUseAfterFree, InBounds, Alignment, perm_prop] {
                self.record(block, idx, prop, false, "requires known provenance", residual);
            }
            return;
        };
        let rstate = region.state;
        let rperms = region.perms;
        let rkind = region.kind;
        let rsize = region.size;
        let contract = region.contract;
        let size_nowrap = region.size_nowrap;
        let region_assumed = region.assumed;

        // Use-after-free: on an exact path a `Freed` region was definitely
        // deallocated, so the access is a certain UAF — refuted with a witness.
        let live = rstate == LifetimeState::Live;
        self.record_temporal((block, idx), NoUseAfterFree, !live, state, "region is live", "region may be freed (use-after-free)");

        // In-bounds: 0 <= offset && offset + asize <= size. Refutable (a real
        // OOB witness) whenever the region's byte size is known not to wrap
        // (concrete, or a symbolic `count * stride` with the recorded
        // `count <= isize::MAX/stride` bound): then a satisfying violation is a
        // genuine reachable OOB, since the only remaining free variable is the
        // access offset and the size cannot be a wrapped too-small value.
        let conjuncts = self.in_bounds_conjuncts(p.offset, asize, rsize);
        let (mut mode, extra) = match size_nowrap {
            Some(fact) => (RefuteMode::Possible, vec![fact]),
            None => (RefuteMode::Off, vec![]),
        };
        // An *assumed* region's size is a caller-supplied guess, not a proven bound
        // (see `SymRegion::assumed`). Refute an OOB against it only when the access
        // offset is actually driven by a genuine adversarial input; a constant offset
        // (`container_of`'s backward step, a fixed field past the guessed size) is an
        // artifact of the guess — reporting it would be a false FAIL.
        if region_assumed && !self.expr_has_genuine_leaf(p.offset) {
            mode = RefuteMode::Off;
        }
        let decision = self.decide(&conjuncts, state, mode, &extra);
        self.record_mem(block, idx, InBounds, decision, "access stays within the allocation", "could not prove the access stays in bounds");

        // Alignment (concrete).
        let aligned = aalign <= 1 || p.align.is_multiple_of(aalign);
        self.record(block, idx, Alignment, aligned, "address meets the required alignment", "could not prove the required alignment");

        // Permission. A write into a region that provably lacks write permission is a
        // real violation. When that region is a definitely read-only GLOBAL — a store
        // into `.rodata` / a `constant` object, which faults at runtime — it is refuted
        // (a FAIL with a witness) like any other definite memory violation. Any other
        // non-writable region (a contract-derived `const`/`readonly` parameter, which C
        // legitimately casts away) stays a prove-only UNKNOWN, so this adds no false FAIL.
        if matches!(perm_prop, ValidWrite) && !rperms.write && matches!(rkind, RegionKind::Global) {
            self.record_temporal(
                (block, idx),
                ValidWrite,
                true,
                state,
                "region grants the write permission",
                "write into a read-only (constant/.rodata) region",
            );
        } else {
            let granted = match perm_prop {
                ValidRead => rperms.read,
                ValidWrite => rperms.write,
                _ => true,
            };
            self.record(block, idx, perm_prop, granted, "region grants the access permission", "region does not grant the access permission");
        }

        if non_null && live {
            self.assumptions.insert(contract.unwrap_or(ALLOC_SUCCEEDS));
        }
    }

    fn check_ptr_arith(&mut self, block: BlockId, idx: usize, p: &SymPointer, state: &PathState) {
        use SafetyProperty::ValidPointerArith;
        // A join: the arithmetic stays in-object iff it does for each alternative
        // under its guard.
        if let Prov::Select { cond, then_ptr, else_ptr } = &p.prov {
            let (cond, then_ptr, else_ptr) = (*cond, then_ptr.clone(), else_ptr.clone());
            let ncond = self.ctx.not(cond);
            let outer = p.offset;
            let branch = |ex: &mut Self, sub: &SymPointer| SymPointer {
                prov: sub.prov.clone(),
                offset: ex.ctx.bin(BvOp::Add, sub.offset, outer),
                align: sub.align,
            };
            let pa = branch(self, &then_ptr);
            let pb = branch(self, &else_ptr);
            let mut sa = state.clone();
            sa.pathcond.push(cond);
            let mut sb = state.clone();
            sb.pathcond.push(ncond);
            self.check_ptr_arith(block, idx, &pa, &sa);
            self.check_ptr_arith(block, idx, &pb, &sb);
            return;
        }
        let Prov::Region(rid) = p.prov else {
            self.record(block, idx, ValidPointerArith, false, "requires known provenance", p.prov.provenance_residual());
            return;
        };
        // A stale region id — a pointer into a region a control-flow merge dropped —
        // whose id now points past this path's `regions`. `eval_value` rewrites such
        // pointers on a register read, but one can still reach here via a heap reload, a
        // block argument, or a `select` branch; treat it as unknown provenance rather
        // than indexing out of bounds. Sound: the arithmetic is left unproven, never a
        // false PASS.
        let Some(region) = state.regions.get(rid) else {
            self.record(block, idx, ValidPointerArith, false, "requires known provenance", Prov::Unknown(POrigin::RegionDrop, None).provenance_residual());
            return;
        };
        let rsize = region.size;
        let contract = region.contract;
        // In-object or one-past-end: 0 <= offset <= size. Refutation off here:
        // the *access* in-bounds check (in `check_access`) is the one that
        // carries the OOB counterexample; the intermediate pointer arithmetic is
        // only proved.
        let conjuncts = self.in_range_conjuncts(p.offset, rsize);
        let decision = self.decide(&conjuncts, state, RefuteMode::Off, &[]);
        let proven = matches!(decision, Decision::Proven);
        self.record_mem(block, idx, ValidPointerArith, decision, "result stays within the object (or one-past-end)", "could not prove the offset stays in-object");
        if proven {
            self.assumptions.insert(contract.unwrap_or(ALLOC_SUCCEEDS));
        }
    }

    fn check_dealloc(&mut self, block: BlockId, idx: usize, p: &SymPointer, state: &mut PathState) {
        use SafetyProperty::NoDoubleFree;
        let Prov::Region(rid) = p.prov else {
            self.record(block, idx, NoDoubleFree, false, "requires known provenance", "freed pointer provenance is not tracked");
            return;
        };
        // A stale (dropped-region) id is treated as unknown provenance, not an OOB index.
        if state.regions.get(rid).is_none() {
            self.record(block, idx, NoDoubleFree, false, "requires known provenance", "freed pointer provenance is not tracked (region dropped at path merge)");
            return;
        }
        if state.regions[rid].contract.is_some() {
            // Freeing caller-owned (borrowed) memory is not ours to prove safe.
            self.record(block, idx, NoDoubleFree, false, "caller-owned region", "freeing a borrowed (caller-owned) region is not provably valid");
            return;
        }
        if !matches!(state.regions[rid].kind, RegionKind::Heap) {
            // Only allocator memory can be deallocated: freeing a stack slot /
            // global / TLS region is UB regardless of its state. This is also
            // the callee-side guarantee behind the caller-side assumption that
            // a call never frees a stack region (see `step_call`) — the pair
            // must stay in sync or the composition is unsound.
            self.record_temporal((block, idx), NoDoubleFree, true, state, "frees allocator memory", "freeing non-heap (stack/global) memory is undefined behaviour");
            return;
        }
        let rstate = state.regions[rid].state;
        if rstate != LifetimeState::Live {
            // On an exact path the region was definitely freed already, so this
            // is a certain double free — refuted with a witness.
            self.record_temporal((block, idx), NoDoubleFree, true, state, "region must be live to free", "region may already be freed (double free)");
            return;
        }
        // Must free the base pointer (offset == 0).
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let goal = self.ctx.cmp(SCmp::Eq, p.offset, zero);
        let at_base = self.prove(goal, state);
        self.record(block, idx, NoDoubleFree, at_base, "frees the base of a live allocation exactly once", "could not prove the freed pointer is the live base");
        if at_base {
            self.assumptions.insert(ALLOC_SUCCEEDS);
            state.regions[rid].state = LifetimeState::Freed;
        }
    }

    /// The conjuncts of in-bounds: `0 <= offset`, no-overflow of the extent, and
    /// `offset + asize <= size`. The middle conjunct (`offset <= offset+asize`)
    /// rules out a wrapped `end` that would satisfy the upper bound vacuously (see
    /// [`Self::prove_in_bounds_len`]).
    fn in_bounds_conjuncts(&mut self, offset: ExprId, asize: u64, size: ExprId) -> [ExprId; 3] {
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let asize_e = self.ctx.int(PTR_WIDTH, asize as u128);
        let end = self.ctx.bin(BvOp::Add, offset, asize_e);
        let lower = self.ctx.cmp(SCmp::Sle, zero, offset);
        let no_overflow = self.ctx.cmp(SCmp::Sle, offset, end);
        let upper = self.ctx.cmp(SCmp::Sle, end, size);
        [lower, no_overflow, upper]
    }

    /// `0 <= offset`, no-overflow, and `offset + len <= size` for a **symbolic**
    /// byte length `len` (a bulk copy). The refutable form of
    /// [`prove_in_bounds_len`].
    fn in_bounds_len_conjuncts(&mut self, offset: ExprId, len: ExprId, size: ExprId) -> [ExprId; 3] {
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let end = self.ctx.bin(BvOp::Add, offset, len);
        let lower = self.ctx.cmp(SCmp::Sle, zero, offset);
        let no_overflow = self.ctx.cmp(SCmp::Sle, offset, end);
        let upper = self.ctx.cmp(SCmp::Sle, end, size);
        [lower, no_overflow, upper]
    }

    /// The goal "the allocation byte size does not overflow the pointer width",
    /// for a size of the form `var * C` (a variable count times a *constant*
    /// element/product `C`). Overflow is exactly `var >u (UINT_MAX / C)`, so the
    /// goal is the constant-bound comparison `var <=u UINT_MAX / C` — no wide
    /// multiply, so the solver discharges it cheaply and can witness a violation.
    ///
    /// Returns `None` (obligation trivially satisfied) when the size is a bare
    /// constant, has no constant factor `> 1`, or has *two or more* variable
    /// factors (`n * m` — a wide multiply this path deliberately does not model;
    /// its overflow, if any, still surfaces downstream as an OOB against the
    /// wrapped region size). Sound: a `None` only ever *omits* a check.
    fn size_overflow_goal(&mut self, size: ExprId) -> Option<ExprId> {
        let factors = self.mul_factors(size);
        let mut c: u128 = 1;
        let mut var: Option<ExprId> = None;
        for f in factors {
            match self.ctx.node(f) {
                Node::Const(bv) => c = c.checked_mul(bv.unsigned())?,
                _ => {
                    // More than one variable factor: not this path's job.
                    if var.replace(f).is_some() {
                        return None;
                    }
                }
            }
        }
        let var = var?;
        if c <= 1 {
            return None;
        }
        let umax = (1u128 << PTR_WIDTH) - 1;
        let bound = self.ctx.int(PTR_WIDTH, umax / c);
        Some(self.ctx.cmp(SCmp::Ule, var, bound))
    }

    /// Flatten a tree of `BvOp::Mul` nodes into its leaf factors (a non-mul is one
    /// factor). So `(n * size) * stride` yields `[n, size, stride]`.
    fn mul_factors(&self, e: ExprId) -> Vec<ExprId> {
        let mut out = Vec::new();
        let mut stack = vec![e];
        while let Some(x) = stack.pop() {
            match self.ctx.node(x) {
                Node::Bin { op: BvOp::Mul, a, b } => {
                    stack.push(*a);
                    stack.push(*b);
                }
                _ => out.push(x),
            }
        }
        out
    }

    /// The fact `count <=u isize::MAX / stride`, so `count * stride` does not
    /// wrap and the byte size is faithful. Sound under `alloc-succeeds` /
    /// `slice-abi` (a successful allocation / valid slice has a size that fits).
    fn size_no_wrap_fact(&mut self, count: ExprId, stride: u64) -> ExprId {
        let max_count = ISIZE_MAX / (stride.max(1) as u128);
        let bound = self.ctx.int(PTR_WIDTH, max_count);
        self.ctx.cmp(SCmp::Ule, count, bound)
    }

    /// The conjuncts of in-range: `0 <= offset` and `offset <= size`
    /// (one-past-end allowed).
    fn in_range_conjuncts(&mut self, offset: ExprId, size: ExprId) -> [ExprId; 2] {
        let zero = self.ctx.int(PTR_WIDTH, 0);
        let lower = self.ctx.cmp(SCmp::Sle, zero, offset);
        let upper = self.ctx.cmp(SCmp::Sle, offset, size);
        [lower, upper]
    }

    /// Decide a (possibly conjunctive) safety goal on one path. Tries to **prove**
    /// it (`A ⟹ P ∧ Q` by proving each conjunct — the linear procedure only takes
    /// conjunctive goals); failing that, on an **exact** path, tries to **refute**
    /// it per `mode` and return a concrete counterexample. `extra` adds premises
    /// used *only* for the refutation query (e.g. a region's no-wrap bound) — not
    /// for proving, which stays cheap.
    fn decide(
        &mut self,
        conjuncts: &[ExprId],
        state: &PathState,
        mode: RefuteMode,
        extra: &[ExprId],
    ) -> Decision {
        if conjuncts.iter().all(|&g| self.prove(g, state)) {
            return Decision::Proven;
        }
        // Refute on an exact path (the strict, always-sound gate) — EXCEPT when the
        // goal is a free choice of an **internal** function's parameter: those are
        // caller-established (the guard lives at the in-module call sites), so a
        // witness picked freely from the parameter space may never occur, exactly as
        // an internal function's pointer contracts are prove-only. A constant OOB in
        // an internal function still refutes (no caller can prevent it). OR, in
        // bug-finding mode, refute on an inexact path when the goal depends only on
        // genuine inputs (see `goal_is_genuine`), so the witness is genuinely reachable.
        let internal_free_param =
            !self.exported && conjuncts.iter().any(|&g| self.goal_has_param(g));
        let gate = (state.exact && !internal_free_param)
            || (self.bug_finding
                && mode == RefuteMode::Possible
                && conjuncts.iter().all(|&g| self.goal_is_genuine(g)));
        if mode != RefuteMode::Off && gate {
            if let Some(model) = self.try_refute(conjuncts, state, mode, extra) {
                return Decision::Refuted(model);
            }
        }
        Decision::Unknown
    }

    /// Whether every symbolic leaf of `goal` is a **genuine input** — a function
    /// parameter (named `arg…`), as opposed to an over-approximated value (loop
    /// havoc / opaque call / undetermined load, all named `?…`, or a global `@…`).
    /// A goal built only from genuine inputs and constants is exactly refutable
    /// even on an over-approximated path: the path condition constrains genuine
    /// inputs only through real branch guards (never dropped by havoc, which only
    /// replaces the values it modifies), so a witness violating such a goal is a
    /// genuinely reachable input. Stateless — the name records the value's origin.
    /// Whether `goal` depends on a bare function parameter (`arg…`) — used to
    /// suppress refuting an *internal* function's access on a freely-chosen
    /// parameter value (caller-constrained). Constants and derived non-parameter
    /// values do not count, so a definite (constant) violation still refutes.
    fn goal_has_param(&self, goal: ExprId) -> bool {
        let mut stack = vec![goal];
        let mut seen: HashSet<ExprId> = HashSet::new();
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            match self.ctx.node(e) {
                Node::Sym { name, .. } if name.starts_with("arg") => return true,
                Node::Sym { .. } | Node::Const(_) | Node::Bool(_) => {}
                Node::Not(a) => stack.push(*a),
                Node::Bin { a, b, .. } | Node::Cmp { a, b, .. } => {
                    stack.push(*a);
                    stack.push(*b);
                }
                Node::And(xs) | Node::Or(xs) => stack.extend(xs.iter().copied()),
                Node::Ite { c, t, e } => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                Node::Zext(v) => stack.push(*v),
            }
        }
        false
    }

    fn goal_is_genuine(&self, goal: ExprId) -> bool {
        let mut stack = vec![goal];
        let mut seen: HashSet<ExprId> = HashSet::new();
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            match self.ctx.node(e) {
                Node::Sym { name, .. } => {
                    // Genuine inputs a witness may freely take: untrusted user data
                    // (`user…`, from `copy_from_user`) and unit-stride counting
                    // inductions (`ind…`, which reach every guard-admitted value) are
                    // always genuine; a parameter (`arg…`) only when the function is
                    // **exported** — an internal function's parameters are supplied by
                    // in-module callers (caller-constrained), so refuting on a freely
                    // chosen value would be a false positive.
                    let genuine = name.starts_with("user")
                        || name.starts_with("ind")
                        || (self.exported && name.starts_with("arg"));
                    if !genuine {
                        return false;
                    }
                }
                Node::Const(_) | Node::Bool(_) => {}
                Node::Not(a) => stack.push(*a),
                Node::Bin { a, b, .. } | Node::Cmp { a, b, .. } => {
                    stack.push(*a);
                    stack.push(*b);
                }
                Node::And(xs) | Node::Or(xs) => stack.extend(xs.iter().copied()),
                Node::Ite { c, t, e } => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                Node::Zext(v) => stack.push(*v),
            }
        }
        true
    }

    /// `true` if `expr` contains **at least one** genuine-input leaf (`user…`, `ind…`,
    /// or — when the function is exported — `arg…`). Unlike [`Explorer::goal_is_genuine`]
    /// (which is vacuously true for a pure constant), this requires the value to
    /// *actually vary* with an adversarial input. Used to keep an assumed region from
    /// refuting a constant-offset access (see `check_access`).
    fn expr_has_genuine_leaf(&self, expr: ExprId) -> bool {
        let mut stack = vec![expr];
        let mut seen: HashSet<ExprId> = HashSet::new();
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            match self.ctx.node(e) {
                Node::Sym { name, .. } => {
                    if name.starts_with("user")
                        || name.starts_with("ind")
                        || (self.exported && name.starts_with("arg"))
                    {
                        return true;
                    }
                }
                Node::Const(_) | Node::Bool(_) => {}
                Node::Not(a) | Node::Zext(a) => stack.push(*a),
                Node::Bin { a, b, .. } | Node::Cmp { a, b, .. } => {
                    stack.push(*a);
                    stack.push(*b);
                }
                Node::And(xs) | Node::Or(xs) => stack.extend(xs.iter().copied()),
                Node::Ite { c, t, e } => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
            }
        }
        false
    }

    /// On an exact path, return a concrete witness of a violation, or `None`.
    ///
    /// - [`RefuteMode::Definite`] refutes only a **definite** violation
    ///   (`assumptions ⟹ ¬goal`, proved bit-precisely): the goal can never hold
    ///   on this path. Used for scalar `SafetyCheck`s, so a merely
    ///   *satisfiable-but-not-valid* check (e.g. an unconstrained `i < 8`) stays
    ///   `Unknown` rather than becoming a FAIL.
    /// - [`RefuteMode::Possible`] refutes whenever **some** reaching input
    ///   violates the goal (`assumptions ∧ ¬goal` is satisfiable). Used for
    ///   memory accesses: the access *executes*, so any reachable input that
    ///   makes it out of bounds is a definite runtime violation. Sound because
    ///   the model satisfies the (exact) path condition, hence is genuinely
    ///   reachable, and callers restrict it to concrete-size regions (so a
    ///   wrapped allocation size can't fabricate a too-small buffer).
    ///
    /// Either way the witness existing also confirms the path is feasible.
    fn try_refute(
        &mut self,
        conjuncts: &[ExprId],
        state: &PathState,
        mode: RefuteMode,
        extra: &[ExprId],
    ) -> Option<Model> {
        let goal = if conjuncts.len() == 1 {
            conjuncts[0]
        } else {
            self.ctx.and(conjuncts.to_vec())
        };
        let not_goal = self.ctx.not(goal);
        let mut assumptions = state.pathcond.clone();
        assumptions.extend_from_slice(&state.facts);
        assumptions.extend_from_slice(extra);
        // For a *definite* refutation, first require that the goal can never hold
        // on this (feasible, exact) path — proved bit-precisely. A *possible*
        // refutation skips this: any satisfiable violation is a real one.
        if mode == RefuteMode::Definite
            && !bitprecise::prove_implies(&self.ctx, &assumptions, not_goal)
        {
            return None;
        }
        // The witness is a model of `assumptions ∧ ¬goal`: it satisfies the path
        // condition (reachable) and falsifies the goal (violating).
        bitprecise::find_counterexample(&self.ctx, &assumptions, goal)
    }

    /// A model of the path condition — a witness that this program point is
    /// genuinely reached. `None` if the path is infeasible (or over-approximated,
    /// outside bug-finding). Used to witness a *definite* temporal violation
    /// (use-after-free / double-free): the region reached `Freed` through an explicit
    /// `Dealloc` on this path and is now accessed, so the violation holds for every
    /// reaching input and the reachability witness *is* the counterexample.
    ///
    /// In **bug-finding mode** the exactness gate is dropped: the free and the access
    /// are structural facts of this path, so an over-approximation elsewhere (an init
    /// loop before the free, an opaque call) does not make the use-after-free any less
    /// real — reporting it accepts the same small path-feasibility risk the mode
    /// trades for recall. Strict verification keeps the exact gate.
    fn feasibility_witness(&mut self, state: &PathState) -> Option<Model> {
        if !state.exact && !self.bug_finding {
            return None;
        }
        let mut assumptions = state.pathcond.clone();
        assumptions.extend_from_slice(&state.facts);
        let never = self.ctx.boolean(false);
        bitprecise::find_counterexample(&self.ctx, &assumptions, never)
    }

    /// Record a temporal obligation (use-after-free / no-double-free) decided
    /// structurally from the region's lifetime state. On an **exact** path a
    /// region only reaches `Freed` through an explicit `Dealloc`, so a violating
    /// state there is a *definite* violation for every reaching input — `Refuted`
    /// with the feasibility witness. Off an exact path (a freeing call/loop only
    /// *may* have freed) it degrades to `Unknown`; a safe state is `Proven`.
    fn record_temporal(
        &mut self,
        at: (BlockId, usize),
        prop: SafetyProperty,
        violated: bool,
        state: &PathState,
        desc: &str,
        residual: &str,
    ) {
        let (block, idx) = at;
        if !violated {
            self.record(block, idx, prop, true, desc, residual);
            return;
        }
        match self.feasibility_witness(state) {
            Some(model) => {
                self.record_mem(block, idx, prop, Decision::Refuted(model), desc, residual)
            }
            None => self.record(block, idx, prop, false, desc, residual),
        }
    }

    /// Try to prove `goal` under the current path. Prefers the bit-precise
    /// procedure (exact, no overflow assumption); only when the proof falls back
    /// to the linear-integer model is `linear-no-overflow` recorded — so a goal
    /// decided bit-precisely yields a `PASS` with one fewer assumption.
    fn prove(&mut self, goal: ExprId, state: &PathState) -> bool {
        let mut assumptions = state.pathcond.clone();
        assumptions.extend_from_slice(&state.facts);
        let key = (assumptions.clone().into_boxed_slice(), goal);
        let method = match self.prove_cache.get(&key) {
            Some(m) => *m,
            None => {
                let m = prove_implies_method(&self.ctx, &assumptions, goal);
                self.prove_cache.insert(key, m);
                m
            }
        };
        match method {
            Some(ProofMethod::BitPrecise) => true,
            Some(ProofMethod::Linear) => {
                self.assumptions.insert(LINEAR_NO_OVERFLOW);
                true
            }
            None => false,
        }
    }

    /// Resolve a load by scanning the symbolic store most-recent-first: a
    /// must-aliasing store supplies the value, a may-aliasing store makes the
    /// value ambiguous (fresh unknown), a no-aliasing store is skipped. This is
    /// what preserves a pointer's provenance across a store/load round-trip.
    /// Resolve a load against the store log, reporting both the value and its
    /// [`LoadOrigin`]. A value not pinned by a `Must`-aliasing store is a fresh
    /// unknown (an over-approximation); the caller drops `exact` for it, since a
    /// violating model could assign that unknown a value memory never holds.
    fn load_value(
        &mut self,
        p: &SymPointer,
        asize: u64,
        ty: &Type,
        state: &mut PathState,
    ) -> (SymValue, LoadOrigin) {
        for k in (0..state.heap.len()).rev() {
            let rec_size = state.heap[k].size;
            let target = state.heap[k].target.clone();
            match self.alias_check(&target, p, rec_size, asize, state) {
                AliasResult::No => continue,
                AliasResult::Must => return (state.heap[k].value.clone(), LoadOrigin::Stored),
                AliasResult::May => return (self.fresh_value(ty, POrigin::Load), LoadOrigin::Uncertain),
            }
        }
        // A load from a user-controlled region (filled by `copy_from_user`) reads
        // untrusted data: a *genuine adversarial input*, so it may drive a refutable
        // overflow. Model a scalar as a genuine symbol (like a parameter) rather than
        // an over-approximated one. Reported as `Stored` so the path stays exact —
        // the value is genuinely free, not an over-approximation to be distrusted.
        let user = matches!(p.prov, Prov::Region(rid) if state.regions.get(rid).is_some_and(|r| r.user_controlled));
        if user && !ty.is_ptr() {
            return (SymValue::Scalar(self.fresh_genuine_scalar(type_width(ty))), LoadOrigin::Stored);
        }
        // Read-consistency: no store aliases this location, so it is unwritten. Two reads of
        // the same never-written `(base, concrete offset, width)` must agree (unwritten memory
        // holds one fixed unknown value). Reuse the value first materialized here; materialize
        // (and cache) it otherwise. Only for a concrete offset — a symbolic offset stays a
        // fresh over-approximation. The cache is dropped on every heap havoc.
        //
        // The base is a region id OR an **opaque object id** (an interior field of a call
        // result / parameter, e.g. `areq->src` and `areq->dst` read twice off the same opaque
        // request) placed in a disjoint id namespace so the two spaces never collide. This is
        // what lets two loads of the same opaque field alias — sound: the returned value is a
        // fresh unknown either way, so read-consistency can only ADD an equality between two
        // reads of one location, never a false PASS (it makes nothing wrongly provable) nor a
        // false FAIL (the two reads genuinely are the same location, hence the same value).
        const OPAQUE_NS: usize = 1 << 48;
        let base = match p.prov {
            Prov::Region(rid) => Some(rid),
            Prov::Unknown(_, Some(id)) => Some((id as usize) | OPAQUE_NS),
            _ => None,
        };
        if let (Some(base), Some(off)) = (base, self.ctx.as_const(p.offset).map(|bv| bv.unsigned())) {
            let key = (base, off, ty.size_bytes(&LAYOUT).unwrap_or(0) as u32);
            if let Some(v) = state.unwritten_reads.get(&key) {
                return (v.clone(), LoadOrigin::Unwritten);
            }
            let v = self.fresh_value(ty, POrigin::Load);
            state.unwritten_reads.insert(key, v.clone());
            return (v, LoadOrigin::Unwritten);
        }
        (self.fresh_value(ty, POrigin::Load), LoadOrigin::Unwritten)
    }

    /// A fresh **genuine** input symbol (named `user…`, treated like a parameter by
    /// [`Explorer::goal_is_genuine`]): an untrusted value an attacker fully controls,
    /// so a violation it drives is genuinely reachable and refutable.
    fn fresh_genuine_scalar(&mut self, width: u32) -> ExprId {
        let name = format!("user{}", self.fresh);
        self.fresh += 1;
        self.ctx.symbol(name, width)
    }

    /// Zero-extend a scalar to pointer width (identity if already that wide) so a
    /// narrower length — a `zext` the executor modelled as width-preserving — takes
    /// part in pointer-width bounds arithmetic without a width mismatch.
    fn widen_to_ptr(&mut self, e: ExprId) -> ExprId {
        self.ctx.zext(e, PTR_WIDTH)
    }

    /// Does `p` point into a freshly-allocated region (one with no caller
    /// contract)? Such a region's bytes are *uninitialized* until written.
    fn is_fresh_alloc(&self, p: &SymPointer, state: &PathState) -> bool {
        match &p.prov {
            Prov::Region(rid) => state.regions.get(*rid).is_some_and(|r| r.contract.is_none()),
            _ => false,
        }
    }

    /// Record a definite read of uninitialized memory as a `ValidRead`
    /// refutation (UB: reading never-written allocated bytes). Overwrites any
    /// permission-worded predicate from `check_access` so the report names the
    /// real cause.
    fn record_uninit_read(&mut self, block: BlockId, idx: usize, model: Model) {
        let entry = self
            .mem
            .entry((block, idx, SafetyProperty::ValidRead))
            .or_insert(MemAgg {
                all_proven: true,
                refutation: None,
                predicate: String::new(),
                residual: String::new(),
            });
        entry.all_proven = false;
        entry.refutation.get_or_insert(model);
        entry.predicate = "reads initialized memory".to_string();
        entry.residual = "reads uninitialized (never-written) freshly-allocated memory".to_string();
    }

    /// Whether the range `[base, base+n)` contains a chunk that **no store definitely
    /// determines** — i.e. some copied byte is uninitialized. Scans in 8-byte words (plus
    /// a byte tail), bounded to a fixed number of chunks so a huge buffer cannot blow up
    /// the check; a `LoadOrigin::Unwritten` chunk (every store `No`-aliases it) is a
    /// definite never-written region. Only *definite* uninit counts (a `May`/`Stored`
    /// chunk does not), so this never fabricates a leak.
    fn range_has_unwritten_bytes(&mut self, base: &SymPointer, n: u64, state: &mut PathState) -> bool {
        const MAX_CHUNKS: u64 = 512; // cap the scan (covers 4 KiB at 8-byte words)
        let word = 8u64;
        let full = n / word;
        let tail = n % word;
        let scanned = full.min(MAX_CHUNKS);
        for k in 0..scanned {
            let delta = self.ctx.int(PTR_WIDTH, (k * word) as u128);
            let off = self.ctx.bin(BvOp::Add, base.offset, delta);
            let p = SymPointer { prov: base.prov.clone(), offset: off, align: 1 };
            let (_, origin) = self.load_value(&p, word, &Type::int(64), state);
            if matches!(origin, LoadOrigin::Unwritten) {
                return true;
            }
        }
        // The sub-word tail (only when the whole-word scan wasn't truncated).
        if tail > 0 && full <= MAX_CHUNKS {
            let delta = self.ctx.int(PTR_WIDTH, (full * word) as u128);
            let off = self.ctx.bin(BvOp::Add, base.offset, delta);
            let p = SymPointer { prov: base.prov.clone(), offset: off, align: 1 };
            let ty = Type::int((tail * 8) as u32);
            let (_, origin) = self.load_value(&p, tail, &ty, state);
            if matches!(origin, LoadOrigin::Unwritten) {
                return true;
            }
        }
        false
    }

    /// Record a `copy_to_user` disclosure of never-written source bytes as a
    /// `NoInfoLeak` refutation (a kernel information leak: uninitialized memory
    /// copied out to userspace).
    fn record_info_leak(&mut self, block: BlockId, idx: usize, model: Model) {
        let entry = self
            .mem
            .entry((block, idx, SafetyProperty::NoInfoLeak))
            .or_insert(MemAgg {
                all_proven: true,
                refutation: None,
                predicate: String::new(),
                residual: String::new(),
            });
        entry.all_proven = false;
        entry.refutation.get_or_insert(model);
        entry.predicate = "copies only initialized bytes to userspace".to_string();
        entry.residual =
            "discloses uninitialized (never-written) kernel memory to userspace".to_string();
    }

    /// Classify the alias relationship between two accesses `a` (`sizea` bytes)
    /// and `b` (`sizeb` bytes) under the current path condition.
    fn alias_check(
        &mut self,
        a: &SymPointer,
        b: &SymPointer,
        sizea: u64,
        sizeb: u64,
        state: &PathState,
    ) -> AliasResult {
        match (&a.prov, &b.prov) {
            // Same allocation: decide by offsets.
            (Prov::Region(r1), Prov::Region(r2)) if r1 == r2 => {
                self.offsets_alias(a, b, sizea, sizeb, state)
            }
            // Distinct allocations never alias.
            (Prov::Region(_), Prov::Region(_)) => AliasResult::No,
            // Same opaque object identity (the unique `Prov::Unknown` id minted per opaque
            // pointer, which flows through `gep`/copy — the same identity `opaque_labels` and
            // `RefBase::Opaque` key on): two accesses to the same opaque object decide by
            // offset exactly like a region, so a field store into an opaque base
            // (`store p, areq->dst`) is read back (`load areq->dst`) — read-your-writes over
            // an opaque object. Sound: an intervening writing call clears the store list
            // (`heap.clear()`), so a stale store is never forwarded across a havoc.
            (Prov::Unknown(_, Some(i1)), Prov::Unknown(_, Some(i2))) if i1 == i2 => {
                self.offsets_alias(a, b, sizea, sizeb, state)
            }
            // Distinct or unidentified opaque / null provenance: be conservative.
            _ => AliasResult::May,
        }
    }

    /// Decide aliasing of two pointers already known to address the **same** object
    /// (same region or same opaque identity) purely by their offsets and access sizes.
    fn offsets_alias(
        &mut self,
        a: &SymPointer,
        b: &SymPointer,
        sizea: u64,
        sizeb: u64,
        state: &PathState,
    ) -> AliasResult {
        let eq = self.ctx.cmp(SCmp::Eq, a.offset, b.offset);
        if sizea >= sizeb && self.prove(eq, state) {
            return AliasResult::Must;
        }
        let asz = self.ctx.int(PTR_WIDTH, sizea as u128);
        let bsz = self.ctx.int(PTR_WIDTH, sizeb as u128);
        let a_end = self.ctx.bin(BvOp::Add, a.offset, asz);
        let b_end = self.ctx.bin(BvOp::Add, b.offset, bsz);
        let a_before_b = self.ctx.cmp(SCmp::Sle, a_end, b.offset);
        let b_before_a = self.ctx.cmp(SCmp::Sle, b_end, a.offset);
        if self.prove(a_before_b, state) || self.prove(b_before_a, state) {
            return AliasResult::No;
        }
        AliasResult::May
    }

    fn record(
        &mut self,
        block: BlockId,
        idx: usize,
        prop: SafetyProperty,
        proven: bool,
        proven_desc: &str,
        residual: &str,
    ) {
        let entry = self.mem.entry((block, idx, prop)).or_insert(MemAgg {
            all_proven: true,
            refutation: None,
            predicate: proven_desc.to_string(),
            residual: residual.to_string(),
        });
        entry.all_proven &= proven;
    }

    /// Record a memory obligation decided as [`Decision`] (carrying a refutation
    /// model when definitely violated).
    fn record_mem(
        &mut self,
        block: BlockId,
        idx: usize,
        prop: SafetyProperty,
        decision: Decision,
        proven_desc: &str,
        residual: &str,
    ) {
        let entry = self.mem.entry((block, idx, prop)).or_insert(MemAgg {
            all_proven: true,
            refutation: None,
            predicate: proven_desc.to_string(),
            residual: residual.to_string(),
        });
        match decision {
            Decision::Proven => {}
            Decision::Unknown => entry.all_proven = false,
            Decision::Refuted(model) => {
                entry.all_proven = false;
                entry.refutation.get_or_insert(model);
            }
        }
    }

    /// Aggregate a scalar `SafetyCheck` decision across paths.
    fn record_scalar(&mut self, block: BlockId, idx: usize, decision: Decision) {
        let entry = self.scalar.entry((block, idx)).or_insert(ScalarAgg {
            all_proven: true,
            refutation: None,
        });
        match decision {
            Decision::Proven => {}
            Decision::Unknown => entry.all_proven = false,
            Decision::Refuted(model) => {
                entry.all_proven = false;
                entry.refutation.get_or_insert(model);
            }
        }
    }

    // --- expression evaluation ---------------------------------------------

    fn eval_value(&mut self, op: &Operand, state: &PathState) -> SymValue {
        match op {
            Operand::Reg(r) => match state.env.get(r) {
                // A pointer into a region that a control-flow merge dropped keeps its old
                // region id, which now points past the end of this path's `regions`.
                // `merge_core` rewrites such pointers held in the environment, but one can
                // still reach a register via the heap/store list, a block argument, or a
                // summary return. Sanitize it to Unknown provenance on read, so every
                // downstream region access (bounds, liveness, dealloc, provenance) sees a
                // valid id or an opaque pointer — never an out-of-range index. Sound: an
                // unknown-provenance pointer is only ever treated conservatively.
                Some(SymValue::Ptr(p))
                    if matches!(p.prov, Prov::Region(rid) if rid >= state.regions.len()) =>
                {
                    SymValue::Ptr(SymPointer {
                        prov: Prov::Unknown(POrigin::RegionDrop, None),
                        offset: p.offset,
                        align: p.align,
                    })
                }
                Some(v) => v.clone(),
                None => SymValue::Scalar(self.fresh_scalar(PTR_WIDTH)),
            },
            Operand::Const(Const::Int(bv)) => SymValue::Scalar(self.ctx.constant(*bv)),
            Operand::Const(Const::Null) => SymValue::Ptr(SymPointer {
                prov: Prov::Null,
                offset: self.ctx.int(PTR_WIDTH, 0),
                align: 1,
            }),
            Operand::Const(Const::Undef) => SymValue::Scalar(self.fresh_scalar(PTR_WIDTH)),
            Operand::Const(Const::Symbol(name)) => match self.global_rids.get(name) {
                Some(&(rid, align)) => SymValue::Ptr(SymPointer {
                    prov: Prov::Region(rid),
                    offset: self.ctx.int(PTR_WIDTH, 0),
                    align,
                }),
                // Not a known global (e.g. a function address): an opaque scalar.
                None => SymValue::Scalar(self.ctx.symbol(format!("@{name}"), PTR_WIDTH)),
            },
            Operand::Const(Const::SymbolOffset(name, off)) => {
                match self.global_rids.get(name) {
                    Some(&(rid, align)) => {
                        let offset = if *off >= 0 {
                            self.ctx.int(PTR_WIDTH, *off as u128)
                        } else {
                            let zero = self.ctx.int(PTR_WIDTH, 0);
                            let mag = self.ctx.int(PTR_WIDTH, (-*off) as u128);
                            self.ctx.bin(BvOp::Sub, zero, mag)
                        };
                        // The interior pointer's alignment is what offset+align
                        // imply, conservatively 1 unless the offset preserves it.
                        let a = if *off >= 0 && (*off as u64).is_multiple_of(align) {
                            align
                        } else {
                            1
                        };
                        SymValue::Ptr(SymPointer { prov: Prov::Region(rid), offset, align: a })
                    }
                    None => SymValue::Scalar(self.fresh_scalar(PTR_WIDTH)),
                }
            }
        }
    }

    fn eval_scalar(&mut self, op: &Operand, state: &PathState) -> ExprId {
        let v = self.eval_value(op, state);
        self.scalarize(v)
    }

    /// A symbolic value as a scalar expression: a pointer of null provenance is
    /// `0`, any other pointer a fresh unknown (its numeric address is unknown).
    fn scalarize(&mut self, v: SymValue) -> ExprId {
        match v {
            SymValue::Scalar(e) => e,
            SymValue::Ptr(p) => match p.prov {
                Prov::Null => self.ctx.int(PTR_WIDTH, 0),
                _ => self.fresh_scalar(PTR_WIDTH),
            },
        }
    }

    /// Evaluate a comparison, treating two **same-allocation** pointer operands
    /// as a comparison of their offsets — so `iter != end` within one allocation
    /// becomes the offset relation the pointer-walk bounds reasoning needs.
    /// Pointers of differing or opaque provenance fall back to fresh scalars
    /// (sound: the result is simply unconstrained).
    fn eval_ptr_aware_cmp(
        &mut self,
        op: CmpOp,
        lhs: &Operand,
        rhs: &Operand,
        state: &PathState,
    ) -> ExprId {
        let lv = self.eval_value(lhs, state);
        let rv = self.eval_value(rhs, state);
        if let (SymValue::Ptr(pa), SymValue::Ptr(pb)) = (&lv, &rv) {
            if let (Prov::Region(ra), Prov::Region(rb)) = (&pa.prov, &pb.prov) {
                if ra == rb {
                    return self.ctx.cmp(map_cmpop(op), pa.offset, pb.offset);
                }
            }
        }
        let a = self.scalarize(lv);
        let b = self.scalarize(rv);
        self.ctx.cmp(map_cmpop(op), a, b)
    }

    fn eval_pointer(&mut self, op: &Operand, state: &PathState) -> SymPointer {
        match self.eval_value(op, state) {
            SymValue::Ptr(p) => p,
            SymValue::Scalar(_) => {
                let cause = match op {
                    Operand::Reg(r) => {
                        self.scalar_ptr_cause.get(r).copied().unwrap_or(ScalarPtrCause::Other)
                    }
                    _ => ScalarPtrCause::Other,
                };
                SymPointer {
                    prov: Prov::Unknown(POrigin::ScalarAsPtr(cause), None),
                    offset: self.ctx.int(PTR_WIDTH, 0),
                    align: 1,
                }
            }
        }
    }

    fn eval_rvalue(&mut self, rv: &RValue, state: &PathState) -> SymValue {
        match rv {
            RValue::Use(op) => self.eval_value(op, state),
            RValue::Bin { op, lhs, rhs } => {
                let a = self.eval_scalar(lhs, state);
                let b = self.eval_scalar(rhs, state);
                SymValue::Scalar(self.ctx.bin(map_binop(*op), a, b))
            }
            RValue::Cmp { op, lhs, rhs } => {
                SymValue::Scalar(self.eval_ptr_aware_cmp(*op, lhs, rhs, state))
            }
            RValue::Cast { op, operand, .. } => match op {
                CastOp::Bitcast => self.eval_value(operand, state),
                CastOp::IntToPtr => SymValue::Ptr(SymPointer {
                    prov: Prov::Unknown(POrigin::IntToPtr, None),
                    offset: self.ctx.int(PTR_WIDTH, 0),
                    align: 1,
                }),
                CastOp::ZExt | CastOp::SExt => match self.eval_value(operand, state) {
                    SymValue::Scalar(e) => SymValue::Scalar(e),
                    SymValue::Ptr(_) => SymValue::Scalar(self.fresh_scalar(PTR_WIDTH)),
                },
                CastOp::Trunc | CastOp::PtrToInt => SymValue::Scalar(self.fresh_scalar(PTR_WIDTH)),
            },
            RValue::Select { cond, then_val, else_val } => {
                let d = self.eval_scalar(cond, state);
                let a = self.eval_value(then_val, state);
                let b = self.eval_value(else_val, state);
                let ty = Type::ptr(Type::Unit); // a hint; `select` builds Prov::Select for ptrs, ite for scalars
                self.select(d, a, b, &ty)
            }
        }
    }

    fn eval_condition(&mut self, cond: &Condition, state: &PathState) -> ExprId {
        match cond {
            Condition::True => self.ctx.boolean(true),
            Condition::Cmp { op, lhs, rhs } => self.eval_ptr_aware_cmp(*op, lhs, rhs, state),
            Condition::And(cs) => {
                let parts = cs.iter().map(|c| self.eval_condition(c, state)).collect();
                self.ctx.and(parts)
            }
            Condition::Or(cs) => {
                let parts = cs.iter().map(|c| self.eval_condition(c, state)).collect();
                self.ctx.or(parts)
            }
            Condition::Not(c) => {
                let inner = self.eval_condition(c, state);
                self.ctx.not(inner)
            }
        }
    }
}

/// Nesting depth of a `Select` provenance (to cap join growth).
fn prov_select_depth(p: &Prov) -> u32 {
    match p {
        Prov::Select { then_ptr, else_ptr, .. } => {
            1 + prov_select_depth(&then_ptr.prov).max(prov_select_depth(&else_ptr.prov))
        }
        _ => 0,
    }
}

/// Follow register-copy chains (`dst = src`, which mem2reg leaves when a promoted
/// load feeds a use) to the underlying register.
fn resolve_copy(mut r: RegId, def: &HashMap<RegId, &Inst>) -> RegId {
    for _ in 0..64 {
        match def.get(&r) {
            Some(Inst::Assign { value: RValue::Use(Operand::Reg(src)), .. }) if *src != r => r = *src,
            _ => break,
        }
    }
    r
}

/// Like [`resolve_copy`], but also strips value-preserving integer widenings
/// (`sext`/`zext`). At `-O0` an `i32` loop counter is sign-extended to `i64` before
/// indexing (`gep i8, p, sext(n)`), so the GEP index is a *cast* of the induction,
/// not a copy. A widening of a non-negative counter preserves its value, so the
/// widened index denotes the same induction for the scan-bound pattern — soundness
/// is retained because the installed bound is stated over the widened value itself
/// (with `0 <= i`), not over the narrow one.
fn resolve_index(mut r: RegId, def: &HashMap<RegId, &Inst>) -> RegId {
    for _ in 0..64 {
        r = resolve_copy(r, def);
        match def.get(&r) {
            Some(Inst::Assign {
                value: RValue::Cast { op: CastOp::SExt | CastOp::ZExt, operand: Operand::Reg(src), .. },
                ..
            }) if *src != r => r = *src,
            _ => break,
        }
    }
    r
}

/// The argument list `pred`'s terminator passes along the edge to `target`
/// (the block-parameter bindings), or `None` if `pred` does not branch there.
fn edge_args(f: &Function, pred: BlockId, target: BlockId) -> Option<&Vec<Operand>> {
    match &f.block(pred)?.term {
        Terminator::Br { target: t, args } if *t == target => Some(args),
        Terminator::CondBr { then_blk, then_args, else_blk, else_args, .. } => {
            if *then_blk == target {
                Some(then_args)
            } else if *else_blk == target {
                Some(else_args)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn type_width(ty: &Type) -> u32 {
    match ty {
        Type::Bool => 1,
        Type::Int { bits } => *bits,
        Type::Ptr { .. } => PTR_WIDTH,
        _ => PTR_WIDTH,
    }
}

/// The facts about the region a pointer points into (copied out so callers hold
/// no borrow on the path state).
#[derive(Clone, Copy)]
struct RegionFacts {
    live: bool,
    size: ExprId,
    perms: Permissions,
    contract: Option<&'static str>,
}

/// If `p` points into a known region whose byte size cannot wrap, return that
/// `(size, no-wrap fact)` — the premise that makes a bulk-copy OOB *refutable* (a
/// satisfying `off + len > size` is then a genuine reachable overrun, not an artifact
/// of a wrapped too-small size). `None` for opaque provenance or an unbounded size.
fn dst_region_nowrap(p: &SymPointer, state: &PathState) -> Option<(ExprId, ExprId)> {
    let Prov::Region(rid) = p.prov else { return None };
    let r = state.regions.get(rid)?;
    r.size_nowrap.map(|nowrap| (r.size, nowrap))
}

fn region_facts(p: &SymPointer, state: &PathState) -> Option<RegionFacts> {
    let Prov::Region(r) = p.prov else {
        return None;
    };
    let reg = &state.regions[r];
    Some(RegionFacts {
        live: reg.state == LifetimeState::Live,
        size: reg.size,
        perms: reg.perms,
        contract: reg.contract,
    })
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a.max(1)
}

fn map_binop(op: BinOp) -> BvOp {
    match op {
        BinOp::Add => BvOp::Add,
        BinOp::Sub => BvOp::Sub,
        BinOp::Mul => BvOp::Mul,
        BinOp::UDiv => BvOp::UDiv,
        BinOp::SDiv => BvOp::SDiv,
        BinOp::URem => BvOp::URem,
        BinOp::SRem => BvOp::SRem,
        BinOp::And => BvOp::And,
        BinOp::Or => BvOp::Or,
        BinOp::Xor => BvOp::Xor,
        BinOp::Shl => BvOp::Shl,
        BinOp::LShr => BvOp::LShr,
        BinOp::AShr => BvOp::AShr,
    }
}

fn map_cmpop(op: CmpOp) -> SCmp {
    match op {
        CmpOp::Eq => SCmp::Eq,
        CmpOp::Ne => SCmp::Ne,
        CmpOp::Ult => SCmp::Ult,
        CmpOp::Ule => SCmp::Ule,
        CmpOp::Ugt => SCmp::Ugt,
        CmpOp::Uge => SCmp::Uge,
        CmpOp::Slt => SCmp::Slt,
        CmpOp::Sle => SCmp::Sle,
        CmpOp::Sgt => SCmp::Sgt,
        CmpOp::Sge => SCmp::Sge,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use csolver_ir::{BasicBlock, FuncId};

    /// `guarded(i, len)`: scalar SafetyCheck `i < len` under guard `i < len`.
    fn guarded() -> Function {
        let i = RegId(0);
        let len = RegId(1);
        let c = RegId(2);
        let mut bb0 = BasicBlock::new(
            BlockId(0),
            Terminator::CondBr {
                cond: Operand::Reg(c),
                then_blk: BlockId(1),
                then_args: vec![],
                else_blk: BlockId(2),
                else_args: vec![],
            },
        );
        bb0.insts.push(Inst::Assign {
            dst: c,
            ty: Type::Bool,
            value: RValue::Cmp {
                op: CmpOp::Ult,
                lhs: Operand::Reg(i),
                rhs: Operand::Reg(len),
            },
        });
        let mut bb1 = BasicBlock::new(BlockId(1), Terminator::Return(None));
        bb1.insts.push(Inst::SafetyCheck {
            property: SafetyProperty::InBounds,
            condition: Condition::Cmp {
                op: CmpOp::Ult,
                lhs: Operand::Reg(i),
                rhs: Operand::Reg(len),
            },
            note: "guard".into(),
        });
        let bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));
        Function {
            id: FuncId(0),
            name: "guarded".into(),
            params: vec![(i, Type::int(64)), (len, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2],
            entry: BlockId(0),
        }
    }

    #[test]
    fn scalar_guarded_check_still_proven() {
        let r = discharge_function(&guarded());
        assert_eq!(r.outcome(BlockId(1), 0), Some(SymOutcome::Proven));
    }

    /// `masked(x)`: `j = x | 8; check j < 8` — always false (definite violation).
    fn masked_check() -> Function {
        let x = RegId(0);
        let j = RegId(1);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Assign {
            dst: j,
            ty: Type::int(64),
            value: RValue::Bin { op: BinOp::Or, lhs: Operand::Reg(x), rhs: Operand::int(64, 8) },
        });
        bb0.insts.push(Inst::SafetyCheck {
            property: SafetyProperty::InBounds,
            condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(j), rhs: Operand::int(64, 8) },
            note: "x|8 < 8".into(),
        });
        Function {
            id: FuncId(0),
            name: "masked".into(),
            params: vec![(x, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn definite_violation_is_refuted_with_model() {
        let r = discharge_function(&masked_check());
        match r.outcome(BlockId(0), 1) {
            Some(SymOutcome::Refuted(model)) => {
                assert!(model.get("arg0").is_some(), "witness names the input: {model:?}");
            }
            other => panic!("expected Refuted, got {other:?}"),
        }
    }

    /// `uninit()`: `buf = alloc i32*4; v = load buf` — read before any write.
    fn uninit() -> Function {
        let buf = RegId(0);
        let v = RegId(1);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(32),
            count: Operand::int(64, 4),
            align: 4,
        });
        bb0.insts.push(Inst::Load { dst: v, ty: Type::int(32), ptr: Operand::Reg(buf), align: 4 });
        Function {
            id: FuncId(0),
            name: "uninit".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn uninitialized_read_is_refuted() {
        // The load (block 0, idx 1) reads a freshly-allocated, never-written
        // region: a definite read of uninitialized memory, refuted as ValidRead.
        let r = discharge_function(&uninit());
        let d = r
            .mem_decision(BlockId(0), 1, SafetyProperty::ValidRead)
            .expect("ValidRead obligation for the load");
        assert!(!d.proven, "an uninitialized read must not be proven");
        assert!(d.refutation.is_some(), "it is refuted with a witness: {d:?}");
    }

    /// `store 7 -> a; memcpy(b, a, 4); load b`: the copy *initializes* `b`, so
    /// the load must not be refuted as an uninitialized read. Before the bulk
    /// write was modelled, the heap was merely cleared and the load looked
    /// never-written — a definite-UB verdict on rustc's pervasive aggregate-copy
    /// pattern (a false FAIL on `Result::map_err` et al.).
    #[test]
    fn memcpy_transfers_initialization() {
        let a = RegId(0);
        let b = RegId(1);
        let v = RegId(2);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        for dst in [a, b] {
            bb0.insts.push(Inst::Alloc {
                dst,
                region: RegionKind::Stack,
                elem: Type::int(32),
                count: Operand::int(64, 1),
                align: 4,
            });
        }
        bb0.insts.push(Inst::Store {
            ty: Type::int(32),
            ptr: Operand::Reg(a),
            value: Operand::int(32, 7),
            align: 4,
        });
        bb0.insts.push(Inst::MemIntrinsic {
            kind: MemKind::Copy,
            dst: Operand::Reg(b),
            src: Some(Operand::Reg(a)),
            len: Operand::int(64, 4),
        });
        bb0.insts.push(Inst::Load { dst: v, ty: Type::int(32), ptr: Operand::Reg(b), align: 4 });
        let f = Function {
            id: FuncId(0),
            name: "copy_init".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let r = discharge_function(&f);
        let d = r
            .mem_decision(BlockId(0), 4, SafetyProperty::ValidRead)
            .expect("ValidRead obligation for the load");
        assert!(
            d.refutation.is_none(),
            "a load of memcpy-initialized bytes must not be refuted: {d:?}"
        );
    }

    /// Allocate an 8-byte kernel buffer, optionally initialize it, then `copy_to_user`
    /// (a `UserDrain`) its bytes. Copying the uninitialized buffer is an information
    /// leak (`NoInfoLeak` refuted); initializing it first must clear the leak.
    fn info_leak_fn(init: bool) -> Function {
        let buf = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 8),
            align: 8,
        });
        if init {
            bb0.insts.push(Inst::MemIntrinsic {
                kind: MemKind::Set,
                dst: Operand::Reg(buf),
                src: None,
                len: Operand::int(64, 8),
            });
        }
        bb0.insts.push(Inst::MemIntrinsic {
            kind: MemKind::UserDrain,
            dst: Operand::Reg(buf),
            src: None,
            len: Operand::int(64, 8),
        });
        Function {
            id: FuncId(0),
            name: "drain".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    /// Two `spin_lock(&l)` on the same lock without an intervening unlock is an AA
    /// self-deadlock; releasing between them (unlock) clears it.
    fn double_lock_fn(unlock_between: bool) -> Function {
        let l = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        // A local lock object so the two acquisitions share a base identity.
        bb0.insts.push(Inst::Alloc {
            dst: l,
            region: RegionKind::Stack,
            elem: Type::int(32),
            count: Operand::int(64, 1),
            align: 4,
        });
        let lock = |b: &mut BasicBlock| b.insts.push(Inst::Call {
            dst: None,
            callee: csolver_ir::Callee::Symbol("spin_lock".into()),
            args: vec![Operand::Reg(l)],
            ret_ty: Type::Unit,
            ret_ref: None,
        });
        lock(&mut bb0);
        if unlock_between {
            bb0.insts.push(Inst::Call {
                dst: None,
                callee: csolver_ir::Callee::Symbol("spin_unlock".into()),
                args: vec![Operand::Reg(l)],
                ret_ty: Type::Unit,
                ret_ref: None,
            });
        }
        lock(&mut bb0);
        Function {
            id: FuncId(0),
            name: "dl".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn double_lock_is_flagged_as_a_deadlock() {
        let f = double_lock_fn(false);
        let limits = ExecLimits { bug_finding: true, exported: true, ..ExecLimits::default() };
        let r = discharge_with(&f, limits);
        // alloc=0, lock=1, lock=2 → the second lock is the deadlock.
        let d = r
            .mem_decision(BlockId(0), 2, SafetyProperty::DataRace)
            .expect("DataRace obligation at the second lock");
        assert!(d.refutation.is_some(), "re-acquiring a held lock must be flagged: {d:?}");
    }

    #[test]
    fn lock_unlock_lock_is_not_a_deadlock() {
        let f = double_lock_fn(true);
        let limits = ExecLimits { bug_finding: true, exported: true, ..ExecLimits::default() };
        let r = discharge_with(&f, limits);
        // alloc=0, lock=1, unlock=2, lock=3 → the last lock is fine.
        let d = r
            .mem_decision(BlockId(0), 3, SafetyProperty::DataRace)
            .expect("DataRace obligation");
        assert!(d.refutation.is_none() && d.proven, "lock/unlock/lock is balanced: {d:?}");
    }

    /// Soundness (no false FAIL): a lock released via an *unrecognized* helper that
    /// takes the lock as an argument must NOT be reported as a double-lock when
    /// re-acquired — the escape-bounded clear drops the base on any call handed it.
    #[test]
    fn lock_then_unlock_via_unknown_helper_then_lock_is_not_a_deadlock() {
        let l = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: l,
            region: RegionKind::Stack,
            elem: Type::int(32),
            count: Operand::int(64, 1),
            align: 4,
        });
        let call = |b: &mut BasicBlock, name: &str| b.insts.push(Inst::Call {
            dst: None,
            callee: csolver_ir::Callee::Symbol(name.into()),
            args: vec![Operand::Reg(l)],
            ret_ty: Type::Unit,
            ret_ref: None,
        });
        call(&mut bb0, "spin_lock"); // 1
        call(&mut bb0, "my_custom_unlock"); // 2 — NOT in LOCK_ACQUIRE, takes l → drops it
        call(&mut bb0, "spin_lock"); // 3 — must NOT be a double-lock
        let f = Function {
            id: FuncId(0),
            name: "dl_helper".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let limits = ExecLimits { bug_finding: true, exported: true, ..ExecLimits::default() };
        let r = discharge_with(&f, limits);
        let d = r
            .mem_decision(BlockId(0), 3, SafetyProperty::DataRace)
            .expect("DataRace obligation");
        assert!(
            d.refutation.is_none() && d.proven,
            "an unlock via an unrecognized helper must clear the lock (no false double-lock): {d:?}"
        );
    }

    #[test]
    fn attacker_controlled_alloc_size_overflow_is_flagged() {
        // buf = alloc [n x i32]: size = n * 4, n attacker-controlled → can wrap.
        let n = RegId(0);
        let buf = RegId(1);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(32),
            count: Operand::Reg(n),
            align: 8,
        });
        let f = Function {
            id: FuncId(0),
            name: "alloc_n_i32".into(),
            params: vec![(n, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let limits = ExecLimits { bug_finding: true, exported: true, ..ExecLimits::default() };
        let r = discharge_with(&f, limits);
        let d = r
            .mem_decision(BlockId(0), 0, SafetyProperty::NoSizeOverflow)
            .expect("NoSizeOverflow obligation at the alloc");
        assert!(
            d.refutation.is_some(),
            "an unbounded attacker-controlled n*sizeof size must be flagged: {d:?}"
        );
    }

    #[test]
    fn bounded_alloc_size_is_not_flagged_as_overflow() {
        // A guarded count (n < 1024) cannot overflow n*4 → the size proves safe.
        let n = RegId(0);
        let ok = RegId(1);
        let buf = RegId(2);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::CondBr {
            cond: Operand::Reg(ok),
            then_blk: BlockId(1),
            then_args: vec![],
            else_blk: BlockId(2),
            else_args: vec![],
        });
        bb0.insts.push(Inst::Assign {
            dst: ok,
            ty: Type::Bool,
            value: RValue::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(n), rhs: Operand::int(64, 1024) },
        });
        let mut bb1 = BasicBlock::new(BlockId(1), Terminator::Return(None));
        bb1.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(32),
            count: Operand::Reg(n),
            align: 8,
        });
        let bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));
        let f = Function {
            id: FuncId(0),
            name: "alloc_bounded".into(),
            params: vec![(n, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2],
            entry: BlockId(0),
        };
        let limits = ExecLimits { bug_finding: true, exported: true, ..ExecLimits::default() };
        let r = discharge_with(&f, limits);
        let d = r
            .mem_decision(BlockId(1), 0, SafetyProperty::NoSizeOverflow)
            .expect("NoSizeOverflow obligation");
        assert!(
            d.refutation.is_none() && d.proven,
            "a count guarded < 1024 cannot overflow n*4: {d:?}"
        );
    }

    #[test]
    fn copy_to_user_of_uninitialized_buffer_is_an_info_leak() {
        let f = info_leak_fn(false);
        let r = discharge_function(&f);
        // The drain is the last instruction (index 1: alloc=0, drain=1).
        let d = r
            .mem_decision(BlockId(0), 1, SafetyProperty::NoInfoLeak)
            .expect("NoInfoLeak obligation for the drain");
        assert!(
            d.refutation.is_some(),
            "copy_to_user of a never-written buffer must be refuted as an info leak: {d:?}"
        );
    }

    #[test]
    fn copy_to_user_with_uninitialized_tail_is_an_info_leak() {
        // 32-byte buffer, only the first 8 bytes written, all 32 copied out → the tail
        // [8,32) is disclosed uninitialized. The single-word check missed this; the
        // whole-range scan must catch it.
        let buf = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 32),
            align: 8,
        });
        bb0.insts.push(Inst::Store {
            ty: Type::int(64),
            ptr: Operand::Reg(buf),
            value: Operand::int(64, 0),
            align: 8,
        });
        bb0.insts.push(Inst::MemIntrinsic {
            kind: MemKind::UserDrain,
            dst: Operand::Reg(buf),
            src: None,
            len: Operand::int(64, 32),
        });
        let f = Function {
            id: FuncId(0),
            name: "drain_tail".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let r = discharge_function(&f);
        let d = r
            .mem_decision(BlockId(0), 2, SafetyProperty::NoInfoLeak)
            .expect("NoInfoLeak obligation for the drain");
        assert!(
            d.refutation.is_some(),
            "copy_to_user of a buffer with an uninitialized tail must be flagged: {d:?}"
        );
    }

    #[test]
    fn copy_to_user_of_initialized_buffer_does_not_leak() {
        let f = info_leak_fn(true);
        let r = discharge_function(&f);
        // alloc=0, memset=1, drain=2.
        if let Some(d) = r.mem_decision(BlockId(0), 2, SafetyProperty::NoInfoLeak) {
            assert!(
                d.refutation.is_none(),
                "a memset-initialized buffer copied out must not be flagged as a leak: {d:?}"
            );
        }
    }

    /// A straight-line function: allocate a 16-byte region, optionally label it with
    /// provenance id 0, then `CapRequire` capability id 1 on it. The `CapRequire` is the
    /// last instruction (index 1 unlabelled, 2 labelled).
    fn cap_func(with_label: bool) -> (Function, usize) {
        let buf = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 16),
            align: 16,
        });
        if with_label {
            bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(buf), label: 0 });
        }
        bb0.insts.push(Inst::CapRequire { ptr: Operand::Reg(buf), cap: 1 });
        let idx = bb0.insts.len() - 1;
        let f = Function {
            id: FuncId(0),
            name: "cap".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        (f, idx)
    }

    fn discharge_with_grants(f: &Function, grants: HashMap<u32, HashSet<u32>>) -> SymbolicReport {
        discharge_with_fields(
            f,
            &HashMap::new(),
            &[],
            &[],
            &HashMap::new(),
            &grants,
            false,
            false,
            false,
        )
    }

    #[test]
    fn capability_violation_on_labelled_region_is_refuted() {
        // Region labelled `foreign` (id 0), which grants nothing; a `CapRequire` for
        // capability `write` (id 1) is therefore a definite violation → FAIL with witness.
        let (f, idx) = cap_func(true);
        let grants = HashMap::from([(0u32, HashSet::new())]);
        let d = discharge_with_grants(&f, grants)
            .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
            .expect("a WriteCapability obligation for the CapRequire")
            .clone();
        assert!(!d.proven, "a label lacking the capability must not be proven");
        assert!(d.refutation.is_some(), "it is refuted with a witness: {d:?}");
    }

    #[test]
    fn capability_granted_by_label_proves() {
        // The same label now grants `write` (id 1) → the requirement holds.
        let (f, idx) = cap_func(true);
        let grants = HashMap::from([(0u32, HashSet::from([1u32]))]);
        let d = discharge_with_grants(&f, grants)
            .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
            .expect("a WriteCapability obligation")
            .clone();
        assert!(d.proven, "a granting label proves the requirement: {d:?}");
    }

    #[test]
    fn capability_on_unlabelled_region_proves() {
        // No label ⇒ the region grants EVERYTHING (the sound default): no false FAIL,
        // even though the grant map withholds the capability from label 0.
        let (f, idx) = cap_func(false);
        let grants = HashMap::from([(0u32, HashSet::new())]);
        let d = discharge_with_grants(&f, grants)
            .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
            .expect("a WriteCapability obligation")
            .clone();
        assert!(d.proven, "an unlabelled region grants all capabilities: {d:?}");
    }

    /// The Copy-Fail flow in miniature: a `foreign` element propagates its provenance into
    /// a container, and a later `require write` on the container is refuted — the container
    /// is only as capable as its least-capable member.
    #[test]
    fn capability_propagates_from_element_into_container() {
        let page = RegId(0);
        let container = RegId(1);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        for dst in [page, container] {
            bb0.insts.push(Inst::Alloc {
                dst,
                region: RegionKind::Heap,
                elem: Type::int(8),
                count: Operand::int(64, 16),
                align: 16,
            });
        }
        // page is `foreign` (label 0); container absorbs page's labels; then require `write`.
        bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(page), label: 0 });
        bb0.insts.push(Inst::ProvPropagate { dst: Operand::Reg(container), src: Operand::Reg(page) });
        bb0.insts.push(Inst::CapRequire { ptr: Operand::Reg(container), cap: 1 });
        let idx = bb0.insts.len() - 1;
        let f = Function {
            id: FuncId(0),
            name: "prop".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        // `foreign` (0) grants read only, not write (1).
        let grants = HashMap::from([(0u32, HashSet::from([2u32]))]);
        let d = discharge_with_grants(&f, grants)
            .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
            .expect("a WriteCapability obligation")
            .clone();
        assert!(!d.proven, "the container inherits the element's foreign provenance");
        assert!(d.refutation.is_some(), "a write to the foreign-tainted container is refuted: {d:?}");
    }

    /// The real algif_aead shape in miniature: the request object is an **opaque** pointer
    /// (an allocator's result, not a tracked region), it is labelled `foreign`, and the same
    /// foreign pointer is stored into two of its fields (`req->src` at +64 and `req->dst` at
    /// +72 — an in-place op). The `require-if-alias-fields` sink reads those fields back and
    /// must refute the write. This exercises read-your-writes over an *opaque base* (the
    /// `alias_check` same-opaque-identity case): without it the field loads return fresh
    /// values, the alias is lost, and the bug is missed.
    #[test]
    fn in_place_write_of_a_foreign_opaque_object_is_refused() {
        let obj = RegId(0); // an opaque pointer parameter (Prov::Unknown)
        let fsrc = RegId(1);
        let fdst = RegId(2);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        // Label the opaque object `foreign` (id 0).
        bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(obj), label: 0 });
        // req->src = obj  (field at +64)
        bb0.insts.push(Inst::PtrOffset {
            dst: fsrc,
            base: Operand::Reg(obj),
            index: Operand::int(64, 64),
            elem: Type::int(8),
        });
        bb0.insts.push(Inst::Store {
            ty: Type::ptr(Type::int(8)),
            ptr: Operand::Reg(fsrc),
            value: Operand::Reg(obj),
            align: 8,
        });
        // req->dst = obj  (field at +72) — same pointer ⇒ in-place
        bb0.insts.push(Inst::PtrOffset {
            dst: fdst,
            base: Operand::Reg(obj),
            index: Operand::int(64, 72),
            elem: Type::int(8),
        });
        bb0.insts.push(Inst::Store {
            ty: Type::ptr(Type::int(8)),
            ptr: Operand::Reg(fdst),
            value: Operand::Reg(obj),
            align: 8,
        });
        // Sink: read req->src (+64) and req->dst (+72) back; iff they alias, require `write` (1).
        bb0.insts.push(Inst::CapRequireIfAliasFields {
            obj: Operand::Reg(obj),
            off_a: 64,
            off_b: 72,
            cap: 1,
        });
        let idx = bb0.insts.len() - 1;
        let f = Function {
            id: FuncId(0),
            name: "inplace_opaque".into(),
            params: vec![(obj, Type::ptr(Type::int(8)))],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        // `foreign` (0) grants read (2) only, not write (1).
        let grants = HashMap::from([(0u32, HashSet::from([2u32]))]);
        let d = discharge_with_grants(&f, grants)
            .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
            .expect("a WriteCapability obligation")
            .clone();
        assert!(!d.proven, "the in-place write of a foreign opaque object is refuted: {d:?}");
        assert!(d.refutation.is_some(), "read-your-writes over the opaque base found the alias: {d:?}");
    }

    /// COPY-FAIL DIAGNOSIS, suspect 3 — a DERIVED pointer. The real IR stores
    /// `%143 = gep %87+K` (a field pointer derived from the opaque object), not the
    /// object itself, into req->src and req->dst. Does the derived pointer still carry
    /// `foreign` and alias itself when read back? Expect: still refuted (fires).
    #[test]
    fn diag_copyfail_3_derived_pointer_in_place() {
        let obj = RegId(0);
        let p = RegId(1);
        let fsrc = RegId(2);
        let fdst = RegId(3);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(obj), label: 0 });
        bb0.insts.push(Inst::PtrOffset { dst: p, base: Operand::Reg(obj), index: Operand::int(64, 16), elem: Type::int(8) });
        bb0.insts.push(Inst::PtrOffset { dst: fsrc, base: Operand::Reg(obj), index: Operand::int(64, 64), elem: Type::int(8) });
        bb0.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fsrc), value: Operand::Reg(p), align: 8 });
        bb0.insts.push(Inst::PtrOffset { dst: fdst, base: Operand::Reg(obj), index: Operand::int(64, 72), elem: Type::int(8) });
        bb0.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fdst), value: Operand::Reg(p), align: 8 });
        bb0.insts.push(Inst::CapRequireIfAliasFields { obj: Operand::Reg(obj), off_a: 64, off_b: 72, cap: 1 });
        let idx = bb0.insts.len() - 1;
        let f = Function {
            id: FuncId(0),
            name: "diag3".into(),
            params: vec![(obj, Type::ptr(Type::int(8)))],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let grants = HashMap::from([(0u32, HashSet::from([2u32]))]);
        let d = discharge_with_grants(&f, grants)
            .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
            .expect("a WriteCapability obligation")
            .clone();
        assert!(!d.proven && d.refutation.is_some(), "a derived foreign pointer stored in-place is refuted: {d:?}");
    }

    /// SOUNDNESS GUARD for the satisfiability-based offset alias (Fix 2): the OUT-OF-PLACE
    /// (patched) shape — req->src and req->dst hold DIFFERENT, provably-distinct field
    /// offsets of the same foreign object — must NOT fire. If the possible-alias check over-
    /// fired, this would be a false FAIL on patched code.
    #[test]
    fn out_of_place_distinct_fields_do_not_fire() {
        let obj = RegId(0);
        let p1 = RegId(1); // gep obj+16
        let p2 = RegId(2); // gep obj+32  (distinct from p1)
        let fsrc = RegId(3);
        let fdst = RegId(4);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(obj), label: 0 });
        bb0.insts.push(Inst::PtrOffset { dst: p1, base: Operand::Reg(obj), index: Operand::int(64, 16), elem: Type::int(8) });
        bb0.insts.push(Inst::PtrOffset { dst: p2, base: Operand::Reg(obj), index: Operand::int(64, 32), elem: Type::int(8) });
        bb0.insts.push(Inst::PtrOffset { dst: fsrc, base: Operand::Reg(obj), index: Operand::int(64, 64), elem: Type::int(8) });
        bb0.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fsrc), value: Operand::Reg(p1), align: 8 });
        bb0.insts.push(Inst::PtrOffset { dst: fdst, base: Operand::Reg(obj), index: Operand::int(64, 72), elem: Type::int(8) });
        bb0.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fdst), value: Operand::Reg(p2), align: 8 });
        bb0.insts.push(Inst::CapRequireIfAliasFields { obj: Operand::Reg(obj), off_a: 64, off_b: 72, cap: 1 });
        let idx = bb0.insts.len() - 1;
        let f = Function {
            id: FuncId(0),
            name: "outofplace".into(),
            params: vec![(obj, Type::ptr(Type::int(8)))],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let grants = HashMap::from([(0u32, HashSet::from([2u32]))]);
        for bugf in [false, true] {
            let d = discharge_with_fields(
                &f, &HashMap::new(), &[], &[], &HashMap::new(), &grants, bugf, false, false,
            )
            .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
            .expect("a WriteCapability obligation")
            .clone();
            assert!(d.refutation.is_none(), "distinct (out-of-place) fields must NOT be refuted (bug_finding={bugf}): {d:?}");
        }
    }

    /// COPY-FAIL DIAGNOSIS, suspect 1 — a PHI on the src value. The real IR sets
    /// `req->src = phi [%143 (in-place), %190 (out-of-place)]` and `req->dst = %143`. On
    /// the in-place path src == dst == foreign ⇒ must refute. Tests whether the block-arg
    /// merge (a `Prov::Select` at the join) preserves the in-place aliasing/foreign label.
    #[test]
    fn diag_copyfail_1_phi_on_src() {
        let obj = RegId(0);
        let c = RegId(1); // nondeterministic condition
        let p143 = RegId(2); // in-place value: derived from obj
        let other = RegId(3); // out-of-place value: a distinct tracked region
        let src = RegId(4); // the phi (merge block param)
        let fsrc = RegId(5);
        let fdst = RegId(6);
        let mut bb0 = BasicBlock::new(
            BlockId(0),
            Terminator::CondBr {
                cond: Operand::Reg(c),
                then_blk: BlockId(1),
                then_args: vec![Operand::Reg(p143)],
                else_blk: BlockId(1),
                else_args: vec![Operand::Reg(other)],
            },
        );
        bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(obj), label: 0 });
        bb0.insts.push(Inst::PtrOffset { dst: p143, base: Operand::Reg(obj), index: Operand::int(64, 16), elem: Type::int(8) });
        bb0.insts.push(Inst::Alloc { dst: other, region: RegionKind::Heap, elem: Type::int(8), count: Operand::int(64, 16), align: 16 });
        let mut bb1 = BasicBlock::new(BlockId(1), Terminator::Return(None));
        bb1.params = vec![(src, Type::ptr(Type::int(8)))];
        bb1.insts.push(Inst::PtrOffset { dst: fsrc, base: Operand::Reg(obj), index: Operand::int(64, 64), elem: Type::int(8) });
        bb1.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fsrc), value: Operand::Reg(src), align: 8 });
        bb1.insts.push(Inst::PtrOffset { dst: fdst, base: Operand::Reg(obj), index: Operand::int(64, 72), elem: Type::int(8) });
        bb1.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fdst), value: Operand::Reg(p143), align: 8 });
        bb1.insts.push(Inst::CapRequireIfAliasFields { obj: Operand::Reg(obj), off_a: 64, off_b: 72, cap: 1 });
        let idx = bb1.insts.len() - 1;
        let f = Function {
            id: FuncId(0),
            name: "diag1".into(),
            params: vec![(obj, Type::ptr(Type::int(8))), (c, Type::int(1))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1],
            entry: BlockId(0),
        };
        let grants = HashMap::from([(0u32, HashSet::from([2u32]))]);
        let d = discharge_with_grants(&f, grants)
            .mem_decision(BlockId(1), idx, SafetyProperty::WriteCapability)
            .expect("a WriteCapability obligation")
            .clone();
        // Strict mode: the two-way merge marks the path inexact, so the (correctly found)
        // refutation is soundly downgraded to UNKNOWN — never proven (no false PASS).
        assert!(!d.proven, "the phi merge never proves the in-place write safe: {d:?}");
        assert!(d.refutation.is_none(), "strict mode downgrades the merged-path refutation to UNKNOWN: {d:?}");

        // Bug-finding mode (the real kernel scan mode): the refutation stands — the merge's
        // `Prov::Select` is decomposed and the in-place foreign alternative refutes. So the
        // PHI is NOT what blocks the real algif_aead (which PASSes, a mode no synthetic hits).
        let grants2 = HashMap::from([(0u32, HashSet::from([2u32]))]);
        let d2 = discharge_with_fields(
            &f, &HashMap::new(), &[], &[], &HashMap::new(), &grants2, true, false, false,
        )
        .mem_decision(BlockId(1), idx, SafetyProperty::WriteCapability)
        .expect("a WriteCapability obligation")
        .clone();
        assert!(!d2.proven && d2.refutation.is_some(), "bug-finding mode refutes the phi in-place write: {d2:?}");
    }

    /// COPY-FAIL DIAGNOSIS, suspect 1b — a pointer passed through a SINGLE-EDGE block
    /// parameter (no two-way merge). Distinguishes "block-arg pointer passing loses
    /// identity" from "only the two-predecessor merge loses it". Expect: still refuted.
    #[test]
    fn diag_copyfail_1b_single_edge_blockparam() {
        let obj = RegId(0);
        let p143 = RegId(1);
        let src = RegId(2); // block param, bound to p143 by the single incoming edge
        let fsrc = RegId(3);
        let fdst = RegId(4);
        let mut bb0 = BasicBlock::new(
            BlockId(0),
            Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(p143)] },
        );
        bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(obj), label: 0 });
        bb0.insts.push(Inst::PtrOffset { dst: p143, base: Operand::Reg(obj), index: Operand::int(64, 16), elem: Type::int(8) });
        let mut bb1 = BasicBlock::new(BlockId(1), Terminator::Return(None));
        bb1.params = vec![(src, Type::ptr(Type::int(8)))];
        bb1.insts.push(Inst::PtrOffset { dst: fsrc, base: Operand::Reg(obj), index: Operand::int(64, 64), elem: Type::int(8) });
        bb1.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fsrc), value: Operand::Reg(src), align: 8 });
        bb1.insts.push(Inst::PtrOffset { dst: fdst, base: Operand::Reg(obj), index: Operand::int(64, 72), elem: Type::int(8) });
        bb1.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fdst), value: Operand::Reg(p143), align: 8 });
        bb1.insts.push(Inst::CapRequireIfAliasFields { obj: Operand::Reg(obj), off_a: 64, off_b: 72, cap: 1 });
        let idx = bb1.insts.len() - 1;
        let f = Function {
            id: FuncId(0),
            name: "diag1b".into(),
            params: vec![(obj, Type::ptr(Type::int(8)))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1],
            entry: BlockId(0),
        };
        let grants = HashMap::from([(0u32, HashSet::from([2u32]))]);
        let d = discharge_with_grants(&f, grants)
            .mem_decision(BlockId(1), idx, SafetyProperty::WriteCapability)
            .expect("a WriteCapability obligation")
            .clone();
        assert!(!d.proven && d.refutation.is_some(), "a pointer through a single-edge block param still refutes: {d:?}");
    }

    /// COPY-FAIL DIAGNOSIS, suspect 2 — the sink object is a NESTED field of the opaque
    /// base. The real IR's `crypto_aead_encrypt(%193)` has `%193 = gep %87 field9` (the
    /// embedded request), and the src/dst stores + the sink's +64/+72 are all relative to
    /// `%193`, i.e. `%87 + off(field9) + {64,72}`. This mirrors the real shape exactly:
    /// obj is opaque+foreign, reqbase = gep obj+128, and everything hangs off reqbase.
    /// Expect: still refuted (the real case PASSes, so if THIS one PASSes, the nested base
    /// is the blocker).
    #[test]
    fn diag_copyfail_2_nested_request_base() {
        let obj = RegId(0);
        let reqbase = RegId(1); // = gep obj + 128  (the embedded request, like %193)
        let p = RegId(2); // the foreign scatterlist pointer, derived from obj (like %143)
        let fsrc = RegId(3);
        let fdst = RegId(4);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::ProvLabel { ptr: Operand::Reg(obj), label: 0 });
        bb0.insts.push(Inst::PtrOffset { dst: reqbase, base: Operand::Reg(obj), index: Operand::int(64, 128), elem: Type::int(8) });
        bb0.insts.push(Inst::PtrOffset { dst: p, base: Operand::Reg(obj), index: Operand::int(64, 16), elem: Type::int(8) });
        // req->src = p  (reqbase + 64)
        bb0.insts.push(Inst::PtrOffset { dst: fsrc, base: Operand::Reg(reqbase), index: Operand::int(64, 64), elem: Type::int(8) });
        bb0.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fsrc), value: Operand::Reg(p), align: 8 });
        // req->dst = p  (reqbase + 72)
        bb0.insts.push(Inst::PtrOffset { dst: fdst, base: Operand::Reg(reqbase), index: Operand::int(64, 72), elem: Type::int(8) });
        bb0.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(fdst), value: Operand::Reg(p), align: 8 });
        // sink on the NESTED base reqbase, offsets 64/72
        bb0.insts.push(Inst::CapRequireIfAliasFields { obj: Operand::Reg(reqbase), off_a: 64, off_b: 72, cap: 1 });
        let idx = bb0.insts.len() - 1;
        let f = Function {
            id: FuncId(0),
            name: "diag2".into(),
            params: vec![(obj, Type::ptr(Type::int(8)))],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let grants = HashMap::from([(0u32, HashSet::from([2u32]))]);
        // Fires in both modes — a nested request base (sink object = gep of the opaque base)
        // read-your-writes and aliases correctly. So the nested base is NOT the blocker.
        for bugf in [false, true] {
            let d = discharge_with_fields(
                &f, &HashMap::new(), &[], &[], &HashMap::new(), &grants, bugf, false, false,
            )
            .mem_decision(BlockId(0), idx, SafetyProperty::WriteCapability)
            .expect("a WriteCapability obligation")
            .clone();
            assert!(!d.proven && d.refutation.is_some(), "nested-base in-place write refuted (bug_finding={bugf}): {d:?}");
        }
    }

    /// `init()`: `buf = alloc i32*4; store 7 -> buf; v = load buf` — read after
    /// write, so the load reads an initialized value.
    fn init() -> Function {
        let buf = RegId(0);
        let v = RegId(1);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(32),
            count: Operand::int(64, 4),
            align: 4,
        });
        bb0.insts.push(Inst::Store {
            ty: Type::int(32),
            ptr: Operand::Reg(buf),
            value: Operand::int(32, 7),
            align: 4,
        });
        bb0.insts.push(Inst::Load { dst: v, ty: Type::int(32), ptr: Operand::Reg(buf), align: 4 });
        Function {
            id: FuncId(0),
            name: "init".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn initialized_read_is_not_flagged() {
        // The store `Must`-aliases the load, so the value is determined and the
        // definedness check does not fire (no refutation).
        let r = discharge_function(&init());
        let d = r
            .mem_decision(BlockId(0), 2, SafetyProperty::ValidRead)
            .expect("ValidRead obligation for the load");
        assert!(d.proven, "a read after write is proven: {d:?}");
        assert!(d.refutation.is_none(), "no refutation for an initialized read: {d:?}");
    }

    /// `bare(x)`: `check x < 8` — satisfiable but not valid, so NOT refuted.
    fn bare_check() -> Function {
        let x = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::SafetyCheck {
            property: SafetyProperty::InBounds,
            condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(x), rhs: Operand::int(64, 8) },
            note: "x < 8".into(),
        });
        Function {
            id: FuncId(0),
            name: "bare".into(),
            params: vec![(x, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn satisfiable_but_invalid_check_stays_unknown() {
        // `x < 8` holds for some inputs and fails for others — never refuted.
        let r = discharge_function(&bare_check());
        assert_eq!(r.outcome(BlockId(0), 0), Some(SymOutcome::Unknown));
    }

    /// `unguarded(i)`: `buf = alloc i32*8; store 0 -> buf+i` — OOB for i >= 8.
    fn unguarded_store() -> Function {
        let i = RegId(0);
        let buf = RegId(1);
        let p = RegId(2);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(32),
            count: Operand::int(64, 8),
            align: 4,
        });
        bb0.insts.push(Inst::PtrOffset {
            dst: p,
            base: Operand::Reg(buf),
            index: Operand::Reg(i),
            elem: Type::int(32),
        });
        bb0.insts.push(Inst::Store {
            ty: Type::int(32),
            ptr: Operand::Reg(p),
            value: Operand::int(32, 0),
            align: 4,
        });
        Function {
            id: FuncId(0),
            name: "unguarded".into(),
            params: vec![(i, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn concrete_size_oob_memory_access_is_refuted() {
        let r = discharge_function(&unguarded_store());
        let d = r
            .mem_decision(BlockId(0), 2, SafetyProperty::InBounds)
            .expect("in-bounds obligation exists");
        assert!(!d.proven, "an unguarded OOB write is not provable");
        let model = d.refutation.as_ref().expect("refuted with a counterexample");
        assert!(model.get("arg0").is_some(), "witness names the index: {model:?}");
    }

    /// `store_buf(i, n)`: alloc n i32; if 0<=i { if i<n { store buf[i] } }.
    fn store_buf() -> Function {
        let i = RegId(0);
        let n = RegId(1);
        let buf = RegId(2);
        let c0 = RegId(3);
        let c1 = RegId(4);
        let p = RegId(5);

        let mut bb0 = BasicBlock::new(
            BlockId(0),
            Terminator::CondBr {
                cond: Operand::Reg(c0),
                then_blk: BlockId(1),
                then_args: vec![],
                else_blk: BlockId(3),
                else_args: vec![],
            },
        );
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(32),
            count: Operand::Reg(n),
            align: 4,
        });
        bb0.insts.push(Inst::Assign {
            dst: c0,
            ty: Type::Bool,
            value: RValue::Cmp {
                op: CmpOp::Sle,
                lhs: Operand::int(64, 0),
                rhs: Operand::Reg(i),
            },
        });

        let mut bb1 = BasicBlock::new(
            BlockId(1),
            Terminator::CondBr {
                cond: Operand::Reg(c1),
                then_blk: BlockId(2),
                then_args: vec![],
                else_blk: BlockId(3),
                else_args: vec![],
            },
        );
        bb1.insts.push(Inst::Assign {
            dst: c1,
            ty: Type::Bool,
            value: RValue::Cmp {
                op: CmpOp::Slt,
                lhs: Operand::Reg(i),
                rhs: Operand::Reg(n),
            },
        });

        let mut bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));
        bb2.insts.push(Inst::PtrOffset {
            dst: p,
            base: Operand::Reg(buf),
            index: Operand::Reg(i),
            elem: Type::int(32),
        });
        bb2.insts.push(Inst::Store {
            ty: Type::int(32),
            ptr: Operand::Reg(p),
            value: Operand::int(32, 0),
            align: 4,
        });

        let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

        Function {
            id: FuncId(0),
            name: "store_buf".into(),
            params: vec![(i, Type::int(64)), (n, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2, bb3],
            entry: BlockId(0),
        }
    }

    #[test]
    fn guarded_store_proves_all_memory_checks() {
        let f = store_buf();
        let r = discharge_function(&f);
        assert!(!r.truncated);
        // The store is at bb2 index 1; all five obligations must be proven.
        for prop in [
            SafetyProperty::NoNullDeref,
            SafetyProperty::NoUseAfterFree,
            SafetyProperty::InBounds,
            SafetyProperty::Alignment,
            SafetyProperty::ValidWrite,
        ] {
            let d = r.mem_decision(BlockId(2), 1, prop).expect("decided");
            assert!(d.proven, "{prop} should be proven, got residual: {}", d.residual);
        }
        // PtrOffset at bb2 index 0: valid pointer arithmetic.
        let arith = r
            .mem_decision(BlockId(2), 0, SafetyProperty::ValidPointerArith)
            .expect("decided");
        assert!(arith.proven, "pointer arithmetic: {}", arith.residual);
    }

    #[test]
    fn truncated_exploration_reports_no_memory_decision() {
        // Soundness positive control for the truncation rule. When exploration
        // hits its visit budget, the report is `{ truncated: true, ..default }` —
        // every decision map empty — so each memory op falls back to `Open` and the
        // function can never PASS on an unanalysed access. (This is the property the
        // scaling sweep's "truncated" residual bucket rests on; the sweep happens to
        // show 0 truncations today, but the guarantee must hold for the ones it will
        // eventually hit, so it is pinned here rather than assumed.) A 1-visit budget
        // truncates this 4-block function before it reaches the store at bb2.
        let f = store_buf();
        let r = discharge_with(&f, crate::ExecLimits { max_visits: 1, ..Default::default() });
        assert!(r.truncated, "a 1-visit budget must truncate a 4-block function");
        for prop in [
            SafetyProperty::NoNullDeref,
            SafetyProperty::NoUseAfterFree,
            SafetyProperty::InBounds,
            SafetyProperty::Alignment,
            SafetyProperty::ValidWrite,
        ] {
            assert!(
                r.mem_decision(BlockId(2), 1, prop).is_none(),
                "{prop} must be undecided (Open) under truncation, never reported safe"
            );
        }
    }

    #[test]
    fn time_budget_bail_reports_no_memory_decision() {
        // The per-function wall-clock bail (the turnkey-path termination guarantee)
        // must fall to non-PASS exactly like the visit budget: a zero time budget
        // truncates before any memory op is decided, so every obligation is `Open`,
        // never a half-analysed `PASS`. (Soundness pin for the bail path, the same
        // discipline as the wall-clock solve valve.)
        let f = store_buf();
        let r = discharge_with(
            &f,
            crate::ExecLimits {
                max_visits: usize::MAX,
                time_budget: Some(std::time::Duration::ZERO),
                ..Default::default()
            },
        );
        assert!(r.truncated, "a zero time budget must truncate");
        for prop in [
            SafetyProperty::NoNullDeref,
            SafetyProperty::InBounds,
            SafetyProperty::Alignment,
            SafetyProperty::ValidWrite,
        ] {
            assert!(
                r.mem_decision(BlockId(2), 1, prop).is_none(),
                "{prop} must be undecided (Open) under the time bail, never reported safe"
            );
        }
    }

    /// A use-after-free: alloc, free, then store through the freed pointer.
    fn use_after_free() -> Function {
        let buf = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 8),
            align: 1,
        });
        bb0.insts.push(Inst::Dealloc {
            region: RegionKind::Heap,
            ptr: Operand::Reg(buf),
        });
        bb0.insts.push(Inst::Store {
            ty: Type::int(8),
            ptr: Operand::Reg(buf),
            value: Operand::int(8, 0),
            align: 1,
        });
        Function {
            id: FuncId(0),
            name: "uaf".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn use_after_free_is_not_proven() {
        let f = use_after_free();
        let r = discharge_function(&f);
        // The free itself (index 1) is proven (base of a live region).
        let free = r.mem_decision(BlockId(0), 1, SafetyProperty::NoDoubleFree).expect("free");
        assert!(free.proven);
        // The store after free (index 2) must NOT prove temporal safety.
        let uaf = r
            .mem_decision(BlockId(0), 2, SafetyProperty::NoUseAfterFree)
            .expect("uaf");
        assert!(!uaf.proven, "use-after-free must stay unproven");
        // On this exact path the region is definitely freed, so the UAF is
        // refuted with a (here input-free) witness.
        assert!(uaf.refutation.is_some(), "definite use-after-free is refuted");
    }

    /// `double_free()`: `buf = alloc; free buf; free buf` — the second free is a
    /// definite double free.
    fn double_free() -> Function {
        let buf = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 8),
            align: 1,
        });
        bb0.insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: Operand::Reg(buf) });
        bb0.insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: Operand::Reg(buf) });
        Function {
            id: FuncId(0),
            name: "double_free".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    /// `branch_fixture(K)`: `if i < K { if i >= 1 { check } }`. The inner branch
    /// `i >= 1` is unreachable exactly when `K == 1` (`i < 1 ∧ i >= 1`).
    fn branch_fixture(c_bound: u128, name: &'static str) -> Function {
        let i = RegId(0);
        let c = RegId(1);
        let d = RegId(2);
        let mut bb0 = BasicBlock::new(
            BlockId(0),
            Terminator::CondBr {
                cond: Operand::Reg(c),
                then_blk: BlockId(1),
                then_args: vec![],
                else_blk: BlockId(3),
                else_args: vec![],
            },
        );
        bb0.insts.push(Inst::Assign {
            dst: c,
            ty: Type::Bool,
            value: RValue::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(i), rhs: Operand::int(64, c_bound) },
        });
        let mut bb1 = BasicBlock::new(
            BlockId(1),
            Terminator::CondBr {
                cond: Operand::Reg(d),
                then_blk: BlockId(2),
                then_args: vec![],
                else_blk: BlockId(3),
                else_args: vec![],
            },
        );
        bb1.insts.push(Inst::Assign {
            dst: d,
            ty: Type::Bool,
            value: RValue::Cmp { op: CmpOp::Uge, lhs: Operand::Reg(i), rhs: Operand::int(64, 1) },
        });
        let mut bb2 = BasicBlock::new(BlockId(2), Terminator::Return(None));
        bb2.insts.push(Inst::SafetyCheck {
            property: SafetyProperty::InBounds,
            condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(i), rhs: Operand::int(64, 8) },
            note: "inner check".into(),
        });
        let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));
        Function {
            id: FuncId(0),
            name: name.into(),
            params: vec![(i, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2, bb3],
            entry: BlockId(0),
        }
    }

    #[test]
    fn infeasible_branch_is_pruned() {
        // `if i < 1 { if i >= 1 { check } }` — the inner block is unreachable, so
        // its check is never explored (absent from the report).
        let r = discharge_function(&branch_fixture(1, "dead"));
        assert!(r.outcome(BlockId(2), 0).is_none(), "the dead inner check is pruned");
    }

    #[test]
    fn feasible_branch_is_explored() {
        // `if i < 8 { if i >= 1 { check } }` — the inner block is reachable
        // (e.g. i = 5), so its check IS explored.
        let r = discharge_function(&branch_fixture(8, "live"));
        assert!(r.outcome(BlockId(2), 0).is_some(), "the reachable inner check is explored");
    }

    /// `diamond_phi(sel)`: `p = if sel < 1 { 3 } else { 5 }; check p < 8`. The
    /// join block has a PHI (`p`) merged via `ITE`; the check holds on the merged
    /// value (both arms are < 8).
    fn diamond_phi() -> Function {
        let sel = RegId(0);
        let c = RegId(1);
        let p = RegId(2);
        let mut bb0 = BasicBlock::new(
            BlockId(0),
            Terminator::CondBr {
                cond: Operand::Reg(c),
                then_blk: BlockId(1),
                then_args: vec![],
                else_blk: BlockId(2),
                else_args: vec![],
            },
        );
        bb0.insts.push(Inst::Assign {
            dst: c,
            ty: Type::Bool,
            value: RValue::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(sel), rhs: Operand::int(64, 1) },
        });
        let bb1 = BasicBlock::new(BlockId(1), Terminator::Br { target: BlockId(3), args: vec![Operand::int(64, 3)] });
        let bb2 = BasicBlock::new(BlockId(2), Terminator::Br { target: BlockId(3), args: vec![Operand::int(64, 5)] });
        let mut bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));
        bb3.params = vec![(p, Type::int(64))];
        bb3.insts.push(Inst::SafetyCheck {
            property: SafetyProperty::InBounds,
            condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::Reg(p), rhs: Operand::int(64, 8) },
            note: "merged p < 8".into(),
        });
        Function {
            id: FuncId(0),
            name: "diamond_phi".into(),
            params: vec![(sel, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2, bb3],
            entry: BlockId(0),
        }
    }

    #[test]
    fn merged_phi_value_is_proven_at_the_join() {
        // The join is analysed once with `p = ite(sel<1, 3, 5)`, and the check
        // `p < 8` is proved bit-precisely on the merged value.
        let r = discharge_function(&diamond_phi());
        assert_eq!(r.outcome(BlockId(3), 0), Some(SymOutcome::Proven));
    }

    /// `n` independent diamonds in sequence — `2^n` distinct paths, but only
    /// `4n + 1` blocks. Each diamond `i` branches on bit `i` of `sel`.
    fn wide_diamonds(n: usize) -> Function {
        let sel = RegId(0);
        let final_id = BlockId((4 * n) as u32);
        let mut blocks = Vec::new();
        for i in 0..n {
            let h = BlockId((4 * i) as u32);
            let t = BlockId((4 * i + 1) as u32);
            let e = BlockId((4 * i + 2) as u32);
            let m = BlockId((4 * i + 3) as u32);
            let next = if i + 1 < n { BlockId((4 * (i + 1)) as u32) } else { final_id };
            let tmask = RegId((1 + 2 * i) as u32);
            let creg = RegId((2 + 2 * i) as u32);
            let mut hb = BasicBlock::new(
                h,
                Terminator::CondBr { cond: Operand::Reg(creg), then_blk: t, then_args: vec![], else_blk: e, else_args: vec![] },
            );
            hb.insts.push(Inst::Assign {
                dst: tmask,
                ty: Type::int(64),
                value: RValue::Bin { op: BinOp::And, lhs: Operand::Reg(sel), rhs: Operand::int(64, 1u128 << i) },
            });
            hb.insts.push(Inst::Assign {
                dst: creg,
                ty: Type::Bool,
                value: RValue::Cmp { op: CmpOp::Ne, lhs: Operand::Reg(tmask), rhs: Operand::int(64, 0) },
            });
            blocks.push(hb);
            blocks.push(BasicBlock::new(t, Terminator::Br { target: m, args: vec![] }));
            blocks.push(BasicBlock::new(e, Terminator::Br { target: m, args: vec![] }));
            blocks.push(BasicBlock::new(m, Terminator::Br { target: next, args: vec![] }));
        }
        let mut fb = BasicBlock::new(final_id, Terminator::Return(None));
        fb.insts.push(Inst::SafetyCheck {
            property: SafetyProperty::InBounds,
            condition: Condition::Cmp { op: CmpOp::Ult, lhs: Operand::int(64, 3), rhs: Operand::int(64, 8) },
            note: "final".into(),
        });
        blocks.push(fb);
        Function {
            id: FuncId(0),
            name: "wide".into(),
            params: vec![(sel, Type::int(64))],
            ret_ty: Type::Unit,
            blocks,
            entry: BlockId(0),
        }
    }

    #[test]
    fn wide_cfg_is_processed_once_per_block_not_per_path() {
        // 8 independent diamonds = 256 distinct paths, but only 33 blocks. With a
        // budget far below the path count, merging still verifies — each block is
        // processed once (the old per-path walk would truncate).
        let f = wide_diamonds(8);
        let r = discharge_with(&f, crate::ExecLimits { max_visits: 40, ..Default::default() });
        assert!(!r.truncated, "merging keeps visits linear in blocks, not exponential in paths");
        assert_eq!(r.outcome(BlockId(32), 0), Some(SymOutcome::Proven), "final check verified");
    }

    #[test]
    fn double_free_is_refuted() {
        let r = discharge_function(&double_free());
        // First free (index 1) is proven safe.
        let first = r.mem_decision(BlockId(0), 1, SafetyProperty::NoDoubleFree).expect("first free");
        assert!(first.proven);
        // Second free (index 2) is a definite double free — refuted.
        let second = r.mem_decision(BlockId(0), 2, SafetyProperty::NoDoubleFree).expect("second free");
        assert!(!second.proven);
        assert!(second.refutation.is_some(), "double free is refuted with a witness");
    }

    /// `alloca; store; call @unknown(); load` — with `kind` distinguishing the
    /// region. A callee cannot legitimately free a caller's *stack* slot (that
    /// free is UB, refuted in the callee by `check_dealloc`'s non-heap check),
    /// so the alloca's liveness survives the opaque call and the load's
    /// use-after-free obligation is provable. This assume/guarantee pair is what
    /// keeps rustc's ubiquitous alloca-heavy debug IR provable across helper
    /// calls.
    fn call_then_load(kind: RegionKind) -> Function {
        let buf = RegId(0);
        let v = RegId(1);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: kind,
            elem: Type::int(32),
            count: Operand::int(64, 1),
            align: 4,
        });
        bb0.insts.push(Inst::Store {
            ty: Type::int(32),
            ptr: Operand::Reg(buf),
            value: Operand::int(32, 7),
            align: 4,
        });
        bb0.insts.push(Inst::Call {
            dst: None,
            callee: Callee::Symbol("unknown".into()),
            args: vec![],
            ret_ty: Type::Unit,
            ret_ref: None,
        });
        bb0.insts.push(Inst::Load { dst: v, ty: Type::int(32), ptr: Operand::Reg(buf), align: 4 });
        Function {
            id: FuncId(0),
            name: "call_then_load".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn stack_liveness_survives_an_opaque_call() {
        let r = discharge_function(&call_then_load(RegionKind::Stack));
        let d = r
            .mem_decision(BlockId(0), 3, SafetyProperty::NoUseAfterFree)
            .expect("UAF obligation for the load");
        assert!(d.proven, "a stack slot cannot be freed by a callee: {d:?}");
    }

    /// Positive control for the stack-liveness rule: an *owned heap* region can
    /// genuinely be handed off and freed by an opaque callee, so its liveness
    /// must NOT be provable after the call. If this starts passing, the havoc is
    /// muted and the rule above proves too much.
    #[test]
    fn heap_liveness_is_still_havocked_by_an_opaque_call() {
        let r = discharge_function(&call_then_load(RegionKind::Heap));
        let d = r
            .mem_decision(BlockId(0), 3, SafetyProperty::NoUseAfterFree)
            .expect("UAF obligation for the load");
        assert!(!d.proven, "owned heap liveness must not survive an opaque call: {d:?}");
    }

    /// Freeing a stack region is UB no matter its state — and it is the
    /// callee-side guarantee the stack-liveness rule composes with, so it must
    /// be *refuted*, not merely unproven.
    #[test]
    fn freeing_a_stack_region_is_refuted() {
        let buf = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Stack,
            elem: Type::int(8),
            count: Operand::int(64, 8),
            align: 1,
        });
        bb0.insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: Operand::Reg(buf) });
        let f = Function {
            id: FuncId(0),
            name: "free_stack".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let r = discharge_function(&f);
        let d = r.mem_decision(BlockId(0), 1, SafetyProperty::NoDoubleFree).expect("free");
        assert!(!d.proven, "freeing a stack region must never be proven");
        assert!(d.refutation.is_some(), "freeing a stack region is definite UB: {d:?}");
    }

    /// A counting loop writing across an allocation:
    ///   bb0: buf = alloc i32*n ; br bb1(0)
    ///   bb1(i): c = i < n ; condbr c -> bb2(i) / bb3
    ///   bb2(j): p = buf + j*4 ; store 0 -> p ; nj = j+1 ; br bb1(nj)
    ///   bb3: return
    fn loop_store() -> Function {
        let n = RegId(0);
        let buf = RegId(1);
        let i = RegId(2);
        let c = RegId(3);
        let j = RegId(4);
        let p = RegId(5);
        let nj = RegId(6);

        let mut bb0 = BasicBlock::new(
            BlockId(0),
            Terminator::Br {
                target: BlockId(1),
                args: vec![Operand::int(64, 0)],
            },
        );
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(32),
            count: Operand::Reg(n),
            align: 4,
        });

        let mut bb1 = BasicBlock::new(
            BlockId(1),
            Terminator::CondBr {
                cond: Operand::Reg(c),
                then_blk: BlockId(2),
                then_args: vec![Operand::Reg(i)],
                else_blk: BlockId(3),
                else_args: vec![],
            },
        );
        bb1.params = vec![(i, Type::int(64))];
        bb1.insts.push(Inst::Assign {
            dst: c,
            ty: Type::Bool,
            value: RValue::Cmp {
                op: CmpOp::Slt,
                lhs: Operand::Reg(i),
                rhs: Operand::Reg(n),
            },
        });

        let mut bb2 = BasicBlock::new(
            BlockId(2),
            Terminator::Br {
                target: BlockId(1),
                args: vec![Operand::Reg(nj)],
            },
        );
        bb2.params = vec![(j, Type::int(64))];
        bb2.insts.push(Inst::PtrOffset {
            dst: p,
            base: Operand::Reg(buf),
            index: Operand::Reg(j),
            elem: Type::int(32),
        });
        bb2.insts.push(Inst::Store {
            ty: Type::int(32),
            ptr: Operand::Reg(p),
            value: Operand::int(32, 0),
            align: 4,
        });
        bb2.insts.push(Inst::Assign {
            dst: nj,
            ty: Type::int(64),
            value: RValue::Bin {
                op: BinOp::Add,
                lhs: Operand::Reg(j),
                rhs: Operand::int(64, 1),
            },
        });

        let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));

        Function {
            id: FuncId(0),
            name: "loop_store".into(),
            params: vec![(n, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2, bb3],
            entry: BlockId(0),
        }
    }

    /// Store a pointer into a slot, load it back, dereference it. Without a
    /// heap model the loaded pointer is opaque (deref → Unknown); with the
    /// alias-aware heap, provenance survives the round-trip and the deref proves.
    fn indirect_store() -> Function {
        let buf = RegId(0);
        let slot = RegId(1);
        let p = RegId(2);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 16),
            align: 1,
        });
        bb0.insts.push(Inst::Alloc {
            dst: slot,
            region: RegionKind::Heap,
            elem: Type::ptr(Type::int(8)),
            count: Operand::int(64, 1),
            align: 8,
        });
        bb0.insts.push(Inst::Store {
            ty: Type::ptr(Type::int(8)),
            ptr: Operand::Reg(slot),
            value: Operand::Reg(buf),
            align: 8,
        });
        bb0.insts.push(Inst::Load {
            dst: p,
            ty: Type::ptr(Type::int(8)),
            ptr: Operand::Reg(slot),
            align: 8,
        });
        bb0.insts.push(Inst::Store {
            ty: Type::int(8),
            ptr: Operand::Reg(p),
            value: Operand::int(8, 0),
            align: 1,
        });
        Function {
            id: FuncId(0),
            name: "indirect_store".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    /// slot ← buf; call `asm`; p = load slot; store through p. A register-only
    /// (`<inline asm nomem>`) call must NOT havoc the heap, so the round-trip survives
    /// and the final store proves temporal safety; a memory-clobbering `<inline asm>`
    /// does havoc, so it does not.
    fn asm_roundtrip(asm_name: &str) -> Function {
        let slot = RegId(0);
        let buf = RegId(1);
        let p = RegId(2);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc { dst: slot, region: RegionKind::Heap, elem: Type::ptr(Type::int(8)), count: Operand::int(64, 1), align: 8 });
        bb0.insts.push(Inst::Alloc { dst: buf, region: RegionKind::Heap, elem: Type::int(8), count: Operand::int(64, 8), align: 1 });
        bb0.insts.push(Inst::Store { ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(slot), value: Operand::Reg(buf), align: 8 });
        bb0.insts.push(Inst::Call { dst: None, callee: csolver_ir::Callee::Symbol(asm_name.into()), args: vec![], ret_ty: Type::Unit, ret_ref: None });
        bb0.insts.push(Inst::Load { dst: p, ty: Type::ptr(Type::int(8)), ptr: Operand::Reg(slot), align: 8 });
        bb0.insts.push(Inst::Store { ty: Type::int(8), ptr: Operand::Reg(p), value: Operand::int(8, 0), align: 1 });
        Function { id: FuncId(0), name: "asm_rt".into(), params: vec![], ret_ty: Type::Unit, blocks: vec![bb0], entry: BlockId(0) }
    }

    #[test]
    fn register_only_inline_asm_does_not_havoc_the_heap() {
        let r = discharge_function(&asm_roundtrip("<inline asm nomem>"));
        let d = r.mem_decision(BlockId(0), 5, SafetyProperty::NoUseAfterFree).expect("uaf");
        assert!(d.proven, "register-only asm must preserve the heap: {}", d.residual);
    }

    #[test]
    fn memory_clobbering_inline_asm_havocs_the_heap() {
        let r = discharge_function(&asm_roundtrip("<inline asm>"));
        let d = r.mem_decision(BlockId(0), 5, SafetyProperty::NoUseAfterFree).expect("uaf");
        assert!(!d.proven, "a memory-clobbering asm must havoc (stay conservative)");
    }

    #[test]
    fn pointer_survives_store_load_roundtrip() {
        let f = indirect_store();
        let r = discharge_function(&f);
        // The final deref (store at index 4): provenance survived the load, so
        // non-null and in-bounds are proven (they would be Unknown if the load
        // had returned an opaque value).
        for prop in [
            SafetyProperty::NoNullDeref,
            SafetyProperty::NoUseAfterFree,
            SafetyProperty::InBounds,
            SafetyProperty::ValidWrite,
        ] {
            let d = r.mem_decision(BlockId(0), 4, prop).expect("decided");
            assert!(d.proven, "{prop} should be proven via heap/alias: {}", d.residual);
        }
    }

    /// Regression (soundness): a `free` inside a loop body must NOT let an
    /// access or the free itself be proved — later iterations are UAF/double-free.
    #[test]
    fn free_inside_loop_is_not_proven() {
        let n = RegId(0);
        let buf = RegId(1);
        let i = RegId(2);
        let c = RegId(3);
        let j = RegId(4);
        let nj = RegId(5);

        let mut bb0 = BasicBlock::new(
            BlockId(0),
            Terminator::Br { target: BlockId(1), args: vec![Operand::int(64, 0)] },
        );
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 8),
            align: 1,
        });
        let mut bb1 = BasicBlock::new(
            BlockId(1),
            Terminator::CondBr {
                cond: Operand::Reg(c),
                then_blk: BlockId(2),
                then_args: vec![Operand::Reg(i)],
                else_blk: BlockId(3),
                else_args: vec![],
            },
        );
        bb1.params = vec![(i, Type::int(64))];
        bb1.insts.push(Inst::Assign {
            dst: c,
            ty: Type::Bool,
            value: RValue::Cmp { op: CmpOp::Slt, lhs: Operand::Reg(i), rhs: Operand::Reg(n) },
        });
        let mut bb2 = BasicBlock::new(
            BlockId(2),
            Terminator::Br { target: BlockId(1), args: vec![Operand::Reg(nj)] },
        );
        bb2.params = vec![(j, Type::int(64))];
        bb2.insts.push(Inst::Store {
            ty: Type::int(8),
            ptr: Operand::Reg(buf),
            value: Operand::int(8, 0),
            align: 1,
        });
        bb2.insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: Operand::Reg(buf) });
        bb2.insts.push(Inst::Assign {
            dst: nj,
            ty: Type::int(64),
            value: RValue::Bin { op: BinOp::Add, lhs: Operand::Reg(j), rhs: Operand::int(64, 1) },
        });
        let bb3 = BasicBlock::new(BlockId(3), Terminator::Return(None));
        let f = Function {
            id: FuncId(0),
            name: "loop_free".into(),
            params: vec![(n, Type::int(64))],
            ret_ty: Type::Unit,
            blocks: vec![bb0, bb1, bb2, bb3],
            entry: BlockId(0),
        };
        let r = discharge_function(&f);
        let uaf = r.mem_decision(BlockId(2), 0, SafetyProperty::NoUseAfterFree).expect("uaf");
        assert!(!uaf.proven, "store in a freeing loop must not prove temporal safety");
        let df = r.mem_decision(BlockId(2), 1, SafetyProperty::NoDoubleFree).expect("df");
        assert!(!df.proven, "free in a loop must not prove no-double-free");
    }

    /// Regression (soundness): a call to a freeing function must invalidate
    /// region liveness, so a use after it is not proved.
    #[test]
    fn use_after_freeing_call_is_not_proven() {
        use std::collections::HashMap;
        let buf = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 8),
            align: 1,
        });
        bb0.insts.push(Inst::Call {
            dst: None,
            callee: csolver_ir::Callee::Direct(FuncId(9)),
            args: vec![Operand::Reg(buf)],
            ret_ty: Type::Unit,
            ret_ref: None,
        });
        bb0.insts.push(Inst::Store {
            ty: Type::int(8),
            ptr: Operand::Reg(buf),
            value: Operand::int(8, 0),
            align: 1,
        });
        let f = Function {
            id: FuncId(0),
            name: "caller".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let mut summaries = HashMap::new();
        summaries.insert(
            FuncId(9),
            crate::summary::Summary {
                ret: crate::summary::RetSummary::Unknown,
                writes: false,
                frees: true,
                frees_arg: None,
                prov: crate::summary::ProvTransfer::default(),
            },
        );
        let r = discharge_with_summaries(&f, &summaries);
        let uaf = r.mem_decision(BlockId(0), 2, SafetyProperty::NoUseAfterFree).expect("uaf");
        assert!(!uaf.proven, "use after a freeing call must not prove temporal safety");
    }

    /// Double-free through a freeing *wrapper* (a callee that definitely frees its
    /// parameter): calling it twice on the same pointer is a double-free (flagged in
    /// bug-finding mode); calling it once is not.
    #[test]
    fn double_free_through_a_freeing_wrapper_is_flagged() {
        use std::collections::HashMap;
        let buf = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 8),
            align: 1,
        });
        let free_call = |b: &mut BasicBlock| b.insts.push(Inst::Call {
            dst: None,
            callee: csolver_ir::Callee::Direct(FuncId(9)),
            args: vec![Operand::Reg(buf)],
            ret_ty: Type::Unit,
            ret_ref: None,
        });
        free_call(&mut bb0); // idx 1 — first free
        free_call(&mut bb0); // idx 2 — double free
        let f = Function {
            id: FuncId(0),
            name: "double_free_wrapper".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let mut summaries = HashMap::new();
        summaries.insert(
            FuncId(9),
            Summary { ret: RetSummary::Unknown, writes: false, frees: true, frees_arg: Some(0), prov: ProvTransfer::default() },
        );
        let r = discharge_with_fields(
            &f, &summaries, &[], &[], &HashMap::new(), &HashMap::new(), true, true, false,
        );
        let first = r.mem_decision(BlockId(0), 1, SafetyProperty::NoDoubleFree).expect("first free");
        assert!(first.refutation.is_none(), "the first free must not be flagged: {first:?}");
        let second = r.mem_decision(BlockId(0), 2, SafetyProperty::NoDoubleFree).expect("second free");
        assert!(second.refutation.is_some(), "the second free of the same pointer is a double-free: {second:?}");
    }

    /// Soundness: `frees_arg` is derived only for a single-block `kfree`-style wrapper;
    /// a multi-block callee gets `frees_arg = None`, so two calls are NOT a double-free.
    #[test]
    fn derive_frees_arg_only_for_single_block_wrapper() {
        let p = RegId(0);
        // Single block: `free(p)` → frees_arg = Some(0).
        let mut single = BasicBlock::new(BlockId(0), Terminator::Return(None));
        single.insts.push(Inst::Dealloc { region: RegionKind::Heap, ptr: Operand::Reg(p) });
        let wrapper = Function {
            id: FuncId(0), name: "w".into(), params: vec![(p, Type::ptr(Type::int(8)))],
            ret_ty: Type::Unit, blocks: vec![single], entry: BlockId(0),
        };
        assert_eq!(crate::summary::summarize_module(&{
            let mut m = csolver_ir::Module::new("m"); m.functions.push(wrapper); m
        }).get(&FuncId(0)).unwrap().frees_arg, Some(0));
    }

    /// Build a caller that stores `buf` into `slot`, loads a function pointer
    /// from constant global `G` at offset 0, calls it indirectly, reloads `slot`
    /// and writes through it. The final write proves temporal safety **iff** the
    /// indirect call was devirtualised to a pure summary (no havoc/free).
    fn devirt_caller() -> Function {
        let slot = RegId(0);
        let buf = RegId(1);
        let fp = RegId(2);
        let p = RegId(3);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: slot,
            region: RegionKind::Heap,
            elem: Type::ptr(Type::int(8)),
            count: Operand::int(64, 1),
            align: 8,
        });
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 8),
            align: 1,
        });
        bb0.insts.push(Inst::Store {
            ty: Type::ptr(Type::int(8)),
            ptr: Operand::Reg(slot),
            value: Operand::Reg(buf),
            align: 8,
        });
        bb0.insts.push(Inst::Load {
            dst: fp,
            ty: Type::ptr(Type::int(8)),
            ptr: Operand::Const(Const::Symbol("G".into())),
            align: 8,
        });
        bb0.insts.push(Inst::Call {
            dst: None,
            callee: csolver_ir::Callee::Indirect(Operand::Reg(fp)),
            args: vec![],
            ret_ty: Type::Unit,
            ret_ref: None,
        });
        bb0.insts.push(Inst::Load {
            dst: p,
            ty: Type::ptr(Type::int(8)),
            ptr: Operand::Reg(slot),
            align: 8,
        });
        bb0.insts.push(Inst::Store {
            ty: Type::int(8),
            ptr: Operand::Reg(p),
            value: Operand::int(8, 0),
            align: 1,
        });
        Function {
            id: FuncId(0),
            name: "devirt_caller".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        }
    }

    #[test]
    fn indirect_call_devirtualised_to_a_pure_summary_preserves_state() {
        use std::collections::HashMap;
        let f = devirt_caller();
        let mut summaries = HashMap::new();
        // A pure callee: no writes, no frees.
        summaries.insert(
            FuncId(1),
            Summary { ret: RetSummary::Unknown, writes: false, frees: false, frees_arg: None, prov: ProvTransfer::default() },
        );
        let mut globals = HashMap::new();
        globals.insert("G".to_string(), csolver_ir::GlobalDef { size: 8, align: 8, writable: false });
        let empty_grants = HashMap::new();

        // With the devirt table, the indirect call resolves to the pure summary,
        // so the store into `slot` survives and `buf`'s liveness/provenance too.
        let mut table = HashMap::new();
        table.insert("G".to_string(), vec![(0u64, FuncId(1))]);
        let r = discharge_inner(
            &f, ExecLimits::default(), &summaries, &HashMap::new(), &[], &[], &[], &globals,
            &empty_grants, &table, None,
        );
        assert!(
            r.assumptions.iter().any(|a| a == "devirtualized-indirect-call"),
            "the indirect call should have been devirtualised: {:?}", r.assumptions,
        );
        let uaf = r.mem_decision(BlockId(0), 6, SafetyProperty::NoUseAfterFree).expect("uaf");
        assert!(uaf.proven, "pure devirtualised call must preserve liveness: {}", uaf.residual);

        // Control: no table ⇒ opaque indirect call ⇒ default (may write & free)
        // havoc ⇒ the final write is not proven safe.
        let r2 = discharge_inner(
            &f, ExecLimits::default(), &summaries, &HashMap::new(), &[], &[], &[], &globals,
            &empty_grants, &HashMap::new(), None,
        );
        assert!(
            !r2.assumptions.iter().any(|a| a == "devirtualized-indirect-call"),
            "no table ⇒ no devirtualisation",
        );
        let uaf2 = r2.mem_decision(BlockId(0), 6, SafetyProperty::NoUseAfterFree).expect("uaf2");
        assert!(!uaf2.proven, "an opaque indirect call must havoc, leaving the write unproven");
    }

    /// A1 (IR-intrinsic read-only): a store into a `constant` global — a `.rodata`
    /// write that faults at runtime — is a refutable violation (FAIL), while a store
    /// into a writable global proves. General and sound: it rests only on the module's
    /// own `constant` vs `global` linkage, and a runtime `.rodata` write is always a bug.
    #[test]
    fn write_to_constant_global_is_refuted() {
        use std::collections::HashMap;
        let mk = |name: &str| {
            let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
            bb0.insts.push(Inst::Store {
                ty: Type::int(32),
                ptr: Operand::Const(Const::Symbol(name.into())),
                value: Operand::int(32, 7),
                align: 4,
            });
            Function {
                id: FuncId(0),
                name: "w".into(),
                params: vec![],
                ret_ty: Type::Unit,
                blocks: vec![bb0],
                entry: BlockId(0),
            }
        };
        let mut globals = HashMap::new();
        globals.insert("ro".to_string(), csolver_ir::GlobalDef { size: 4, align: 4, writable: false });
        globals.insert("rw".to_string(), csolver_ir::GlobalDef { size: 4, align: 4, writable: true });
        let empty = HashMap::new();
        let run = |f: &Function| {
            discharge_inner(
                f, ExecLimits { bug_finding: true, ..ExecLimits::default() }, &HashMap::new(),
                &HashMap::new(), &[], &[], &[], &globals, &empty, &HashMap::new(), None,
            )
        };
        let ro = run(&mk("ro"));
        let vw = ro.mem_decision(BlockId(0), 0, SafetyProperty::ValidWrite).expect("valid_write");
        assert!(!vw.proven && vw.refutation.is_some(), "a write into a constant global must be refuted: {}", vw.residual);
        let rw = run(&mk("rw"));
        let vw2 = rw.mem_decision(BlockId(0), 0, SafetyProperty::ValidWrite).expect("valid_write");
        assert!(vw2.proven, "a write into a writable global must prove: {}", vw2.residual);
    }

    /// 2b (whole-program on-demand): a cross-file `Callee::Symbol(name)` with no
    /// in-module id resolves to the program-wide callee summary passed in
    /// `name_summaries` — so the call is analysed with the callee's real effect
    /// instead of an opaque havoc. Sound *and* precise: a pure remote callee lets
    /// the following use prove; a remote callee that frees the argument turns it
    /// into a caught use-after-free.
    #[test]
    fn cross_file_symbol_call_resolves_via_name_summaries() {
        use std::collections::HashMap;
        // bb0: buf = alloc[8]; remote(buf); *buf = 0
        let buf = RegId(0);
        let mut bb0 = BasicBlock::new(BlockId(0), Terminator::Return(None));
        bb0.insts.push(Inst::Alloc {
            dst: buf,
            region: RegionKind::Heap,
            elem: Type::int(8),
            count: Operand::int(64, 8),
            align: 1,
        });
        bb0.insts.push(Inst::Call {
            dst: None,
            callee: Callee::Symbol("remote".into()),
            args: vec![Operand::Reg(buf)],
            ret_ty: Type::Unit,
            ret_ref: None,
        });
        bb0.insts.push(Inst::Store {
            ty: Type::int(8),
            ptr: Operand::Reg(buf),
            value: Operand::int(8, 0),
            align: 1,
        });
        let f = Function {
            id: FuncId(0),
            name: "cross_caller".into(),
            params: vec![],
            ret_ty: Type::Unit,
            blocks: vec![bb0],
            entry: BlockId(0),
        };
        let empty_grants = HashMap::new();

        // Control: no name map ⇒ opaque `Symbol` havoc ⇒ the call may free `buf`,
        // so the following store is NOT proven free of use-after-free.
        let opaque = discharge_inner(
            &f, ExecLimits::default(), &HashMap::new(), &HashMap::new(), &[], &[], &[],
            &HashMap::new(), &empty_grants, &HashMap::new(), None,
        );
        let uaf = opaque.mem_decision(BlockId(0), 2, SafetyProperty::NoUseAfterFree).expect("uaf");
        assert!(!uaf.proven, "an unresolved cross-file symbol must havoc (may free)");

        // Resolve `remote` to a PURE summary ⇒ the store is proven live.
        let mut pure = HashMap::new();
        pure.insert(
            "remote".to_string(),
            Summary { ret: RetSummary::Unknown, writes: false, frees: false, frees_arg: None, prov: ProvTransfer::default() },
        );
        let r_pure = discharge_inner(
            &f, ExecLimits::default(), &HashMap::new(), &pure, &[], &[], &[], &HashMap::new(),
            &empty_grants, &HashMap::new(), None,
        );
        let uaf_pure = r_pure.mem_decision(BlockId(0), 2, SafetyProperty::NoUseAfterFree).expect("uaf");
        assert!(uaf_pure.proven, "a pure remote callee must preserve liveness: {}", uaf_pure.residual);

        // Resolve `remote` to a summary that frees argument 0 ⇒ the store is a
        // use-after-free and must be refuted (sound: the real effect flows in).
        let mut frees = HashMap::new();
        frees.insert(
            "remote".to_string(),
            Summary { ret: RetSummary::Unknown, writes: false, frees: true, frees_arg: Some(0), prov: ProvTransfer::default() },
        );
        let r_free = discharge_inner(
            &f, ExecLimits::default(), &HashMap::new(), &frees, &[], &[], &[], &HashMap::new(),
            &empty_grants, &HashMap::new(), None,
        );
        let uaf_free = r_free.mem_decision(BlockId(0), 2, SafetyProperty::NoUseAfterFree).expect("uaf");
        assert!(!uaf_free.proven, "a remote callee that frees the arg makes the store a UAF");
    }

    #[test]
    fn loop_body_access_is_proven_via_invariant() {
        let f = loop_store();
        let r = discharge_function(&f);
        assert!(!r.truncated, "loop exploration must terminate");
        // The store at bb2 index 1: in-bounds proved from the interval
        // invariant (i >= 0) plus the loop guard (i < n).
        let inb = r
            .mem_decision(BlockId(2), 1, SafetyProperty::InBounds)
            .expect("in-bounds decided");
        assert!(inb.proven, "loop body access should be in bounds: {}", inb.residual);
        // Pointer arithmetic too.
        let arith = r
            .mem_decision(BlockId(2), 0, SafetyProperty::ValidPointerArith)
            .expect("ptr arith decided");
        assert!(arith.proven, "pointer arithmetic: {}", arith.residual);
    }
}
