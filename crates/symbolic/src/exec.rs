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
    FuncId, Function, GlobalDef, Inst, MemKind, Operand, PtrContract, PtrHint, RValue, RefResult,
    RegId, SizeSpec, Terminator, Type, WrapFlags,
};
use csolver_memory::{AliasResult, LifetimeState, Permissions};
use csolver_solver::{
    bitprecise, prove_implies_method, BvOp, CmpOp as SCmp, ExprCtx, ExprId, Node, ProofMethod,
};
use std::collections::{HashMap, HashSet};
// Fast, deterministic hasher for the hot internal maps (per-path `PathState`, proof
// caches, the merge worklist). The public `discharge_*` API keeps `std` `HashMap`
// parameters, so both names are in scope. Verdict-neutral (see `csolver_core::hash`).
use csolver_core::{FxHashMap, FxHashSet};

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
/// A raw pointer — a parameter, a loaded field, an `inttoptr` (`current`), or a call result —
/// is *assumed* to designate a valid object of the type its use recovers. The
/// `--assume-valid-params` opt-in; unsound in general (such a pointer may dangle or be null).
const PARAM_VALID: &str = "param-valid";
/// A C `(buf, len)` parameter pairing: the length parameter really does describe the
/// buffer. A convention, not an ABI guarantee (unlike Rust's `slice-abi`) — opt-in only.
const PARAM_BUFFER_LEN: &str = "param-buffer-len";
/// A pointer whose code navigates *past* its declared struct type (`gep %struct.T, ptr %p,
/// i64 1` — `crypto_skcipher_ctx`, `netdev_priv`) designates an allocation holding the struct
/// plus a trailing context. Its real size is known only at the allocation site; the extent the
/// code reaches is assumed to be within it. Opt-in: a symbolic index could overrun into the
/// assumed tail without being refuted.
const STRUCT_TAIL: &str = "struct-tail";
/// A region backing an `ioremap`-style MMIO mapping: live, of the mapped size, and
/// **externally initialized** (device registers), so a read of it is not an
/// uninitialized-read bug. Rests on `alloc-succeeds` (the mapping call succeeded).
const MMIO: &str = "mmio-mapping";
/// The trust that an access through an `iomem`-labelled pointer (an `ioremap` mapping reached,
/// possibly, through a struct field) stays within the device's mapping. Prove-only, opt-in
/// (`--assume-valid-mmio`): a symbolic register offset could genuinely overrun.
const VALID_MMIO: &str = "valid-mmio";
/// A scalar **loaded from memory** (a struct field) is assumed to hold a value valid for its
/// use — a shift amount below the bit width, a non-zero divisor. The scalar analogue of
/// `--assume-valid-params`; unsound in general (an opaque write could store an out-of-range
/// value), so opt-in via `--assume-field-invariants`.
const FIELD_INVARIANTS: &str = "field-invariants";
/// A `&T`/`&mut T` value is a valid reference to its pointee (Rust's reference
/// invariant), even when the analysis cannot see where it came from.
const VALID_REFERENCE: &str = "valid-reference";
const STRUCT_ABI: &str = "struct-abi";


// --- module split (mechanical refactor; one `impl Explorer` part per file) ---
mod driver;
mod value;
mod classify;
mod state;
mod merge;
mod mergecore;
mod loops;
mod sentinel;
mod step;
mod step_contract;
mod step_mem;
mod effects;
mod calls;
mod checks;
mod decide;
mod loadrec;
mod eval;
#[cfg(test)]
mod tests;

use classify::*;
use driver::*;
use state::*;
use value::*;

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
    /// Blocks proven **unreachable**: a visited predecessor pruned the edge into them as
    /// bit-precisely infeasible, and no live edge ever reached them. No concrete execution
    /// enters such a block, so every obligation inside it is **vacuously satisfied** — the
    /// verifier discharges it `Proven` instead of leaving it `UNKNOWN` for want of a decision
    /// (see `not_analyzed_reason`). A block merely *never considered* (no visited predecessor)
    /// is deliberately NOT listed: that cannot distinguish transitively-dead code from a
    /// back-edge-only entry, and claiming it proven could be a false PASS.
    pub dead_blocks: HashSet<BlockId>,
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
    discharge_inner(f, ExecLimits::default(), &HashMap::new(), &HashMap::new(), &[], &[], &[], &HashMap::new(), &HashMap::new(), &HashMap::new(), &HashMap::new(), None, &HashMap::new(), None, &HashMap::new())
}

/// As [`discharge_function`], but using the given function summaries to reason
/// about calls (provenance-preserving returns, effect-aware heap handling).
pub fn discharge_with_summaries(
    f: &Function,
    summaries: &HashMap<FuncId, Summary>,
) -> SymbolicReport {
    discharge_inner(f, ExecLimits::default(), summaries, &HashMap::new(), &[], &[], &[], &HashMap::new(), &HashMap::new(), &HashMap::new(), &HashMap::new(), None, &HashMap::new(), None, &HashMap::new())
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
    discharge_inner(f, ExecLimits::default(), summaries, &HashMap::new(), contracts, &[], &[], globals, &HashMap::new(), &HashMap::new(), &HashMap::new(), None, &HashMap::new(), None, &HashMap::new())
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
        &HashMap::new(), &HashMap::new(), None, ExecLimits::default().time_budget, bug_finding, exported,
        assume_valid_params, false, false, false, false, false, false, false, false, &HashMap::new(), None,
        &HashMap::new(),
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
    global_ptr_fields: &HashMap<String, Vec<(u64, String)>>,
    analysis_in: Option<&IntervalAnalysis>,
    time_budget: Option<std::time::Duration>,
    bug_finding: bool,
    exported: bool,
    assume_valid_params: bool,
    aliasing_model: bool,
    flat_memory: bool,
    assume_valid_returns: bool,
    assume_valid_loop_ptrs: bool,
    assume_param_buffer_len: bool,
    assume_struct_tail: bool,
    assume_valid_mmio: bool,
    assume_field_invariants: bool,
    reg_ptr_hints: &HashMap<RegId, PtrHint>,
    mmio_region: Option<csolver_ir::MmioHandler>,
    devirt: &HashMap<RegId, String>,
) -> SymbolicReport {
    let limits = ExecLimits {
        bug_finding, exported, assume_valid_params, assume_valid_returns, assume_valid_loop_ptrs,
        assume_param_buffer_len, assume_struct_tail, assume_valid_mmio, assume_field_invariants,
        aliasing_model, flat_memory, time_budget,
        ..ExecLimits::default()
    };
    discharge_inner(
        f, limits, summaries, name_summaries, contracts, field_contracts, scalar_pre, globals,
        prov_grants, global_fn_ptrs, global_ptr_fields, analysis_in, reg_ptr_hints, mmio_region,
        devirt,
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
    discharge_inner(f, limits, &HashMap::new(), &HashMap::new(), &[], &[], &[], &HashMap::new(), &HashMap::new(), &HashMap::new(), &HashMap::new(), None, &HashMap::new(), None, &HashMap::new())
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

