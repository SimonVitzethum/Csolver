use super::*;

/// How the integer value used as a pointer was computed — the proximate defining
/// instruction of the pointer operand. Diagnostic only.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ScalarPtrCause {
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
    pub(crate) fn residual(self) -> &'static str {
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
/// The registers whose value is **derived from a load** — a load result, or anything computed
/// from a load-derived register (through arithmetic, casts, or pointer offsets). Used by the
/// weak-memory model: a read whose *address* is load-derived is address-dependent on the earlier
/// load (the `rcu_dereference` pointer-chase), so it does not reorder. A fixpoint over the
/// function; over-approximating is safe (it only *removes* reorderings — never a false race).
pub(crate) fn load_derived_regs(f: &Function) -> HashSet<RegId> {
    let mut derived: HashSet<RegId> = HashSet::new();
    let mut changed = true;
    while changed {
        changed = false;
        for b in &f.blocks {
            for inst in &b.insts {
                let (dst, from_load) = match inst {
                    Inst::Load { dst, .. } => (Some(*dst), true),
                    Inst::Assign { dst, value, .. } => {
                        let dep = rvalue_regs(value).into_iter().any(|r| derived.contains(&r));
                        (Some(*dst), dep)
                    }
                    Inst::PtrOffset { dst, base, index, .. } => {
                        let dep = [base, index]
                            .into_iter()
                            .filter_map(|o| o.as_reg())
                            .any(|r| derived.contains(&r));
                        (Some(*dst), dep)
                    }
                    Inst::FieldPtr { dst, base, .. } => {
                        (Some(*dst), base.as_reg().is_some_and(|r| derived.contains(&r)))
                    }
                    _ => (None, false),
                };
                if let Some(d) = dst {
                    if from_load && derived.insert(d) {
                        changed = true;
                    }
                }
            }
        }
    }
    derived
}

/// The static borrow-tag derivation for the opt-in aliasing model. A **borrow tag** is the
/// register a `csolver.retag.mut` marker created (a `&mut` reborrow); every pointer register
/// derived from it by copy/cast/`PtrOffset`/`FieldPtr` belongs to that borrow. `parent` is the
/// derivation tree over borrows: `parent[tag]` is the borrow the retag reborrowed from (`None`
/// for a root — a reborrow of an untracked pointer such as a `&mut` parameter). SSA-static: a
/// register's borrow is fixed by its definition, so the dynamic executor only tracks which tags
/// are *live* per region (see `PathState.region_borrows`).
#[derive(Debug, Clone, Default)]
pub(crate) struct BorrowInfo {
    /// Borrow tag (a `csolver.retag.*` dst register, or a `&mut`-parameter register) → whether
    /// it is a **unique** (`&mut`) borrow. A tag absent here defaults to unique (parameters and
    /// mutable reborrows), so only `csolver.retag.shared` dsts record `false`. The tag itself
    /// flows dynamically on the pointer value ([`SymPointer::borrow`]), so no static
    /// register→tag map is needed — this only records per-tag uniqueness (a static property).
    pub(crate) unique: HashMap<RegId, bool>,
}

/// Compute [`BorrowInfo`] for `f`: record each `csolver.retag.{mut,shared}` dst's uniqueness.
/// The tag→pointer association is dynamic (`SymPointer::borrow`), so nothing else is precomputed.
pub(crate) fn borrow_info(f: &Function) -> BorrowInfo {
    let mut unique: HashMap<RegId, bool> = HashMap::new();
    for b in &f.blocks {
        for inst in &b.insts {
            if let Inst::Intrinsic { name, args, .. } = inst {
                let is_unique = match name.as_str() {
                    "csolver.retag.mut" => true,
                    "csolver.retag.shared" => false,
                    _ => continue,
                };
                if let Some(d) = args.first().and_then(|o| o.as_reg()) {
                    unique.insert(d, is_unique);
                }
            }
        }
    }
    BorrowInfo { unique }
}

/// The pointer registers derived from a genuine **shared borrow** (`&T`) — a
/// `RefWitness { writable: false, assumed: false }` and anything computed from it by a copy,
/// a pointer cast, a `PtrOffset`, or a `FieldPtr`. A `Store` through such a register is a
/// write through a shared reference, an unambiguous Rust aliasing violation. A fixpoint over
/// the function (defs dominate uses, but a fixpoint is robust to block order). Only shared
/// borrows are seeded — a `&mut` (`writable`) or an opaque/raw pointer never enters the set,
/// so a legitimate write is never flagged. Interior mutability (`&Cell<T>`) writes go through
/// a raw pointer from `UnsafeCell::get` (an opaque call result), which carries no shared tag,
/// so those are not flagged either. Computed only when the aliasing model is enabled.
pub(crate) fn shared_borrow_regs(f: &Function) -> HashSet<RegId> {
    let mut shared: HashSet<RegId> = HashSet::new();
    let mut changed = true;
    while changed {
        changed = false;
        for b in &f.blocks {
            for inst in &b.insts {
                let (dst, is_shared) = match inst {
                    Inst::RefWitness { dst, writable, assumed, .. } => {
                        (Some(*dst), !*writable && !*assumed)
                    }
                    Inst::Assign { dst, value, .. } => {
                        let dep = match value {
                            RValue::Use(o) | RValue::Cast { operand: o, .. } => {
                                o.as_reg().is_some_and(|r| shared.contains(&r))
                            }
                            _ => false,
                        };
                        (Some(*dst), dep)
                    }
                    Inst::PtrOffset { dst, base, .. } => {
                        (Some(*dst), base.as_reg().is_some_and(|r| shared.contains(&r)))
                    }
                    Inst::FieldPtr { dst, base, .. } => {
                        (Some(*dst), base.as_reg().is_some_and(|r| shared.contains(&r)))
                    }
                    _ => (None, false),
                };
                if let Some(d) = dst {
                    if is_shared && shared.insert(d) {
                        changed = true;
                    }
                }
            }
        }
    }
    shared
}

/// The register operands of an r-value.
/// Whether two **sorted, deduplicated** `ExprId` slices share at least one element — a linear
/// merge walk (used by the `branch_infeasible` relevance pre-filter to test variable overlap).
pub(crate) fn sorted_share(a: &[ExprId], b: &[ExprId]) -> bool {
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            std::cmp::Ordering::Equal => return true,
            std::cmp::Ordering::Less => i += 1,
            std::cmp::Ordering::Greater => j += 1,
        }
    }
    false
}

pub(crate) fn rvalue_regs(v: &RValue) -> Vec<RegId> {
    let ops: Vec<&Operand> = match v {
        RValue::Use(o) => vec![o],
        RValue::Bin { lhs, rhs, .. } | RValue::Cmp { lhs, rhs, .. } => vec![lhs, rhs],
        RValue::Cast { operand, .. } => vec![operand],
        RValue::Select { cond, then_val, else_val } => vec![cond, then_val, else_val],
    };
    ops.into_iter().filter_map(|o| o.as_reg()).collect()
}

pub(crate) fn classify_scalar_ptr_defs(f: &Function) -> HashMap<RegId, ScalarPtrCause> {
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
                        RValue::Bin { op, lhs, rhs, .. } => match op {
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
