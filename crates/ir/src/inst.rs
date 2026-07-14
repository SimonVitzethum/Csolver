//! MSIR operands, r-values, conditions and instructions.

use crate::id::RegId;
use crate::ty::Type;
use csolver_core::{RegionKind, SafetyProperty};

/// A compile-time-constant operand.
pub use crate::ops::*;

/// A single MSIR instruction. Instructions are the straight-line body of a
/// [`crate::BasicBlock`]; control flow lives in its [`crate::Terminator`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Inst {
    /// Define a register from a pure r-value.
    Assign {
        /// Destination register.
        dst: RegId,
        /// Its declared type.
        ty: Type,
        /// The computation.
        value: RValue,
    },
    /// Read `ty` from `ptr`. Implies `ValidRead`, `InBounds`, `Alignment`,
    /// `NoNullDeref`, `NoUseAfterFree`.
    Load {
        /// Destination register.
        dst: RegId,
        /// Type loaded.
        ty: Type,
        /// Address.
        ptr: Operand,
        /// Required alignment in bytes.
        align: u32,
        /// An `atomic`/`volatile` access (`READ_ONCE`/`atomic_*`) — **race-free by
        /// construction**, so the data-race pass excludes it. Does not affect any
        /// memory-safety obligation (the access is still checked).
        volatile: bool,
    },
    /// Write `value: ty` to `ptr`. Implies `ValidWrite`, `InBounds`,
    /// `Alignment`, `NoNullDeref`, `NoUseAfterFree`.
    Store {
        /// Type stored.
        ty: Type,
        /// Address.
        ptr: Operand,
        /// Value written.
        value: Operand,
        /// Required alignment in bytes.
        align: u32,
        /// An `atomic`/`volatile` access (`WRITE_ONCE`/`atomic_*`) — **race-free by
        /// construction**, so the data-race pass excludes it.
        volatile: bool,
    },
    /// Allocate `count` elements of `elem` in `region`, yielding a pointer.
    Alloc {
        /// Destination register (the new pointer).
        dst: RegId,
        /// Which region.
        region: RegionKind,
        /// Element type.
        elem: Type,
        /// Element count.
        count: Operand,
        /// Alignment in bytes.
        align: u32,
    },
    /// Free a heap allocation. Implies `NoDoubleFree` and that `ptr` is the
    /// base of a live allocation.
    Dealloc {
        /// Which region.
        region: RegionKind,
        /// The pointer being freed.
        ptr: Operand,
    },
    /// Compute `base + index * sizeof(elem)`. Implies `ValidPointerArith`.
    PtrOffset {
        /// Destination register.
        dst: RegId,
        /// Base pointer.
        base: Operand,
        /// Element index (signed).
        index: Operand,
        /// Element type (the scale).
        elem: Type,
    },
    /// A pointer to field `field` (of `size` bytes, `align`-aligned) within the
    /// struct/aggregate that `base` points to. Unlike [`Inst::PtrOffset`] the byte
    /// offset is *not* computed: a typed field access through a valid reference is
    /// in bounds and aligned by construction (the field lies within the
    /// aggregate). The engine models this with a fresh symbolic offset constrained
    /// to fit, which avoids reconstructing a struct layout — that layout is absent
    /// from MIR and unspecified for `repr(Rust)`.
    FieldPtr {
        /// Destination register (the field pointer).
        dst: RegId,
        /// Base pointer to the aggregate.
        base: Operand,
        /// Field index.
        field: u32,
        /// Field size in bytes.
        size: u64,
        /// Field alignment in bytes.
        align: u64,
    },
    /// A call. The callee's summary supplies the effect; opaque callees emit an
    /// explicit assumption.
    Call {
        /// Destination register for the result, if any.
        dst: Option<RegId>,
        /// Who is called.
        callee: Callee,
        /// Arguments.
        args: Vec<Operand>,
        /// Result type.
        ret_ty: Type,
        /// When the result is a *reference* (`&T`/`&mut T`), the pointee's byte
        /// size (`None` = unsized) and mutability. Rust guarantees a returned
        /// reference is valid, so — absent a more precise callee summary — the
        /// engine materialises it as a valid-reference region instead of an
        /// opaque pointer. `None` for a non-reference result (raw pointer,
        /// scalar): the callee could return anything.
        ret_ref: Option<RefResult>,
    },
    /// Inline assembly, modelled opaquely unless a semantics is supplied.
    Asm {
        /// The assembly template (for reporting).
        template: String,
        /// Registers it may clobber/define.
        defs: Vec<RegId>,
    },
    /// A recognized intrinsic (lifetime markers, `assume`, …) with no modelled
    /// memory effect.
    Intrinsic {
        /// Destination register, if any.
        dst: Option<RegId>,
        /// Intrinsic name.
        name: String,
        /// Arguments.
        args: Vec<Operand>,
    },
    /// Materialise a *valid reference*: `dst` becomes a pointer to a fresh live
    /// region of `size` bytes (`None` = statically-unknown, e.g. a slice/`str`),
    /// readable and writable iff `writable`. Models a `&T`/`&mut T` value
    /// obtained where the analysis cannot see its origin (a call result, or a
    /// by-value aggregate field): Rust's reference invariant guarantees it is
    /// valid for its pointee, so accesses through it prove — but it is a fresh
    /// region (never aliases anything else), so this only ever *loses* precision.
    RefWitness {
        /// Destination register (the reference pointer).
        dst: RegId,
        /// Byte size of the pointee (`None` = unknown / unsized).
        size: Option<u64>,
        /// Alignment in bytes.
        align: u32,
        /// Whether the reference is mutable (`&mut T`).
        writable: bool,
        /// `true` if the reference's validity rests on the `assume_valid_params`
        /// opt-in (a raw pointer field recovered from debug info) rather than the
        /// type system (a Rust `&T`/C++ `T&`, always valid). The executor
        /// materialises an `assumed` witness only when that mode is on.
        assumed: bool,
        /// The **field address** the reference was loaded from (`&struct->field`),
        /// when known. Lets the executor give two loads of the *same* field the *same*
        /// materialised region (keyed by that address's region + offset), so an in-place
        /// `src == dst` through struct-field loads is recognised. `None` ⇒ always a fresh
        /// region (the sound default; e.g. a Rust `&place` with no field identity).
        src: Option<Operand>,
    },
    /// A bulk memory operation (`memcpy`/`memmove`/`memset`): touches `len`
    /// bytes at `dst` (write) and, for copy/move, `len` bytes at `src` (read).
    MemIntrinsic {
        /// Which bulk operation.
        kind: MemKind,
        /// Destination pointer (written).
        dst: Operand,
        /// Source pointer (read), for copy/move; `None` for set.
        src: Option<Operand>,
        /// Number of bytes touched.
        len: Operand,
    },
    /// An explicit proof obligation embedded in the instruction stream.
    SafetyCheck {
        /// Which property must hold.
        property: SafetyProperty,
        /// The condition establishing it.
        condition: Condition,
        /// A human note describing the origin (e.g. "slice index `a[i]`").
        note: String,
    },
    /// Attach a **provenance label** to the region `ptr` points to (from an external
    /// API contract's `label` effect). The label's granted capabilities live in
    /// [`crate::Module::prov_grants`]; a later [`Inst::CapRequire`] checks them.
    ProvLabel {
        /// The pointer whose region is labelled.
        ptr: Operand,
        /// The interned provenance-label id.
        label: u32,
    },
    /// Require that the region `ptr` points to **grants** capability `cap` (from a
    /// contract's `require` effect). Implies [`SafetyProperty::WriteCapability`]:
    /// refuted when the region's provenance label provably does not grant `cap`
    /// (an unlabelled region grants everything — the sound default).
    CapRequire {
        /// The pointer whose region must grant the capability.
        ptr: Operand,
        /// The interned capability id.
        cap: u32,
    },
    /// **Propagate provenance**: the region `dst` points to absorbs the provenance
    /// labels of the region `src` points to (their union), from a contract's `propagate`
    /// effect. Models a container taking in an element (`sg_set_page`, DMA/io-uring
    /// buffers): a foreign element makes the whole container as restricted as its
    /// least-capable member.
    ProvPropagate {
        /// The pointer whose region absorbs the labels.
        dst: Operand,
        /// The pointer whose labels are absorbed.
        src: Operand,
    },
    /// Like [`Inst::CapRequireIfAlias`], but the two pointers are read from **fields of an
    /// object** (`obj + off_a`, `obj + off_b`) rather than being operands — the inlined-
    /// request form (`req->src`/`req->dst` set by stores, no `set_crypt` call). The executor
    /// reads the fields *internally* (read-your-writes, no `ValidRead`/`InBounds` obligation
    /// on these analyzer reads), then fires iff both fields hold the same region and it lacks
    /// `cap`. Implies [`SafetyProperty::WriteCapability`].
    CapRequireIfAliasFields {
        /// The object holding the two pointer fields (e.g. the crypto request).
        obj: Operand,
        /// Byte offset of the first pointer field.
        off_a: u64,
        /// Byte offset of the second pointer field.
        off_b: u64,
        /// The interned capability the aliased field region must grant.
        cap: u32,
    },
    /// **Conditional capability** (a contract's `require-if-alias`): *iff* `a` and `b`
    /// point into the same region (an in-place `src == dst` operation), that region must
    /// grant `cap`. Implies [`SafetyProperty::WriteCapability`]. The precise Copy-Fail
    /// signature — an in-place crypto op writing a `foreign` page — that does **not** fire
    /// when `a` and `b` are distinct regions (the safe out-of-place path).
    CapRequireIfAlias {
        /// The first pointer (e.g. the crypto source).
        a: Operand,
        /// The second pointer (e.g. the crypto destination).
        b: Operand,
        /// The interned capability the aliased region must grant.
        cap: u32,
    },
    /// **Taint source** (a contract's `taint-source`): mark `val`'s register — and, when it
    /// is a pointer, its region — as tainted with label `taint`. An untrusted input that then
    /// flows to a [`Inst::TaintCheck`] sink.
    TaintSource {
        /// The value (or pointer) that becomes tainted.
        val: Operand,
        /// The interned taint-label id.
        taint: u32,
    },
    /// **Taint sink** (a contract's `taint-sink`): require `val` to be free of taint label
    /// `taint`. Implies [`SafetyProperty::TaintedSink`]: refuted when the value reaching the
    /// sink is definitely tainted with `taint` (a `user`-tainted format string / length /
    /// exec arg). An untainted or sanitised value passes.
    TaintCheck {
        /// The value that must not carry the taint label.
        val: Operand,
        /// The interned taint-label id the value must not carry.
        taint: u32,
    },
    /// **Taint sanitiser** (a contract's `taint-sanitize`): clear taint label `taint` from
    /// `val`'s register (a recognised validation/clamp/escape). A sanitised value passes a
    /// later [`Inst::TaintCheck`].
    TaintClear {
        /// The value whose taint label is cleared.
        val: Operand,
        /// The interned taint-label id cleared.
        taint: u32,
    },
    /// **Typestate transition** (a contract's `typestate-set`): move the resource identified
    /// by `val` (its pointer base or scalar identity) into `state` within `protocol`.
    TypestateSet {
        /// The value naming the resource (a handle pointer or an fd scalar).
        val: Operand,
        /// The interned protocol id.
        protocol: u32,
        /// The interned state id the resource enters.
        state: u32,
    },
    /// **Typestate obligation** (a contract's `typestate-require[-not]`): require the resource
    /// `val` to be (`negate=false`) or not be (`negate=true`) in `state` within `protocol`.
    /// Implies [`SafetyProperty::TypestateViolation`]: refuted when the resource is definitely
    /// in the forbidden state on the path.
    TypestateRequire {
        /// The value naming the resource.
        val: Operand,
        /// The interned protocol id.
        protocol: u32,
        /// The interned state id required or forbidden.
        state: u32,
        /// When `true`, `val` must **not** be in `state`; when `false`, it must be.
        negate: bool,
    },
    /// **Protocol-wide yield** (TOCTOU G2, a contract's `typestate-yield`): transition every
    /// resource of `protocol` in state `from` to state `to` — a yield (blocking call / second
    /// syscall) that invalidates a prior check. Not tied to a value.
    TypestateYield {
        /// The interned protocol id.
        protocol: u32,
        /// The interned state a resource must be in to be affected.
        from: u32,
        /// The interned state such resources move to.
        to: u32,
    },
    /// **Reference-count change** (G8, a contract's `refcount-inc`/`refcount-dec`): raise or
    /// lower the refcount of resource `val` within `protocol`. A `dec` below zero is an
    /// underflow (premature free) — implies [`SafetyProperty::TypestateViolation`].
    Refcount {
        /// The value naming the counted resource.
        val: Operand,
        /// The interned protocol id.
        protocol: u32,
        /// `true` for a decrement (`put`), `false` for an increment (`get`).
        dec: bool,
        /// For an increment, whether it is a **checked** get (`*_inc_not_zero` /
        /// `*_get_unless_zero`) — one that refuses to raise a count that already reached zero, so
        /// it cannot resurrect a dying object and does not race the final `put`. A plain
        /// (unchecked) get concurrent with a `put` is a refcount race (subsystem 4). Ignored for
        /// a decrement.
        checked: bool,
    },
    /// **Leak check at return** (K, from a contract's `typestate-leak`): a resource still in
    /// `state` of `protocol` on this path — and not escaping via `escaping` (the return
    /// value) — is a resource leak. Implies [`SafetyProperty::TypestateViolation`]. Injected
    /// before each `Return` by the frontend.
    TypestateLeakCheck {
        /// The interned protocol id.
        protocol: u32,
        /// The interned leak state id.
        state: u32,
        /// The returned value (if any), whose resource escapes and is not a leak.
        escaping: Option<Operand>,
    },
    /// **Memory barrier** (weak-memory, subsystem 4): recorded in the interleaving trace so the
    /// operational weak-memory model orders accesses accordingly. `kind` 0 = full (`smp_mb`),
    /// 1 = write (`smp_wmb`), 2 = read (`smp_rmb`). No memory-safety effect of its own.
    Barrier {
        /// 0 = full, 1 = write, 2 = read.
        kind: u8,
        /// `Some(ptr)` when the barrier call also accesses this location (a
        /// `smp_store_release`/`smp_load_acquire`: `kind` 1 ⇒ a write, `kind` 2 ⇒ a read),
        /// so the message-passing flag is recorded, not just the ordering. `None` = a
        /// standalone fence.
        access: Option<Operand>,
    },
    /// **Thread spawn** (weak-memory happens-before): recorded in the interleaving trace so the
    /// model gates the child thread (`child` is its function name). No memory-safety effect.
    Spawn {
        /// The spawned child's function name.
        child: String,
    },
    /// **Thread join** (weak-memory happens-before): recorded in the interleaving trace so the
    /// model orders the joined children before the parent's later events. No memory-safety effect.
    Join,
    /// **Compare-and-swap** on `val` (ABA detection): recorded in the interleaving trace so a
    /// concurrent modification of the same location (A→B→A) is flagged. No memory-safety effect.
    Cas {
        /// The CAS location pointer.
        val: Operand,
    },
    /// **Secret-dependence check** (constant-time L): `val` (a branch condition or a `gep`
    /// index) must not carry the `secret` taint label. Implies
    /// [`SafetyProperty::SecretDependent`]. Injected by the frontend at every branch and
    /// memory index **only when** a `secret` taint label is defined by the contracts.
    SecretCheck {
        /// The deciding value (branch condition or memory index).
        val: Operand,
        /// The interned `secret` taint-label id.
        taint: u32,
    },
}

/// The reference-validity facts a call's `&T`/`&mut T` result carries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RefResult {
    /// Byte size of the pointee (`None` = unsized / slice).
    pub size: Option<u64>,
    /// Whether the reference is mutable.
    pub writable: bool,
}

impl Inst {
    /// The canonical memory-safety properties this instruction implies.
    ///
    /// These are the obligations a verifier must discharge for the instruction,
    /// in addition to any explicit [`Inst::SafetyCheck`]s. An `Alloc` implies
    /// none here (allocation success is treated as an explicit assumption).
    pub fn implied_checks(&self) -> &'static [SafetyProperty] {
        use SafetyProperty::*;
        match self {
            Inst::Load { .. } => &[NoNullDeref, NoUseAfterFree, InBounds, Alignment, ValidRead],
            Inst::Store { .. } => &[NoNullDeref, NoUseAfterFree, InBounds, Alignment, ValidWrite],
            Inst::Dealloc { .. } => &[NoDoubleFree],
            // Bug-finding only (the verifier does not enumerate it in sound mode): an
            // attacker-controlled `count * sizeof(T)` size must not overflow and
            // under-allocate.
            Inst::Alloc { .. } => &[NoSizeOverflow],
            Inst::PtrOffset { .. } => &[ValidPointerArith],
            Inst::MemIntrinsic { kind, .. } => match kind {
                MemKind::Set => &[NoNullDeref, NoUseAfterFree, InBounds, ValidWrite],
                // A `copy_from_user` also carries the double-fetch obligation (bug-finding
                // only): re-reading the same user address on one path is a TOCTOU race.
                MemKind::UserFill => &[NoNullDeref, NoUseAfterFree, InBounds, ValidWrite, DoubleFetch],
                // `memcpy` additionally requires the source and destination ranges NOT
                // to overlap (overlap is UB — that is what `memmove` is for). `memmove`
                // permits overlap, so it carries no such obligation.
                MemKind::Copy => {
                    &[NoNullDeref, NoUseAfterFree, InBounds, ValidRead, ValidWrite, NoForbiddenOverlap]
                }
                MemKind::Move => {
                    &[NoNullDeref, NoUseAfterFree, InBounds, ValidRead, ValidWrite]
                }
                MemKind::UserDrain => {
                    &[NoNullDeref, NoUseAfterFree, InBounds, ValidRead, NoInfoLeak]
                }
            },
            Inst::CapRequire { .. } => &[WriteCapability],
            Inst::CapRequireIfAlias { .. } => &[WriteCapability],
            Inst::CapRequireIfAliasFields { .. } => &[WriteCapability],
            Inst::TaintCheck { .. } => &[TaintedSink],
            Inst::TypestateRequire { .. } => &[TypestateViolation],
            Inst::Refcount { .. } => &[TypestateViolation],
            Inst::TypestateLeakCheck { .. } => &[TypestateViolation],
            Inst::SecretCheck { .. } => &[SecretDependent],
            // A freeing-wrapper call must not re-free a pointer an earlier freeing call
            // already freed (`NoDoubleFree`); a lock-acquiring call must not re-acquire a
            // held lock (`DataRace`, bug-finding only).
            // An indirect call also carries the valid-target obligation (the function
            // pointer must not be null/invalid); a direct/symbol call cannot be.
            Inst::Call { callee: Callee::Indirect(_), .. } => {
                &[NoDoubleFree, DataRace, SleepInAtomic, TypestateViolation, ValidIndirectTarget]
            }
            Inst::Call { .. } => &[NoDoubleFree, DataRace, SleepInAtomic, TypestateViolation],
            // A division or modulo carries the divisor-non-zero obligation (bug-finding only).
            Inst::Assign {
                value:
                    RValue::Bin {
                        op: BinOp::UDiv | BinOp::SDiv | BinOp::URem | BinOp::SRem,
                        ..
                    },
                ..
            } => &[NoDivByZero],
            // A shift carries the shift-amount-in-range obligation (bug-finding only).
            Inst::Assign {
                value: RValue::Bin { op: BinOp::Shl | BinOp::LShr | BinOp::AShr, .. },
                ..
            } => &[NoShiftOverflow],
            // An `nsw`/`nuw`-flagged add/sub/mul carries the no-overflow obligation
            // (bug-finding only). Unflagged arithmetic wraps and raises nothing.
            Inst::Assign {
                value:
                    RValue::Bin {
                        op: BinOp::Add | BinOp::Sub | BinOp::Mul,
                        flags,
                        ..
                    },
                ..
            } if flags.nsw || flags.nuw => &[NoArithOverflow],
            _ => &[],
        }
    }

    /// The register this instruction defines, if any.
    pub fn defined_reg(&self) -> Option<RegId> {
        match self {
            Inst::Assign { dst, .. }
            | Inst::Load { dst, .. }
            | Inst::Alloc { dst, .. }
            | Inst::PtrOffset { dst, .. }
            | Inst::FieldPtr { dst, .. }
            | Inst::RefWitness { dst, .. } => Some(*dst),
            Inst::Call { dst, .. } | Inst::Intrinsic { dst, .. } => *dst,
            Inst::Store { .. }
            | Inst::Dealloc { .. }
            | Inst::Asm { .. }
            | Inst::SafetyCheck { .. }
            | Inst::ProvLabel { .. }
            | Inst::CapRequire { .. }
            | Inst::ProvPropagate { .. }
            | Inst::CapRequireIfAlias { .. }
            | Inst::CapRequireIfAliasFields { .. }
            | Inst::TaintSource { .. }
            | Inst::TaintCheck { .. }
            | Inst::TaintClear { .. }
            | Inst::TypestateSet { .. }
            | Inst::TypestateRequire { .. }
            | Inst::TypestateYield { .. }
            | Inst::Refcount { .. }
            | Inst::TypestateLeakCheck { .. }
            | Inst::SecretCheck { .. }
            | Inst::Barrier { .. }
            | Inst::Spawn { .. }
            | Inst::Join
            | Inst::Cas { .. }
            | Inst::MemIntrinsic { .. } => None,
        }
    }
}
