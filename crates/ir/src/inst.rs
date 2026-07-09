//! MSIR operands, r-values, conditions and instructions.

use crate::id::{FuncId, RegId};
use crate::ty::Type;
use csolver_core::{BitVector, RegionKind, SafetyProperty};

/// A compile-time-constant operand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Const {
    /// A fixed-width integer constant.
    Int(BitVector),
    /// The null pointer.
    Null,
    /// An undefined value (`undef`/`poison`): reading it is itself a safety
    /// concern and is tracked as such.
    Undef,
    /// The address of a named symbol (global / function).
    Symbol(String),
    /// The address of a named symbol plus a constant byte offset — a folded
    /// `getelementptr` constant expression into a global.
    SymbolOffset(String, i64),
}

/// An instruction operand: either an SSA register or a constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operand {
    /// A previously-defined SSA value.
    Reg(RegId),
    /// A constant.
    Const(Const),
}

impl Operand {
    /// Convenience: an integer constant operand.
    pub fn int(width: u32, value: u128) -> Operand {
        Operand::Const(Const::Int(BitVector::new(width, value)))
    }

    /// If this operand is a register, its id.
    pub fn as_reg(&self) -> Option<RegId> {
        match self {
            Operand::Reg(r) => Some(*r),
            Operand::Const(_) => None,
        }
    }
}

/// Binary arithmetic / bitwise operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Multiplication.
    Mul,
    /// Unsigned division.
    UDiv,
    /// Signed division.
    SDiv,
    /// Unsigned remainder.
    URem,
    /// Signed remainder.
    SRem,
    /// Bitwise and.
    And,
    /// Bitwise or.
    Or,
    /// Bitwise xor.
    Xor,
    /// Shift left.
    Shl,
    /// Logical shift right.
    LShr,
    /// Arithmetic shift right.
    AShr,
}

/// Integer comparison predicates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOp {
    /// Equal.
    Eq,
    /// Not equal.
    Ne,
    /// Unsigned less-than.
    Ult,
    /// Unsigned less-or-equal.
    Ule,
    /// Unsigned greater-than.
    Ugt,
    /// Unsigned greater-or-equal.
    Uge,
    /// Signed less-than.
    Slt,
    /// Signed less-or-equal.
    Sle,
    /// Signed greater-than.
    Sgt,
    /// Signed greater-or-equal.
    Sge,
}

/// Conversion operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CastOp {
    /// Truncate to a narrower integer.
    Trunc,
    /// Zero-extend to a wider integer.
    ZExt,
    /// Sign-extend to a wider integer.
    SExt,
    /// Reinterpret a pointer as an integer (loses, then must re-derive,
    /// provenance — flagged for the memory model).
    PtrToInt,
    /// Reinterpret an integer as a pointer (provenance must be re-established).
    IntToPtr,
    /// Same-size reinterpretation.
    Bitcast,
}

/// The right-hand side of a register-defining assignment (a pure computation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RValue {
    /// Copy an operand.
    Use(Operand),
    /// A binary operation.
    Bin {
        /// Operator.
        op: BinOp,
        /// Left operand.
        lhs: Operand,
        /// Right operand.
        rhs: Operand,
    },
    /// A comparison producing an `i1`.
    Cmp {
        /// Predicate.
        op: CmpOp,
        /// Left operand.
        lhs: Operand,
        /// Right operand.
        rhs: Operand,
    },
    /// A type conversion.
    Cast {
        /// Conversion kind.
        op: CastOp,
        /// Value being converted.
        operand: Operand,
        /// Target type.
        to: Type,
    },
}

/// A boolean predicate over operands, used to express a [`Inst::SafetyCheck`]
/// condition without yet committing to the solver's constraint IR.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Condition {
    /// Always true (a discharged/vacuous check).
    True,
    /// A comparison.
    Cmp {
        /// Predicate.
        op: CmpOp,
        /// Left operand.
        lhs: Operand,
        /// Right operand.
        rhs: Operand,
    },
    /// Conjunction.
    And(Vec<Condition>),
    /// Disjunction.
    Or(Vec<Condition>),
    /// Negation.
    Not(Box<Condition>),
}

/// Which bulk memory operation an [`Inst::MemIntrinsic`] performs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemKind {
    /// `memcpy`: copy, non-overlapping.
    Copy,
    /// `memmove`: copy, may overlap.
    Move,
    /// `memset`: fill with a byte value.
    Set,
    /// A `copy_from_user`-style bulk write of **untrusted user data** into the
    /// destination (kernel) buffer: bounds-checked like `Set`, but it additionally
    /// marks the destination region user-controlled, so a value later loaded from it
    /// is a *genuine adversarial input* (an attacker picks it) — a length read back
    /// from a user-copied struct can then drive a refutable overflow.
    UserFill,
    /// A `copy_to_user`-style bulk **read** of the kernel source buffer that is
    /// disclosed to userspace: bounds-checked like a read, and additionally
    /// carries the `NoInfoLeak` obligation — the copied source bytes must have
    /// been initialized (a never-written freshly-allocated buffer copied out is a
    /// kernel information leak).
    UserDrain,
}

/// The target of a [`Inst::Call`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Callee {
    /// A direct call to a known function in this module.
    Direct(FuncId),
    /// A call to an externally-named symbol (FFI / not-yet-resolved).
    Symbol(String),
    /// An indirect call through a computed pointer.
    Indirect(Operand),
}

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
                MemKind::Set | MemKind::UserFill => {
                    &[NoNullDeref, NoUseAfterFree, InBounds, ValidWrite]
                }
                MemKind::Copy | MemKind::Move => {
                    &[NoNullDeref, NoUseAfterFree, InBounds, ValidRead, ValidWrite]
                }
                MemKind::UserDrain => {
                    &[NoNullDeref, NoUseAfterFree, InBounds, ValidRead, NoInfoLeak]
                }
            },
            Inst::CapRequire { .. } => &[WriteCapability],
            Inst::CapRequireIfAlias { .. } => &[WriteCapability],
            Inst::CapRequireIfAliasFields { .. } => &[WriteCapability],
            // A freeing-wrapper call must not re-free a pointer an earlier freeing call
            // already freed (`NoDoubleFree`); a lock-acquiring call must not re-acquire a
            // held lock (`DataRace`, bug-finding only).
            Inst::Call { .. } => &[NoDoubleFree, DataRace],
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
            | Inst::MemIntrinsic { .. } => None,
        }
    }
}
