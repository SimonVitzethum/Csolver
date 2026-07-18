/// A parsed module.
#[derive(Debug, Clone)]
pub struct LModule {
    /// The defined functions that parsed successfully.
    pub funcs: Vec<LFunc>,
    /// `(name, reason)` for functions that failed to parse and were skipped, so
    /// the caller can report them as `UNKNOWN` rather than silently dropping
    /// them.
    pub unanalyzed: Vec<(String, String)>,
    /// Top-level global/static definitions (`@name = … global/constant <ty> …`).
    /// Only definitions whose type parsed are recorded; anything else is skipped
    /// (its symbol then stays an opaque scalar — the sound default).
    pub globals: Vec<LGlobal>,
    /// The debug-info type graph (`!DI…`), for recovering opaque-pointer pointee
    /// types. Empty when the module carries no debug info.
    pub(crate) debuginfo: crate::debuginfo::DebugInfo,
    /// Per global-symbol, the largest `dereferenceable(N)` a bare `@g` use asserts —
    /// an authoritative lower bound on the global's byte size (clang emits it from the
    /// type), used to correct a size the type-layout computation gets wrong.
    pub(crate) deref_hints: std::collections::HashMap<String, u64>,
}

/// A parsed global definition.
#[derive(Debug, Clone)]
pub struct LGlobal {
    /// Symbol name (without the `@`).
    pub name: String,
    /// The definition's type (its size is the region size).
    pub ty: LType,
    /// `false` for `constant` definitions.
    pub writable: bool,
    /// Declared `align` (1 if unspecified).
    pub align: u32,
    /// The type was a *packed* struct `<{ … }>`: its size is the plain sum of
    /// the field sizes (no padding). Packed types stay rejected in instruction
    /// contexts (a padded stand-in could oversize them); here the exact packed
    /// size is computable, so global definitions can be recorded.
    pub packed: bool,
    /// **Function/symbol-pointer fields** of a *constant* initializer: `(byte
    /// offset, symbol name)` for every element that is the address of a named
    /// symbol (`ptr @foo`). Used to devirtualise an indirect call whose target
    /// is loaded from a known constant ops-struct global. Populated only when the
    /// whole initializer's layout could be tracked exactly (else left empty — a
    /// missed field only lowers recall, an imprecise one would be unsound).
    pub fn_ptrs: Vec<(u64, String)>,
}

/// A parsed function definition.
#[derive(Debug, Clone)]
pub struct LFunc {
    /// Function name (without the leading `@`).
    pub name: String,
    /// Return type.
    pub ret: LType,
    /// Parameters, in order.
    pub params: Vec<LParam>,
    /// Basic blocks in textual order (the first is the entry).
    pub blocks: Vec<LBlock>,
    /// `define internal`/`private`: the function is not visible outside this
    /// module, so the module's call sites are all its call sites.
    pub internal: bool,
    /// The `!dbg !N` `DISubprogram` metadata id, if the function carries debug
    /// info — the key into [`crate::debuginfo`] for recovering pointee types.
    pub dbg: Option<u32>,
    /// `#dbg_value(<local>, !V, …)` records: `(local name, !DILocalVariable id)`. Ties an SSA
    /// value to the source variable it holds, so the variable's *declared type* — and hence a
    /// pointer's pointee size — is recoverable at `-O1`/`-O2`, where the struct type is
    /// canonicalised out of the `getelementptr`. See `DebugInfo::local_pointee_bytes`.
    pub dbg_values: Vec<(String, u32)>,
    /// Slice-length fragments: `(!DILocalVariable id, constant length)` from a
    /// `#dbg_value(iN <len>, !V, !DIExpression(DW_OP_LLVM_fragment, 64, 64))` record — the
    /// length field of a Rust fat pointer (`&[T]`/`&mut [T]`, a 128-bit `{data, len}`). Joined
    /// by `!V` with the pointer fragment in [`LFunc::dbg_values`] to size a slice region:
    /// a `from_raw_parts(ptr, N)` slice erases to a bare pointer at `-O`, but the source-level
    /// length survives here. See `DebugInfo::slice_ref_elem` and the lowering that seeds it.
    pub dbg_slice_lens: Vec<(u32, u64)>,
}

/// A parsed function parameter with the attributes relevant to memory safety.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LParam {
    /// Parameter type.
    pub ty: LType,
    /// Local name (empty if unnamed).
    pub name: String,
    /// `dereferenceable(N)`: bytes guaranteed valid behind a pointer.
    pub deref: Option<u64>,
    /// `sret(T)` / `byval(T)`: the pointer refers to a caller-provided buffer of
    /// `sizeof(T)` bytes (the ABI for returning / passing an aggregate by value).
    /// Semantically a `dereferenceable(sizeof(T))`; kept as the type so the
    /// lowering computes the size with its layout.
    pub abi_buf: Option<LType>,
    /// `align N`.
    pub align: Option<u32>,
    /// `readonly`.
    pub readonly: bool,
    /// `writeonly`.
    pub writeonly: bool,
    /// `nonnull`: the pointer is guaranteed non-null (no size/liveness guarantee).
    pub nonnull: bool,
}

/// A parsed basic block.
#[derive(Debug, Clone)]
pub struct LBlock {
    /// The block label.
    pub label: String,
    /// Leading `phi` instructions (become MSIR block parameters).
    pub phis: Vec<LPhi>,
    /// Straight-line instructions.
    pub insts: Vec<LInst>,
    /// The terminator.
    pub term: LTerm,
}

/// A `phi` node: `dst = phi ty [v, %pred], ...`.
#[derive(Debug, Clone)]
pub struct LPhi {
    /// Destination register name.
    pub dst: String,
    /// Value type.
    pub ty: LType,
    /// `(incoming value, predecessor label)` pairs.
    pub incomings: Vec<(LValue, String)>,
}

/// A parsed LLVM type (subset).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LType {
    /// `void`.
    Void,
    /// `iN`.
    Int(u32),
    /// `ptr` (or legacy `T*`).
    Ptr,
    /// `[N x T]`.
    Array(Box<LType>, u64),
    /// `<N x T>` (a vector — modelled by its byte size).
    Vector(Box<LType>, u64),
    /// `{ T, T, … }` (an aggregate — e.g. the `{iN, i1}` of a checked-arithmetic
    /// intrinsic; destructured by `extractvalue`, not used directly).
    Struct(Vec<LType>),
    /// `<{ T, T, … }>` — a *packed* struct (no inter-field padding, byte
    /// alignment). Modelled with an exact packed layout, so — unlike a padded
    /// stand-in — it never oversizes. Swift lowers every type to a packed struct.
    PackedStruct(Vec<LType>),
    /// `%"name"` — a reference to a top-level `%"name" = type { … }` definition.
    /// Resolved by [`Parser::ltype`] against the collected definitions before it
    /// leaves the parser; reaching the lowering unresolved is a parser bug.
    Named(String),
    /// `metadata` — a compiler-annotation operand (`llvm.assume`,
    /// `llvm.experimental.noalias.scope.decl`, …). Zero-sized; never memory.
    Metadata,
}

/// A parsed operand value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LValue {
    /// `%name`.
    Local(String),
    /// An integer literal (`true`/`false` map to 1/0).
    Int(i128),
    /// `null`.
    Null,
    /// `undef` / `poison`.
    Undef,
    /// `@name`.
    Global(String),
    /// A folded `getelementptr` constant expression into a global:
    /// `@name` displaced by `index` elements of `elem`.
    GlobalOff {
        /// The base symbol.
        name: String,
        /// Element type of the constant gep (byte stride).
        elem: LType,
        /// Element index.
        index: i128,
    },
}

/// Integer binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LBin {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    URem,
    SRem,
    And,
    Or,
    Xor,
    Shl,
    LShr,
    AShr,
}

/// Comparison predicates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LPred {
    Eq,
    Ne,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
}

/// Cast operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LCast {
    Trunc,
    ZExt,
    SExt,
    PtrToInt,
    IntToPtr,
    Bitcast,
}

/// The memory-ordering of an atomic access (LLVM `load atomic`/`store atomic`).
/// Only the acquire/release/seq_cst distinction matters here — it is lowered into
/// the weak-memory fence the ordering guarantees (a release orders prior writes
/// before the store, an acquire orders later reads after the load).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LOrdering {
    /// Non-atomic, or `unordered`/`monotonic` (no synchronising order).
    #[default]
    None,
    /// `acquire` — on a load, orders subsequent reads after it.
    Acquire,
    /// `release` — on a store, orders prior writes before it.
    Release,
    /// `acq_rel` — both (an RMW).
    AcqRel,
    /// `seq_cst` — a full barrier.
    SeqCst,
}

/// A parsed straight-line instruction.
#[derive(Debug, Clone)]
pub enum LInst {
    /// `dst = alloca ty[, align n]`.
    Alloca { dst: String, ty: LType, align: u32 },
    /// `dst = load ty, ptr p[, align n]`.
    Load {
        dst: String,
        ty: LType,
        ptr: LValue,
        align: u32,
        align_meta: Option<u32>,
        /// `atomic`/`volatile` — a race-free access (excluded from the data-race pass).
        atomic: bool,
        /// The atomic memory-ordering (for the weak-memory fence lowering).
        ordering: LOrdering,
    },
    /// `store ty v, ptr p[, align n]`.
    Store {
        ty: LType,
        val: LValue,
        ptr: LValue,
        align: u32,
        /// `atomic`/`volatile` — a race-free access (excluded from the data-race pass).
        atomic: bool,
        /// The atomic memory-ordering (for the weak-memory fence lowering).
        ordering: LOrdering,
    },
    /// `dst = getelementptr [inbounds] elem, ptr base, i.. index`.
    Gep {
        dst: String,
        elem: LType,
        base: LValue,
        index: LValue,
    },
    /// A binary op.
    Bin {
        dst: String,
        op: LBin,
        ty: LType,
        a: LValue,
        b: LValue,
        /// `nsw` flag was present (signed no-wrap).
        nsw: bool,
        /// `nuw` flag was present (unsigned no-wrap).
        nuw: bool,
    },
    /// `dst = icmp pred ty a, b`.
    Icmp {
        dst: String,
        pred: LPred,
        ty: LType,
        a: LValue,
        b: LValue,
    },
    /// A cast.
    Cast {
        dst: String,
        op: LCast,
        val: LValue,
        to: LType,
    },
    /// `[dst =] call ret @callee(args)`.
    Call {
        dst: Option<String>,
        ret: LType,
        callee: String,
        args: Vec<LValue>,
    },
    /// `dst = extractvalue AGG %agg, index` — a field of an aggregate value (the
    /// first index only; nested indices are skipped). Used to recover a
    /// checked-arithmetic tuple's sum (index 0) and overflow flag (index 1).
    ExtractValue {
        dst: String,
        agg: LValue,
        index: u32,
    },
    /// `dst = atomicrmw <op> ptr p, T v <ord>` / `dst = cmpxchg ptr p, T c, T n
    /// <ord> <ord>` — an atomic read-modify-write of `sizeof(T)` bytes at `p`.
    /// At this abstraction both are a *load* (the returned old value) plus a
    /// *store* of an unknown value; `tuple` marks cmpxchg's `{T, i1}` result,
    /// which stays opaque (destructured by `extractvalue`).
    AtomicRmw {
        dst: String,
        ty: LType,
        ptr: LValue,
        tuple: bool,
    },
    /// `dst = getelementptr {S}, ptr base, iN index, i32 field` — an array-of-
    /// structs element's *field*: `base + index * sizeof(S) + offsetof(S, field)`.
    /// Lowered as a two-step pointer-offset chain with the exact padded field
    /// offset (a dropped field offset would misplace every subsequent access).
    GepField {
        dst: String,
        struct_ty: LType,
        base: LValue,
        index: LValue,
        field: u32,
    },
    /// A **multi-level** gep into a nested aggregate with an all-constant navigation
    /// path: `base + index * sizeof(agg) + offsetof(agg, path)` where `path` walks
    /// struct fields and constant array indices (`gep %S, ptr, i, K1, K2, …`). The
    /// exact nested byte offset is resolved at lowering from the type layout. This
    /// is pervasive in real C/kernel IR; without it the whole function was dropped.
    GepChain {
        dst: String,
        agg_ty: LType,
        base: LValue,
        indices: Vec<LValue>,
        /// The LLVM name of the aggregate type when it was a named struct/union
        /// (`%struct.cred` ⇒ `Some("struct.cred")`), captured before `ltype` resolved the
        /// reference away. Bridges the gep to its `DICompositeType` so field pointees load
        /// through the base (see `DebugInfo::composite_by_llvm_name`). `None` for an anonymous
        /// aggregate or a non-`-g` build.
        struct_name: Option<String>,
    },
    /// A value the frontend models opaquely — e.g. `landingpad`'s exception
    /// object, which carries no memory-safety content. Lowered to `undef` (sound;
    /// unconstrained), so a function that merely has an unwind-cleanup path is
    /// analysed rather than dropped whole.
    /// `fence [syncscope(…)] <ordering>` — an atomic memory fence. It carries no
    /// memory-safety obligation of its own; lowered to the matching weak-memory `Barrier`.
    Fence { ordering: LOrdering },
    Opaque { dst: String },
    /// `dst = select i1 cond, T a, T b` — an operand-level select. Kept (not opaque)
    /// so a pointer select becomes a provenance join and a scalar select an `ite`.
    Select { dst: String, cond: LValue, then_val: LValue, else_val: LValue },
}

/// A parsed terminator.
#[derive(Debug, Clone)]
pub enum LTerm {
    /// `ret void` / `ret ty v`.
    Ret(Option<LValue>),
    /// `br label %dest`.
    Br(String),
    /// `br i1 c, label %t, label %f`.
    CondBr(LValue, String, String),
    /// `switch iN %v, label %default [ iN c0, label %d0 ... ]`.
    Switch {
        /// The scrutinee.
        value: LValue,
        /// Bit width of the scrutinee (and every case constant).
        width: u32,
        /// The default destination.
        default: String,
        /// `(case constant, destination)` pairs.
        cases: Vec<(i128, String)>,
    },
    /// `unreachable`.
    Unreachable,
    /// `[dst =] invoke ret @callee(args) to label %ok unwind label %cleanup` — a
    /// call with a normal and an unwind successor. Lowered to a `Call` instruction
    /// plus a branch to *both* edges (the unwind/cleanup path may run `Drop` code,
    /// whose memory safety must still be checked).
    Invoke {
        dst: Option<String>,
        ret: LType,
        callee: String,
        args: Vec<LValue>,
        ok: String,
        cleanup: String,
    },
    /// `[dst =] callbr … asm …(args) to label %ft [label %t1, …]` — an inline-asm
    /// **goto**: an opaque asm effect whose control may continue at the fallthrough
    /// or any listed label. Pervasive in the kernel (static keys, exception tables).
    /// Lowered to an asm havoc + a branch to *every* target (sound over-approximation).
    CallBr {
        dst: Option<String>,
        targets: Vec<String>,
    },
}
