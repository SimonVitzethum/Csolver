use super::*;

/// The base a materialised field region is keyed by: a tracked region, or an opaque
/// provenance identity (so `obj->field` off an *opaque* object also gets a stable region).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum RefBase {
    Region(usize),
    Opaque(u32),
}

/// The identity a **typestate resource** is keyed by: a pointer handle's base (a `FILE*`,
/// a lock, a struct) or a scalar value's identity (an `fd` integer — the same SSA value
/// denotes the same fd). General over both pointer and non-pointer resources.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ResKey {
    Ptr(RefBase),
    Val(ExprId),
}

/// Provenance of a symbolic pointer.
#[derive(Debug, Clone)]
pub(crate) enum Prov {
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
pub(crate) enum POrigin {
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

impl POrigin {
    /// The residual reason string (the bucket key the sweep aggregates on).
    pub(crate) fn residual(self) -> &'static str {
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
    pub(crate) fn provenance_residual(&self) -> &'static str {
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

#[derive(Debug, Clone)]
pub(crate) struct SymPointer {
    pub(crate) prov: Prov,
    pub(crate) offset: ExprId,
    pub(crate) align: u64,
    /// **Borrow tag** for the opt-in aliasing model (`--aliasing-model`): the retag-dst (or
    /// `&mut`-parameter) register this pointer's borrow belongs to. It flows with the pointer
    /// *value* — through copies, `gep`, and crucially **through memory (store→load) and
    /// block-parameter merges** that the static register pre-pass cannot follow. Purely
    /// diagnostic metadata: **deliberately excluded from `PartialEq`/`Eq`** (see below), so
    /// aliasing, merging and every existing verdict stay byte-identical to before it existed.
    /// `None` for a pointer with no tracked borrow. Set only when the model is on.
    pub(crate) borrow: Option<RegId>,
}

// Pointer equality is over `(prov, offset, align)` only: the borrow tag is metadata that must
// not affect aliasing/merge/any verdict (the same discipline as `Prov`'s excluded `POrigin`).
impl PartialEq for SymPointer {
    fn eq(&self, other: &Self) -> bool {
        self.prov == other.prov && self.offset == other.offset && self.align == other.align
    }
}
impl Eq for SymPointer {}

#[derive(Debug, Clone)]
pub(crate) struct SymRegion {
    pub(crate) kind: RegionKind,
    pub(crate) size: ExprId,
    /// The region base's **guaranteed** alignment (a sound under-approximation — powers of two).
    /// The base address is `≡ 0 (mod base_align)`, so an access at a symbolic offset is aligned to
    /// `A` when `base_align ≥ A` and the offset is provably `≡ 0 (mod A)` (see `check_access`).
    pub(crate) base_align: u64,
    pub(crate) state: LifetimeState,
    pub(crate) perms: Permissions,
    /// If this region models a caller-guaranteed pointer parameter, the named
    /// assumption its validity rests on (`param-contracts` / `slice-abi`);
    /// `None` for a freshly-allocated region (which rests on `alloc-succeeds`).
    pub(crate) contract: Option<&'static str>,
    /// `Some(fact)` when the byte size is known not to wrap (`fact` is the
    /// `count <= isize::MAX/stride` premise, trivially `true` for a concrete
    /// size). Then a memory-OOB obligation over the region is **refutable** with
    /// a faithful witness, with `fact` added to the refutation query only (not to
    /// the proving assumptions, to keep proofs cheap). `None` ⇒ not refutable.
    pub(crate) size_nowrap: Option<ExprId>,
    /// `Some(elem_bytes)` if the region is **sentinel-terminated**: a zero element
    /// of that width lies before its end. A sequential `while (p[n] != 0)` scan
    /// over it is then bounded (it must stop at the sentinel), which lets a
    /// `strlen`-shaped loop be proved. `None` for an ordinary region.
    pub(crate) sentinel: Option<u64>,
    /// `true` if the region has been filled with untrusted **user data** (via a
    /// `copy_from_user`-style `MemIntrinsic::UserFill`). A value later loaded from
    /// it is a *genuine adversarial input* — refutable like a parameter — so a
    /// length read back from a user-copied struct can drive an out-of-bounds FAIL.
    pub(crate) user_controlled: bool,
    /// `true` if this region models a raw pointer only **assumed** valid under the
    /// `--assume-valid-params` opt-in (a `RefWitness { assumed }`), so its byte size
    /// is a caller-supplied *guess* (e.g. from DWARF), not a proven allocation bound.
    /// A constant-offset "OOB" against such a region — the pervasive `container_of`
    /// backward step, or a fixed field past the guessed size — is an artifact of the
    /// guess, not a real bug: refuting it would be a false FAIL. Only an OOB the code
    /// drives with a *genuine input* offset is reported (see `check_access`).
    pub(crate) assumed: bool,
    /// The region's **provenance labels** (interned ids), set by [`Inst::ProvLabel`] and
    /// accumulated by [`Inst::ProvPropagate`] (a container unions in each element's labels).
    /// Empty = unlabelled, which grants every capability (the sound default). An
    /// [`Inst::CapRequire`] refutes iff **some** label in the set provably lacks the cap —
    /// a container is only as capable as its least-capable member.
    pub(crate) prov_labels: FxHashSet<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SymValue {
    Scalar(ExprId),
    Ptr(SymPointer),
}

/// Captured data for asserting a pointer equality-exit induction's offset bound
/// (`iter != end`), taken before the loop header havoc clobbers `iter`.
pub(crate) struct PtrIndCapture {
    /// The induction pointer register (a header block-parameter).
    pub(crate) reg: RegId,
    /// The allocation `iter` walks within.
    pub(crate) region: usize,
    /// `iter`'s start offset (its preheader value's offset).
    pub(crate) b0: ExprId,
    /// `iter`'s start alignment.
    pub(crate) align: u64,
    /// The end pointer's offset within the same allocation.
    pub(crate) end_off: ExprId,
    /// The allocation's byte size.
    pub(crate) size: ExprId,
    /// The per-iteration byte stride (`elem size × element step`).
    pub(crate) stride_bytes: u64,
    /// `true` for the rotated form (load precedes the `next == end` check): the
    /// bound is `o + stride ≤ end_off` and its base case is proved from the
    /// preheader guard. `false` for the header-test form (`o ≤ end_off`).
    pub(crate) bottom_test: bool,
}
