//! Function summaries for interprocedural analysis.
//!
//! A [`Summary`] captures the two things a caller needs to reason about a call
//! without re-analyzing the callee from scratch:
//!
//! * **Effects** — does the callee write to, or free, caller-visible memory?
//!   Computed conservatively and propagated to a fixpoint over the call graph
//!   (so recursion and transitive impurity are handled). A call to a *pure*
//!   function need not invalidate the caller's symbolic heap.
//! * **Return value** — when the result is a parameter pointer offset by an
//!   affine function of the parameters (the ubiquitous wrapper / accessor
//!   shape), the summary records that so the caller can rebuild the result
//!   pointer *with its original provenance*. This is what makes pointer-
//!   returning helpers transparent to the memory-safety proof.
//!
//! Everything here is parameter-relative data (no expressions / no solver); the
//! caller instantiates a summary against its actual arguments.

use csolver_core::RegionKind;
use csolver_ir::{
    BinOp, BlockId, Callee, Const, DataLayout, FuncId, Function, Inst, Module, Operand, RValue,
    RegId,
};
use std::collections::{BTreeMap, HashMap};

const LAYOUT: DataLayout = DataLayout::LP64;

/// An affine form `constant + Σ coeff_k · param_k` over a function's parameters
/// (identified by their positional index).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Affine {
    /// The constant term.
    pub constant: i128,
    /// `param index -> coefficient` (zero coefficients omitted).
    pub terms: BTreeMap<usize, i128>,
}

impl Affine {
    /// The constant affine form.
    pub fn constant(c: i128) -> Affine {
        Affine {
            constant: c,
            terms: BTreeMap::new(),
        }
    }

    /// The bare parameter `param_k`.
    pub fn param(k: usize) -> Affine {
        let mut terms = BTreeMap::new();
        terms.insert(k, 1);
        Affine {
            constant: 0,
            terms,
        }
    }

    fn normalized(mut self) -> Affine {
        self.terms.retain(|_, c| *c != 0);
        self
    }

    fn add(&self, o: &Affine) -> Option<Affine> {
        let mut out = self.clone();
        out.constant = out.constant.checked_add(o.constant)?;
        for (&k, &c) in &o.terms {
            let e = out.terms.entry(k).or_insert(0);
            *e = e.checked_add(c)?;
        }
        Some(out.normalized())
    }

    fn sub(&self, o: &Affine) -> Option<Affine> {
        self.add(&o.scale(-1)?)
    }

    fn scale(&self, k: i128) -> Option<Affine> {
        let mut out = Affine::constant(self.constant.checked_mul(k)?);
        for (&p, &c) in &self.terms {
            out.terms.insert(p, c.checked_mul(k)?);
        }
        Some(out.normalized())
    }

    fn as_const(&self) -> Option<i128> {
        self.terms.is_empty().then_some(self.constant)
    }
}

/// What a function returns, in parameter-relative terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RetSummary {
    /// Not characterized (the caller must havoc the result).
    Unknown,
    /// A scalar that is an affine function of the parameters.
    Scalar(Affine),
    /// A pointer derived from parameter `arg`, offset by an affine function of
    /// the parameters (provenance is that of `arg`).
    PtrFromArg {
        /// Index of the source pointer parameter.
        arg: usize,
        /// Byte offset added to that parameter's pointer.
        offset: Affine,
    },
    /// The function returns a pointer into **its own stack frame** on every returning
    /// path (a `return &local`). The frame is popped at the return, so the result is
    /// dangling in the caller. Applied at a call site as a fresh **already-freed**
    /// region, so a caller that dereferences the result is caught by the ordinary
    /// use-after-free machinery — the interprocedural counterpart of `NoDanglingDeref`
    /// (which flags the escape at the callee's own `return`).
    DanglingStack,
    /// The function returns a **fresh heap allocation** on every returning path (an
    /// allocator wrapper, `foo_alloc() { return kmalloc(sizeof(struct foo)); }`), of `size`
    /// bytes when known (else `None` = unsized). Applied at a call site as a fresh live heap
    /// region, so a caller's access through the result is checked (bounds refutable when the
    /// size is known) instead of falling to an opaque `POrigin::Call` — the dominant
    /// `opaque call result` UNKNOWN cause. Rests on `alloc-succeeds` like a direct allocation.
    Alloc {
        /// The allocation's byte size when the count is a compile-time constant; `None`
        /// leaves it unsized (a live, non-null region whose bounds stay prove-only).
        size: Option<u64>,
    },
    /// The function returns a **valid typed reference** of recovered pointee size on every
    /// returning path — a field accessor (`return sk->sk_prot;`, `return dev->driver_data;`)
    /// whose loaded result the frontend already typed as an [`Inst::RefWitness`]. Applied at a
    /// call site as a fresh valid-reference region (exactly the `RefWitness` executor arm), so
    /// accesses through the returned pointer are decided instead of falling to the opaque
    /// `POrigin::Call` (the dominant `opaque call result` UNKNOWN cause). A real `&T`/`&mut T`
    /// field is unconditional; a **raw-pointer** field (`assumed`) rests on `--assume-valid-params`
    /// — so without the opt-in the call still havocs (no false PASS), and being an `assumed`
    /// region a constant offset past the recovered size is not refuted (no false FAIL when the
    /// pointee is embedded in a larger object).
    ValidRef {
        /// Recovered pointee byte size; `None` for an unsized (`slice`/`str`) reference
        /// (a live non-null region whose bounds stay prove-only).
        size: Option<u64>,
        /// The reference's natural/declared alignment (`0` = none recorded).
        align: u32,
        /// Whether the reference is writable (`&mut`/a non-const field).
        writable: bool,
        /// Whether validity rests on `--assume-valid-params` (a raw-pointer field).
        assumed: bool,
    },
}

impl RetSummary {
    /// Whether this return characterization composes **unchanged** through a wrapper that
    /// returns a callee's result verbatim (`fn w(a) { return g(a) }`): a dangling pointer, a
    /// fresh allocation, and a typed valid reference are the *same* regardless of the wrapper's
    /// own arguments, so a wrapper inherits them directly. `PtrFromArg`/`Scalar` depend on the
    /// callee's arguments (which the wrapper maps from *its* arguments) and would need
    /// remapping, so they do not compose here (the caller soundly havocs instead).
    pub fn composes_through_wrapper(&self) -> bool {
        matches!(
            self,
            RetSummary::DanglingStack | RetSummary::Alloc { .. } | RetSummary::ValidRef { .. }
        )
    }
}

/// A function's **provenance-transfer** summary: how a call moves provenance labels
/// between its pointer arguments. Derived from the body (the lowered `ProvLabel`/
/// `ProvPropagate` a contract emits, plus callees' own transfers) to a fixpoint — so an
/// *internal wrapper* around a provenance primitive propagates provenance without a
/// hand-written contract (the general-inference goal). Only **definite** parameter
/// aliasing is recorded, so a transfer is never spurious (a false FAIL); a missed one is a
/// sound under-approximation (a false negative).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProvTransfer {
    /// `(dst_arg, src_arg)`: a call unions `src_arg`'s labels into `dst_arg`'s.
    pub transfers: Vec<(usize, usize)>,
    /// `(arg, label)`: a call adds provenance label `label` to `arg`'s region.
    pub labels: Vec<(usize, u32)>,
}

/// A function's interprocedural summary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Summary {
    /// The return-value characterization.
    pub ret: RetSummary,
    /// Whether the function may write to memory.
    pub writes: bool,
    /// Whether the function may free memory.
    pub frees: bool,
    /// The parameter index this function **definitely frees** (`kfree`-style wrapper),
    /// when that can be established with certainty — used to detect a double-free
    /// through *two* freeing-wrapper calls on the same pointer (which the coarse
    /// `frees` havoc alone cannot attribute). `None` when no single parameter is
    /// provably freed on every path. A `Some(k)` only ever *adds* a definite
    /// double-free check; it never affects liveness (so never a false PASS).
    pub frees_arg: Option<usize>,
    /// How a call moves provenance labels between its pointer arguments.
    pub prov: ProvTransfer,
    /// **Interprocedural reference-count effect**: the net change this function makes to the
    /// refcount of each pointer parameter's object, per protocol — `(param index, protocol id,
    /// delta)`. Composed through direct calls to a fixpoint, so a `get`/`put` protocol
    /// (`sock_hold`/`sock_put`, `kobject_get`/`_put`, `dev_hold`/`_put`, …) balances across
    /// *many* functions. Applied at a call so an unbalanced put (underflow → premature free /
    /// UAF) is caught cross-function. A straight-line sum (path-approximate — a `get`/`put`
    /// wrapper is unconditional), so it only ever *adds* a bug-finding check.
    pub refcount_effect: Vec<(usize, u32, i64)>,
    /// **Out-parameter stack escape**: pointer-parameter indices through which the function
    /// *unconditionally* stores the address of one of its own stack locals (`*out = &x`). The
    /// frame is popped at return, so the pointer the caller reads back from that location is
    /// dangling — a use-after-scope one call away. Only escapes in the **entry block** (which
    /// always executes) are recorded, so the store is unconditional and marking the caller's
    /// location dangling can never be a false FAIL. Applied at the call site as a dangling
    /// store into the argument's location.
    pub escapes_stack: Vec<usize>,
}

impl Summary {
    /// Whether the function is free of caller-visible memory effects.
    pub fn is_pure(&self) -> bool {
        !self.writes && !self.frees
    }
}

/// Abstract value tracked while summarizing a function body.
#[derive(Clone, PartialEq, Eq)]
pub(crate) enum AbsVal {
    PtrArg { arg: usize, off: Affine },
    Scalar(Affine),
    /// A pointer into **this frame's own stack allocation** (an `alloca` result, closed
    /// under offset/copy). Returning it escapes a pointer to a frame that is popped on
    /// return — a dangling-stack return. `join` degrades it to `Opaque` the moment a
    /// returning path yields anything else, so `DanglingStack` is claimed only when the
    /// pointer is a local on *every* returning path (a definite escape, no false FAIL).
    LocalStack,
    /// A pointer into a **fresh heap allocation** this function makes (a `kmalloc`/`malloc`
    /// wrapper), of `size` bytes when the count is a compile-time constant (else `None` =
    /// unsized). Unlike [`AbsVal::LocalStack`] the heap outlives the return, so returning it
    /// is safe — it hands the caller a live region. `join` keeps it only when *every*
    /// returning path yields a heap alloc of the same size (else `Opaque`), so it is claimed
    /// only for a genuine allocator wrapper.
    HeapAlloc { size: Option<u64> },
    /// A pointer the frontend typed as a **valid reference** via [`Inst::RefWitness`] (a loaded
    /// field pointer of recovered pointee size). Returning it hands the caller a valid typed
    /// reference; `join` keeps it only when every returning path yields the same shape (else
    /// `Opaque`), so [`RetSummary::ValidRef`] is claimed only for a genuine field accessor.
    ValidRef { size: Option<u64>, align: u32, writable: bool, assumed: bool },
    /// The **result of the observable call** at this index (in body-call order, matching
    /// `SummaryFacts`' collection). Used only to propagate a callee's `DanglingStack`
    /// return through a wrapper (`fn w() { return leak() }`): the cross-function fixpoint
    /// resolves the callee and, if it returns a dangling stack pointer, so does the wrapper.
    Call(usize),
    Opaque,
}

impl AbsVal {
    /// The join of two abstract values: equal values pass through, any
    /// disagreement is `Opaque`. This is what makes the return summary a *must*
    /// analysis — a summary is only produced when every path computes the same
    /// parameter-relative value, since a caller will trust it to rebuild the
    /// result exactly (a mere "may" summary would be unsound there).
    fn join(&self, other: &AbsVal) -> AbsVal {
        if self == other {
            self.clone()
        } else {
            AbsVal::Opaque
        }
    }
}


// --- module split (mechanical refactor) ---
mod facts;
mod module;
mod perfn;
#[cfg(test)]
#[path = "summary/tests.rs"]
mod tests;
pub use facts::*;
pub use module::*;
pub(crate) use perfn::*;
