//! The catalogue of memory-safety properties CSolver proves.
//!
//! Each [`SafetyProperty`] corresponds to one class of memory error from the
//! project goal. A [`crate::ProofObligation`] always carries exactly one of
//! these so that reports can be grouped, counted, and explained per property.

use std::fmt;

/// A class of memory-safety property to be proven at a program location.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SafetyProperty {
    /// Every indexed/offset access stays within its allocation bounds.
    InBounds,
    /// No access occurs to a freed allocation (temporal safety: read/write).
    NoUseAfterFree,
    /// No allocation is deallocated more than once.
    NoDoubleFree,
    /// No dereference of a pointer whose referent has ended its lifetime.
    NoDanglingDeref,
    /// No dereference of the null pointer.
    NoNullDeref,
    /// The stack is not corrupted (saved registers, return address, canaries).
    ///
    /// **Subsumed — no dedicated emission by design.** The concrete corruption paths are
    /// already covered elsewhere: a buffer overflow that reaches a saved register / return
    /// address is an out-of-bounds store ([`SafetyProperty::InBounds`]), and calling into
    /// overwritten data is [`SafetyProperty::ValidIndirectTarget`] (an indirect call into a
    /// stack/heap region). A *dedicated* refutation would need an explicit return-address /
    /// canary model in the binary frame (the prologue is modelled as one frame region with no
    /// distinguished RA slot), which is deep and adds nothing over the InBounds coverage — so
    /// this variant is deliberately never recorded, retained only as a taxonomy label.
    StackIntegrity,
    /// Pointer arithmetic stays within (or one-past-end of) the same object.
    ValidPointerArith,
    /// A reference (`&T`/`&mut T`) points to a valid, correctly-typed value.
    ValidReference,
    /// A write targets writable, in-bounds, correctly-typed memory.
    ValidWrite,
    /// A read targets readable, initialized, in-bounds memory.
    ValidRead,
    /// Two regions that must not alias/overlap indeed do not.
    NoForbiddenOverlap,
    /// An access satisfies its type's alignment requirement.
    Alignment,
    /// A function's stack frame is set up and torn down correctly.
    ///
    /// **Subsumed — no dedicated emission by design** (see [`SafetyProperty::StackIntegrity`]).
    /// A malformed frame manifests as an out-of-bounds stack access ([`SafetyProperty::InBounds`])
    /// or a dangling stack pointer ([`SafetyProperty::NoDanglingDeref`]); a separate well-formedness
    /// property would duplicate those without a return-address model. Retained as a taxonomy label.
    ValidStackFrame,
    /// An indirect branch/call target is within the analyzable set.
    ValidIndirectTarget,
    /// A write (or other operation) targets a region whose **provenance** grants the
    /// required capability — e.g. not a write through a pointer to a foreign/read-only
    /// page (the Copy-Fail class). Driven by external contract labels; see
    /// `csolver_contracts`.
    WriteCapability,
    /// No **uninitialized memory is disclosed to userspace**: a `copy_to_user`-style
    /// drain must not read source bytes that were never written (a freshly-allocated
    /// kernel buffer copied out before being filled — the classic kernel info-leak).
    NoInfoLeak,
    /// An **allocation size computation does not overflow**: an `n * sizeof(T)` /
    /// `kmalloc_array(n, C)` product with an attacker-controlled count and a constant
    /// element size must not wrap the pointer width to a small value (which
    /// under-allocates, leading to a heap overflow). A bug-finding-only obligation.
    NoSizeOverflow,
    /// No **concurrency-safety violation**. Currently the soundly single-function-decidable
    /// subclass: an AA self-deadlock — acquiring a lock (`spin_lock`/`mutex_lock`/…) that
    /// is already held on the same path, which deadlocks. A bug-finding-only obligation.
    /// (Inter-thread data races proper need a concurrency model and are future work.)
    DataRace,
    /// No **double-fetch** of user memory: a syscall must not read the same user-space
    /// address twice (two `copy_from_user`/`get_user` from a provably-aliasing user
    /// source on one path). User memory is adversary-controlled, so a value validated on
    /// the first read can differ on the second — a time-of-check-to-time-of-use race whose
    /// second timeline is implicit (the user mutates concurrently). A bug-finding-only
    /// obligation, refuted only for a **must-aliasing** re-fetch (no false FAIL on a
    /// re-fetch of a different address).
    DoubleFetch,
    /// No **tainted value reaches an unsafe sink**: a value derived from an untrusted
    /// **source** (`copy_from_user`/`recv`/argv, a `taint-source` contract) must not flow —
    /// through arithmetic, loads and calls — into a **sink** that a `taint-sink` contract
    /// marks as requiring untrusted-free input (a `printf` format string, a `memcpy`/loop
    /// length, an `exec` argument). A recognised **sanitiser** (`taint-sanitize`) clears the
    /// taint. A directional generalisation of the provenance labels; the one mechanism covers
    /// injection (J), tainted-length→OOB (F), and information-flow (D). A bug-finding-only
    /// obligation, refuted only when the value is **definitely tainted** on the path reaching
    /// the sink (taint meet-joined at merges — no false FAIL under a partly-tainted phi).
    TaintedSink,
    /// No **typestate/protocol violation**: a named resource (a file/fd/lock/handle, keyed by
    /// its pointer base or scalar identity) is used in a state its protocol forbids — a
    /// use-after-close/double-close (a `close`d handle read again), a missing-check (a
    /// privileged op on a resource never `checked`), or any contract-defined finite-state
    /// protocol. A **generalisation** of the lifetime/lock/taint typestates: a per-path map
    /// `resource → state`, advanced by `typestate-set` transitions and checked by
    /// `typestate-require[-not]` obligations, all contract-driven. A bug-finding-only
    /// obligation, refuted only when the resource is **definitely** in the forbidden state on
    /// the path (state meet-joined at merges — no false FAIL under a partial state).
    TypestateViolation,
    /// No **secret-dependent control flow or memory index** (constant-time / side-channel, L):
    /// a value carrying a `secret` taint label must not decide a **branch** (a timing side
    /// channel — the taken path is observable) or index memory (a cache side channel). Rides
    /// the taint lattice: `secret` sources (`taint-source … secret`) flow to a branch
    /// condition or a `gep` index. A bug-finding-only obligation, refuted only when the
    /// deciding value is definitely secret-tainted on the path.
    SecretDependent,
    /// No **division (or modulo) by zero**: the divisor of a `/`/`%` (`UDiv`/`SDiv`/`URem`/`SRem`)
    /// must be provably non-zero. A zero divisor is undefined behaviour (a hardware trap on most
    /// targets). Refuted with a witness when the divisor can be zero on the path (bug-finding: a
    /// genuine-input divisor with no non-zero guard; strict: only on an exact path).
    NoDivByZero,
    /// No **shift past the bit width**: the shift amount of a `<<`/`>>` (`Shl`/`LShr`/`AShr`)
    /// must be less than the operand's bit width. Shifting by ≥ the width is undefined behaviour in
    /// C/LLVM (a poison value). Refuted with a witness when the shift amount can reach the width.
    NoShiftOverflow,
    /// No **signed/unsigned arithmetic overflow**: an `add`/`sub`/`mul` the frontend has
    /// marked `nsw`/`nuw` must not wrap. In C signed overflow (and any LLVM `nsw`/`nuw`
    /// operation) is undefined behaviour. Only raised when the producer declared the
    /// no-wrap flag — plain wrapping arithmetic carries no obligation. Refuted with a
    /// witness when the operands can drive the result past the type's range on the path
    /// (bug-finding: genuine input with no bounding guard).
    NoArithOverflow,
    /// No **blocking/sleeping call in atomic context**: a call that may sleep
    /// (`mutex_lock`/`kmalloc(GFP_KERNEL)`/`schedule`/`msleep`/`down`/…) must not run while a
    /// **spinlock is held** (or IRQs/preemption are disabled) — it deadlocks or corrupts the
    /// scheduler. A per-path structural typestate (spinlock held vs. sleepable context); a
    /// bug-finding-only obligation. Refuted only when a spinlock is *definitely* held on
    /// every path reaching the sleeping call (no false FAIL under a partial hold).
    SleepInAtomic,
    /// No **Rust aliasing (borrow-stack) violation**: the Stacked/Tree-Borrows discipline
    /// the Rust reference model requires. Currently the soundly-decidable, unambiguous
    /// subclass — a **write through a shared reference** (`&T`): a store whose pointer is
    /// derived (through casts / field / index projections) from a genuine `&T` borrow, which
    /// is always undefined behaviour (a `&T` grants read-only access; interior mutability
    /// writes go through a raw pointer from `UnsafeCell::get`, so they carry no shared tag).
    /// Opt-in behind `--aliasing-model` (the reference model is only partially reconstructed
    /// from the current frontends). Refuted only on a feasible path (no false FAIL). The full
    /// borrow-stack — use-after-invalidation of `&mut`, two-live-`&mut` siblings, protectors —
    /// needs frontend retag events and derivation-tree tracking; recorded as future work.
    NoAliasingViolation,
}

impl SafetyProperty {
    /// A stable, machine-friendly identifier (used in JSON reports and caches).
    pub fn id(self) -> &'static str {
        match self {
            SafetyProperty::InBounds => "in_bounds",
            SafetyProperty::NoUseAfterFree => "no_use_after_free",
            SafetyProperty::NoDoubleFree => "no_double_free",
            SafetyProperty::NoDanglingDeref => "no_dangling_deref",
            SafetyProperty::NoNullDeref => "no_null_deref",
            SafetyProperty::StackIntegrity => "stack_integrity",
            SafetyProperty::ValidPointerArith => "valid_pointer_arith",
            SafetyProperty::ValidReference => "valid_reference",
            SafetyProperty::ValidWrite => "valid_write",
            SafetyProperty::ValidRead => "valid_read",
            SafetyProperty::NoForbiddenOverlap => "no_forbidden_overlap",
            SafetyProperty::Alignment => "alignment",
            SafetyProperty::ValidStackFrame => "valid_stack_frame",
            SafetyProperty::ValidIndirectTarget => "valid_indirect_target",
            SafetyProperty::WriteCapability => "write_capability",
            SafetyProperty::NoInfoLeak => "no_info_leak",
            SafetyProperty::NoSizeOverflow => "no_size_overflow",
            SafetyProperty::DataRace => "data_race",
            SafetyProperty::DoubleFetch => "double_fetch",
            SafetyProperty::SleepInAtomic => "sleep_in_atomic",
            SafetyProperty::TaintedSink => "tainted_sink",
            SafetyProperty::TypestateViolation => "typestate_violation",
            SafetyProperty::SecretDependent => "secret_dependent",
            SafetyProperty::NoDivByZero => "no_div_by_zero",
            SafetyProperty::NoShiftOverflow => "no_shift_overflow",
            SafetyProperty::NoArithOverflow => "no_arith_overflow",
            SafetyProperty::NoAliasingViolation => "no_aliasing_violation",
        }
    }

    /// A one-line human description.
    pub fn describe(self) -> &'static str {
        match self {
            SafetyProperty::InBounds => "access is within allocation bounds",
            SafetyProperty::NoUseAfterFree => "no access to freed memory",
            SafetyProperty::NoDoubleFree => "no double free",
            SafetyProperty::NoDanglingDeref => "no dereference of a dangling pointer",
            SafetyProperty::NoNullDeref => "no null-pointer dereference",
            SafetyProperty::StackIntegrity => "stack is not corrupted",
            SafetyProperty::ValidPointerArith => "pointer arithmetic stays in-object",
            SafetyProperty::ValidReference => "reference points to a valid value",
            SafetyProperty::ValidWrite => "write targets valid writable memory",
            SafetyProperty::ValidRead => "read targets valid initialized memory",
            SafetyProperty::NoForbiddenOverlap => "disjoint regions do not overlap",
            SafetyProperty::Alignment => "access satisfies alignment requirement",
            SafetyProperty::ValidStackFrame => "stack frame is well-formed",
            SafetyProperty::ValidIndirectTarget => "indirect branch target is valid",
            SafetyProperty::WriteCapability => "access target's provenance grants the capability",
            SafetyProperty::NoInfoLeak => "no uninitialized memory is disclosed to userspace",
            SafetyProperty::NoSizeOverflow => "allocation size computation does not overflow",
            SafetyProperty::DataRace => "no concurrency-safety violation (AA self-deadlock)",
            SafetyProperty::DoubleFetch => "no double-fetch of user memory",
            SafetyProperty::SleepInAtomic => "no sleeping call in atomic (spinlock-held) context",
            SafetyProperty::TaintedSink => "no tainted value reaches an unsafe sink",
            SafetyProperty::TypestateViolation => "no resource is used in a forbidden protocol state",
            SafetyProperty::SecretDependent => "no secret-dependent branch or memory index",
            SafetyProperty::NoDivByZero => "divisor of a division/modulo is non-zero",
            SafetyProperty::NoShiftOverflow => "shift amount is less than the bit width",
            SafetyProperty::NoArithOverflow => "nsw/nuw arithmetic does not overflow",
            SafetyProperty::NoAliasingViolation => "no write through a shared (&T) reference",
        }
    }

    /// All properties, in catalogue order. Useful for reports and tests.
    pub fn all() -> &'static [SafetyProperty] {
        use SafetyProperty::*;
        &[
            InBounds,
            NoUseAfterFree,
            NoDoubleFree,
            NoDanglingDeref,
            NoNullDeref,
            StackIntegrity,
            ValidPointerArith,
            ValidReference,
            ValidWrite,
            ValidRead,
            NoForbiddenOverlap,
            Alignment,
            ValidStackFrame,
            ValidIndirectTarget,
            WriteCapability,
            NoInfoLeak,
            NoSizeOverflow,
            DataRace,
            DoubleFetch,
            SleepInAtomic,
            TaintedSink,
            TypestateViolation,
            SecretDependent,
            NoDivByZero,
            NoShiftOverflow,
            NoArithOverflow,
            NoAliasingViolation,
        ]
    }
}

impl fmt::Display for SafetyProperty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.id())
    }
}
