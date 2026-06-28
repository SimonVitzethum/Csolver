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
    ValidStackFrame,
    /// An indirect branch/call target is within the analyzable set.
    ValidIndirectTarget,
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
        ]
    }
}

impl fmt::Display for SafetyProperty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.id())
    }
}
