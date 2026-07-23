//! Call-site contract synthesis for internal functions.
//!
//! A function with **internal linkage** is invisible outside its module, so the
//! module's direct call sites are provably *all* of its call sites (unless its
//! address is taken, which would allow an untracked indirect call). That
//! licenses deriving a contract for an otherwise-uncontracted pointer
//! parameter: the **weakest guarantee every call site provides** — the minimum
//! of the argument sizes and alignments, the intersection of the permissions.
//!
//! This is the interprocedural lever for rustc's debug IR, which omits the
//! `dereferenceable` attributes: the callee's `ptr %self` has no declared
//! contract, but every caller demonstrably passes (say) a live 32-byte alloca.
//!
//! ## Closed-world mode
//!
//! Internal linkage is one way to *prove* the call sites complete. When the
//! caller declares the module to be the whole program (`Config::closed_world`),
//! completeness is instead *assumed* for every function, so an exported function
//! is contracted from its in-module call sites too. Every other condition below
//! still holds (address-not-taken, statically-derivable arguments, ≥1 call
//! site), and the trust basis is surfaced as the distinct `closed-world-contract`
//! assumption rather than `internal-call-contract`.
//!
//! ## Soundness conditions (each enforced here)
//!
//! 1. The callee has internal linkage (`Module::internal`), *or* closed-world
//!    mode asserts the module is the whole program.
//! 2. Its address is never taken — no `Const::Symbol(name)` operand anywhere in
//!    the module (an escaped function pointer would mean unseen call sites).
//! 3. Every call site's argument is *statically* derivable: the direct result
//!    of an `Alloc` with a constant byte size (live for the whole caller frame,
//!    read+write), or the caller's own parameter carrying a declared
//!    `SizeSpec::Bytes` contract (borrowed for the call's duration). Anything
//!    else — including a synthesized contract, which would be circular — makes
//!    the parameter ineligible.
//! 4. A callee with zero call sites gets nothing (dead code stays UNKNOWN).
//!
//! Proofs resting on a synthesized contract surface the dedicated
//! `internal-call-contract` assumption, not `param-contracts` — the trust basis
//! is different (derived from call-site completeness, not declared attributes).

use csolver_absint::{analyze_intervals, Bound, IntervalAnalysis};
use csolver_ir::{
    BlockId, Callee, Condition, Const, FieldContract, FuncId, Inst, Module, Operand, PtrContract,
    PtrHint, RegId, SizeSpec, Terminator, Type,
};
use std::collections::{HashMap, HashSet};

/// Visit every operand inside a safety-check condition.
fn condition_operands(c: &Condition, op: &mut impl FnMut(&Operand)) {
    match c {
        Condition::True => {}
        Condition::Cmp { lhs, rhs, .. } => {
            op(lhs);
            op(rhs);
        }
        Condition::And(cs) | Condition::Or(cs) => {
            for c in cs {
                condition_operands(c, op);
            }
        }
        Condition::Not(c) => condition_operands(c, op),
    }
}

/// The assumption id surfaced by proofs that rest on a synthesized contract for
/// a function proven complete by **internal linkage**.
pub(crate) const INTERNAL_CALL_CONTRACT: &str = "internal-call-contract";

/// The assumption id for a synthesized contract whose call-site completeness
/// rests on the **whole-program (closed-world)** assertion rather than on
/// internal linkage — an *exported* function all of whose callers are taken to
/// be visible because the module is declared to be the whole program.
pub(crate) const CLOSED_WORLD_CONTRACT: &str = "closed-world-contract";

/// What one call site guarantees about the region behind an argument.
#[derive(Clone, Copy)]
pub(crate) struct SiteGuarantee {
    size: u64,
    align: u32,
    readable: bool,
    writable: bool,
}

/// The call-site guarantee a **DWARF/typed-use pointer hint** provides for an argument register
/// (A2): the argument is used as / declared to be a `sizeof(pointee)`-byte object, so under the
/// `--assume-valid-params` opt-in it designates a valid region of that size — the interprocedural
/// lever for the pervasive `uncontracted pointer parameter` residual, where every call site
/// passes a *typed* pointer (a field load, a heap object, a `current->…` chase) rather than a
/// constant `alloca`. Read+write like the in-function `size_hinted_pointer` region; the size is
/// the declared type only (never the `--assume-struct-tail` extent — that is a separate opt-in).
/// Honoured only when `--assume-valid-params` is on, so without the flag the synthesis is
/// unchanged; the resulting contract is prove-only (never a false FAIL) and rests on the same
/// assumption `size_hinted_pointer` already surfaces.
fn hint_guarantee(hint: &PtrHint) -> SiteGuarantee {
    SiteGuarantee {
        // `region_align` is a small power of two (declared alignment or a size-derived default),
        // so it always fits a `u32`.
        size: hint.size,
        align: hint.region_align() as u32,
        readable: true,
        writable: true,
    }
}


// --- module split (mechanical refactor) ---
mod facts;
mod fields;
mod fieldsyn;
mod ptr;
mod scalars;
mod site;
#[cfg(test)]
#[path = "contracts/tests.rs"]
mod tests;
#[cfg(test)]
#[path = "contracts/tests2.rs"]
mod tests2;
#[cfg(test)]
#[path = "contracts/tests3.rs"]
mod tests3;
pub(crate) use facts::*;
pub(crate) use fields::*;
pub(crate) use fieldsyn::*;
pub(crate) use ptr::*;
pub(crate) use scalars::*;
pub use site::address_taken_names;
use site::*;
