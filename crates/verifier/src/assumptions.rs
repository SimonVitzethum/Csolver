use super::*;

/// Expand a known assumption id into its full record for the report.
pub(crate) fn assumption_record(id: String) -> Assumption {
    match id.as_str() {
        "caller-range-precondition" => Assumption {
            id,
            statement: "a non-entry function's integer parameter stays within the range \
                        that every visible call site passes it"
                .into(),
            justification: "the callee's call sites are provably complete (internal linkage, \
                            or the whole-program assertion), so the union of the argument \
                            ranges over all sites bounds the parameter; the callee is not an \
                            attacker-reachable entry, so no unseen caller can escape the range"
                .into(),
        },
        LINEAR_ASSUMPTION => Assumption {
            id,
            statement: "the integer/offset/size quantities reasoned about are \
                        non-negative and fit in isize::MAX, so they do not wrap and \
                        their signed and unsigned comparisons coincide"
                .into(),
            justification: "the internal linear decision procedure models bit-vectors \
                            as mathematical integers; Rust caps any allocation at \
                            isize::MAX bytes, so offsets, sizes and valid indices lie \
                            in [0, isize::MAX] where this holds. Programs using the \
                            full unsigned range with the sign bit set need the \
                            bit-precise SMT backend (later milestone)"
                .into(),
        },
        "alloc-succeeds" => Assumption {
            id,
            statement: "allocation requests succeed: they return a valid, non-null, \
                        suitably-sized and -aligned block (out-of-memory is not modelled)"
                .into(),
            justification: "the symbolic memory model treats an allocation as producing \
                            a live region; programs that must handle allocation failure \
                            need that null-check modelled separately"
                .into(),
        },
        "param-contracts" => Assumption {
            id,
            statement: "pointer parameters satisfy their declared contracts: a \
                        `dereferenceable(N)`/`align`/`readonly`/`writeonly` pointer \
                        points to N valid bytes with that alignment and access mode"
                .into(),
            justification: "these come from the parameters' Rust reference types \
                            (`&[T]`, `&mut [T; N]`, …), which the compiler guarantees and \
                            emits as LLVM parameter attributes; the proof is relative to \
                            the caller upholding the reference's validity"
                .into(),
        },
        "param-valid" => Assumption {
            id,
            statement: "a raw pointer parameter points to a valid, live, correctly-sized \
                        instance of its (debug-info) pointee type"
                .into(),
            justification: "the opt-in `--assume-valid-params`: a framework/kernel entry \
                            point is passed a valid pointer by its caller (the framework), \
                            which C's type system cannot state; unsound for an arbitrary raw \
                            pointer, so the proof is explicitly relative to this assumption"
                .into(),
        },
        contracts::INTERNAL_CALL_CONTRACT => Assumption {
            id,
            statement: "an internal function's pointer parameter satisfies the weakest \
                        contract its call sites guarantee (minimum size and alignment, \
                        intersected permissions)"
                .into(),
            justification: "the function has internal linkage and its address is never \
                            taken, so the module's direct call sites are provably all of \
                            its call sites; every one passes a live region with at least \
                            the synthesized size (a constant-size stack allocation or a \
                            parameter with a declared contract, borrowed for the call)"
                .into(),
        },
        contracts::CLOSED_WORLD_CONTRACT => Assumption {
            id,
            statement: "in whole-program (closed-world) mode, an exported function's \
                        pointer parameter satisfies the weakest contract its call sites \
                        guarantee (minimum size and alignment, intersected permissions)"
                .into(),
            justification: "the run was told the module is the whole program \
                            (`--closed-world`), so the module's direct call sites are \
                            taken to be all of the function's call sites — the same \
                            derivation as internal linkage, resting on the whole-program \
                            assertion instead of on linkage; every seen call passes a \
                            live region of at least the synthesized size"
                .into(),
        },
        "closed-world-devirt" => Assumption {
            id,
            statement: "an indirect call through a heap/parameter-rooted function pointer \
                        (`obj->ops->fn()`) resolves to the single function the whole-program \
                        points-to analysis proves it designates; that callee's effects are \
                        used in place of an opaque call"
                .into(),
            justification: "the run was told the module is the whole program (`--closed-world`), \
                            so the field-sensitive points-to sees every store to the dispatch \
                            field and resolves it only when a *single* function is possible — an \
                            over-approximation of size one, hence exact; any ambiguous or \
                            unknown-written field stays unresolved (opaque). Call-target \
                            resolution only: the loaded pointer keeps its provenance, so its \
                            null/uninitialised/bounds checks are unchanged and nothing is masked"
                .into(),
        },
        "precondition" => Assumption {
            id,
            statement: "a caller-declared parameter precondition holds: the pointer is a \
                        valid, non-null region of the declared size (readable, and writable \
                        if so declared)"
                .into(),
            justification: "supplied by the user as an opt-in precondition annotation (a \
                            sidecar `--pre` file), the way a `_Nonnull` / `access` attribute \
                            documents an API contract; the callee may assume it, and every \
                            caller is obliged to establish it — so it proves but never refutes"
                .into(),
        },
        "debuginfo" => Assumption {
            id,
            statement: "a reference parameter points to a live object of its                         debug-info pointee type's size (readable, and writable for                         `&mut`/non-const)"
                .into(),
            justification: "recovered from the module's DWARF debug metadata (`!DI…`),                             which records the pointee type the opaque `ptr` erased. A                             contract is synthesized only for pointer kinds the source                             language guarantees valid — a Rust `&T`/`&mut T` or a C++                             `T&` — never a raw pointer, so it grants exactly what the                             type system already does"
                .into(),
        },
        "valid-reference" => Assumption {
            id,
            statement: "a `&T`/`&mut T` value points to a live, correctly-sized                         and -aligned `T`, readable (and writable for `&mut`)"
                .into(),
            justification: "Rust's reference invariant: a reference of type `&T` is                             always valid for its pointee, even when obtained where the                             analysis cannot see its origin (a call result, a by-value                             aggregate field). The region is modelled fresh, so it never                             aliases — the assumption only ever loses precision"
                .into(),
        },
        "global-memory" => Assumption {
            id,
            statement: "a global/static symbol points to a region of its declared                         size and alignment that lives for the whole program (writable                         unless declared `constant`) and is initialized"
                .into(),
            justification: "the size, alignment and mutability come from the module's                             own `@name = global/constant <type>` definition, the same                             trust level as the function bodies being verified"
                .into(),
        },
        "slice-abi" => Assumption {
            id,
            statement: "a `(ptr, usize len)` parameter pair is a Rust slice `&[T]`: \
                        the pointer is valid for `len * size_of::<T>()` bytes"
                .into(),
            justification: "the front-end paired an aligned pointer parameter with the \
                            following length parameter per the Rust slice ABI and took the \
                            element size from a use; this is a heuristic, made explicit so \
                            the proof's trust boundary is visible"
                .into(),
        },
        _ => Assumption {
            statement: id.clone(),
            id,
            justification: String::new(),
        },
    }
}
