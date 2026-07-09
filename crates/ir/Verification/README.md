# Verification — csolver-ir (MSIR)

## Design
MSIR is a typed, block-argument SSA CFG with **explicit** memory operations
(`Load`/`Store`/`Alloc`/`Dealloc`/`PtrOffset`) and first-class
`SafetyCheck` instructions. All frontends lower into it; all analyses read it.
Provenance is carried by `ProvLabel` (tag a region's origin), `ProvPropagate`
(a container absorbs an element's labels), `CapRequire` (demand a capability), and
`CapRequireIfAlias` (demand it only for an in-place `src==dst` op), whose interned
lattice rides on `Module::prov_grants` — the basis for `WriteCapability` (the
Copy-Fail write-to-a-read-only-page class). `MemKind::UserDrain` marks a
`copy_to_user`-style read disclosed to userspace (implies `NoInfoLeak`);
`Module::global_fn_ptrs` (global name → `[(byte offset, FuncId)]`) is the
devirtualization table for indirect calls loaded from constant ops-struct/vtable
globals. `merge_modules(Vec<Module>, name)` links translation units by **moving**
their functions/side tables (no per-function clone).

## Specification
- Block-argument SSA: a value's single definition dominates its uses; PHIs are
  modelled as block parameters bound by branch arguments.
- `Type::size_bytes`/`align_bytes` implement C-style layout with tail padding
  under a `DataLayout`; they return `None` (never a wrong number) when a size is
  not statically determinable.
- Each memory op implies a canonical set of `SafetyProperty` obligations
  (documented on each `Inst` variant).

## Assumptions
- The `DataLayout` matches the target the artifact was built for (LP64 default).
- Frontends preserve the **refinement property**: every concrete behaviour of
  the source is a concrete behaviour of the emitted MSIR.

## Limits
- Floating-point/SIMD are `Type::Opaque` (size/align only) — sound for memory
  safety since they are never pointers, but value-imprecise.
- No vararg / unwinding modelling yet (frontends emit assumptions).

## Proofs (arguments)
- **Layout soundness.** `align_up` rounds to powers of two with checked
  arithmetic; struct size ≥ Σ field sizes and is a multiple of struct align.
  Tested for `{i8,i32}` and `{i8,ptr}`.
- **CFG faithfulness.** `Terminator::successors` enumerates exactly the
  reachable targets; consumed by `csolver-cfg`.

## Test strategy
Unit tests for layout, terminator successors, defined-register extraction, and
constant distinctness. Frontend refinement is argued per-frontend (mir/llvm/asm).
