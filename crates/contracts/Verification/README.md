# Verification — csolver-contracts

## Design
A small, declarative language for the **memory effects of library/kernel APIs**
whose body a single translation unit cannot see (allocators, deallocators,
user-copies, and — toward the Copy-Fail class — provenance/capability rules).
Each API family is one block in a separate `data/*.contract` file, so a new API is
covered by *writing a contract*, not editing the frontend. This replaces the LLVM
frontend's former hardcoded name tables (`alloc_size`/`dealloc_ptr_arg`/
`user_copy_kernel_arg`).

The default files are embedded via `include_str!` (self-contained binary);
`Contracts::load_dir` layers user-supplied files on top for private APIs. The
parser is std-only and line-based.

## File format
```text
# comments start with '#'
[name1 name2 ...]                 # one block, shared by all listed API names
alloc size=arg0 align=16          # result is a fresh region of arg0 bytes
free arg0                         # frees the pointer in arg0
write arg0 len=arg2 fill=user     # bulk-writes arg2 bytes of untrusted data to arg0
read arg1 len=arg2                # bulk-reads arg2 bytes from arg1 (in-kernel)
read arg1 len=arg2 sink=user      # ...disclosed to userspace (copy_to_user): NoInfoLeak

# provenance / capabilities (write-to-a-read-only-page class)
prov foreign grants=read          # top-level lattice: what a label grants
label arg1 foreign                # tag a region's provenance
propagate arg0 from arg1          # a container absorbs an element's labels
require arg0 write                # a region must grant a capability
require-if-alias arg1 arg2 write  # ...only if arg1 and arg2 are the SAME region (in-place)
```
A `<size>` is `arg<k>`, `arg<a>*arg<b>`, or a decimal integer (a byte count).

## Effects and their MSIR lowering (in `csolver-llvm`)
| effect | MSIR |
| --- | --- |
| `alloc` | `Inst::Alloc { Heap }`, result = the pointer |
| `free` | `Inst::Dealloc` |
| `write` / `read` | `Inst::MemIntrinsic` (a bounded op carrying the in-bounds obligation; `fill=user` taints the region so a value read back is a genuine adversarial input; `read … sink=user` → `MemKind::UserDrain`, which additionally carries `NoInfoLeak` — a never-written source disclosed to userspace) |
| `label` | `Inst::ProvLabel { ptr, label_id }` |
| `propagate` | `Inst::ProvPropagate { dst, src }` (dst's region unions in src's labels — a container inherits its elements' provenance) |
| `require` | `Inst::CapRequire { ptr, cap_id }` (implies `SafetyProperty::WriteCapability`) |
| `require-if-alias` | `Inst::CapRequireIfAlias { a, b, cap_id }` — fires only when `a`,`b` are the same region (an in-place `src==dst` op); the precise Copy-Fail signature that never false-FAILs the out-of-place copy |

Label/capability names are interned to stable ids; the lattice (`label id →
granted cap ids`) rides on `Module::prov_grants` for the executor. **Internal wrappers**
around these primitives need no contract of their own — `csolver-symbolic` derives a
`ProvTransfer` summary from the wrapper's body and applies it at call sites.

## Soundness (specification)
The language is **sound-preserving**: it can only describe effects the executor
already models faithfully, and never claims a return-value semantics beyond
"recognized". The provenance mechanism is **opt-in and sound-by-default** — an
unlabelled region grants **every** capability, so `Contracts::grants(label, cap)`
returns `true` for any label not explicitly listed. A `require` therefore fails
only when a label *explicitly* withholds the capability: the mechanism cannot
introduce a false FAIL on code that names no labels.

A malformed **built-in** file panics at first use (a build-time bug); a malformed
**user** file returns an `Err` from `load_dir`.

## Assumptions / limits
- The contract states *what* an API does to memory, not *why*; correctness of a
  contract is the author's responsibility (a wrong contract is a wrong axiom —
  the one place a human must be trusted, kept small and auditable, one block per
  API).
- Zeroing allocators (`kzalloc`/`calloc`) are deliberately absent until zero-init
  is modelled (a fresh region reads as uninitialized).
- Full CVE-2026-31431 "Copy Fail" coverage additionally needs a scatterlist/
  request model to connect the crypto `require write` to the `foreign` label; the
  current default `provenance.contract` records the real labelling source
  (`af_alg_sendpage`) and the lattice.

## Test strategy
Unit tests cover: the default files reproduce the former hardcoded tables; every
`<size>` form and the error cases (effect before a header, unknown effect); the
provenance lattice semantics (grant/withhold, unlabelled-grants-all); comments and
blank lines. The executor enforcement (`ProvLabel`/`CapRequire` → `WriteCapability`
FAIL/PASS) is tested in `csolver-symbolic`.
