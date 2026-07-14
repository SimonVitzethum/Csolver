# CSolver

A **formal memory-safety verifier** for Rust (including `unsafe`), C, and C++,
operating on Rust MIR, LLVM-IR, x86-64 / AArch64 assembly, and compiled binaries
(ELF, PE/COFF, Mach-O — plus ISO 9660 and WIM images, unpacked to the object files
inside).

CSolver has two modes:

- **Verification (default).** It *proves* the absence of memory errors. When a
  full proof is impossible (theory limits or missing information), it explains
  precisely why, lists the minimal extra assumptions or annotations that would
  close the proof, or produces a concrete counterexample. A false `PASS` and a
  false `FAIL` are both treated as bugs.
- **Bug-finding (`--bugs`).** A recall-oriented mode for finding real memory bugs
  in kernel-style C — out-of-bounds, use-after-free, double-free,
  `copy_from_user` overflows, **uninitialized-memory disclosure to userspace**
  (`copy_to_user` of never-written bytes), **allocation-size overflow**
  (`n * sizeof(T)` wrapping to an under-allocation), and **AA self-deadlock**
  (re-acquiring a held lock) — each reported with a concrete triggering input.
  Indirect calls through constant ops-struct / vtable globals are
  **devirtualized** so dispatch is analysed with the callee's summary instead of
  an opaque havoc.

## Status

The common IR (MSIR) and the full pipeline — symbolic execution, memory model,
loops, alias-aware heap, interprocedural summaries, and the internal bit-precise
solver — are implemented and audited for soundness. The **Rust (MIR)** and
**LLVM/C** frontends are mature: the LLVM path handles optimized IR, DWARF field
recovery, C/kernel allocators, `copy_from_user`, and inline assembly, and runs on
real Linux-kernel IR. **C++** goes through the same LLVM path.

The internal SAT core is a full **CDCL** solver (1-UIP clause learning,
non-chronological backjumping, VSIDS, Luby restarts, two-watched literals, LBD
clause deletion) — pure Rust, `unsafe`-free, no external solver. Only `Unsat` is
ever trusted; every soundness-neutral heuristic is guarded by a randomized
brute-force oracle cross-check.

**Whole-program analysis scales without linking.** Cross-module verification
(a caller's validation flowing into a callee) is available two ways: by *linking*
a directory/reachable set into one module (`--cross-file` / `--reachable`), or —
the memory-bounded path — by **streaming**: each `.ll` is lowered, its
interprocedural facts (effect summaries, pointer/scalar preconditions,
member-provenance) folded into compact per-function facts, and the IR dropped.
The four fact passes are each proven *bit-identical* to running them on the fully
linked module, so the whole kernel is analysed in a few GB instead of the tens of
GB the link-everything path needs. See `solver facts` below.

Recognized library/kernel APIs are described by **external, file-driven contracts**
(`crates/contracts/data/*.contract`) — one block per API family, so a new API is
covered by writing a contract, not editing the frontend. The contract language also
carries **provenance labels and a capability lattice**, the general basis for the
write-to-a-read-only-page class (e.g. CVE-2026-31431 "Copy Fail"); enforcement is
sound-by-default (an unlabelled region grants every capability, so it never
false-FAILs).

> **Note.** Today, each recognized leaf API (an allocator, a user-copy, a crypto
> primitive) still needs a hand-written contract entry. This is expected to shrink as
> the project matures: a general effect-summary inference already derives the behaviour
> of *internal wrappers* automatically (no contract per wrapper), and that inference will
> grow to cover more, leaving only a small, auditable set of irreducible interface axioms
> at the true trust boundaries.

Every verdict is checked against a **dynamic oracle**: Rust against **Miri**, C
against **AddressSanitizer + UBSan** (see [differential/](differential/)). The
`--bugs` mode finds all 8 memory-bug classes in the C differential corpus with
**zero false positives**.

**Binary & container frontends.** `csolver-elf` is a pure-Rust, zero-dependency
loader for **ELF** (incl. ELF32 / big-endian), **PE/COFF** (Windows), and **Mach-O**
(macOS) behind one `load_object`, plus DWARF `.debug_info`/`.debug_line`; the x86-64
decoder uses **recursive descent** (only reachable bytes) and bridges any unmodeled
instruction to an opaque havoc, so a stripped or padded binary is analysed rather than
dropped. Container images are unpacked to the object files inside them: **ISO 9660**
(Joliet + Rock Ridge names + El Torito boot images) and **WIM** (`install.wim`;
XPRESS-Huffman decompression, LZX/LZMS reported as not-decoded). See
[docs/STATUS.md](docs/STATUS.md), [docs/ROADMAP.md](docs/ROADMAP.md), and
[ARCHITECTURE.md](ARCHITECTURE.md).

## Properties targeted

No out-of-bounds access · no use-after-free · no double-free · no dangling
deref (incl. dangling-stack return & `llvm.lifetime` use-after-scope) · no null
deref · valid pointer arithmetic · valid references · valid reads/writes · no
forbidden region overlap · alignment · valid indirect branch targets ·
write-capability (provenance: no write through a pointer to a read-only/foreign
region) · no info-leak (no `copy_to_user` of uninitialized memory) · integer UB:
no division/modulo by zero, no shift past the bit width, no `nsw`/`nuw`
add/sub/mul overflow (signed mul included).

Opt-in behind `--aliasing-model`: **no Rust aliasing (borrow-stack) violation** —
currently the unambiguous *write through a shared `&T`* class.

Bug-finding mode (`--bugs`) adds recall-oriented obligations: **no allocation-size
overflow** (`n * sizeof(T)` wrap), **no data race** (AA self-deadlock, Eraser
lockset, ABBA lock-order, atomicity/weak-memory), **no double-fetch** of user
memory, **no tainted value into an unsafe sink**, **no typestate/protocol
violation**, **no secret-dependent branch/index**, and **no sleep in atomic
context**. These are enumerated only under `--bugs`, so sound `verify` verdicts are
unchanged.

## Soundness contract

A `PASS` means *proven safe under the explicitly reported assumptions*. We
never emit `PASS` without a proof; otherwise we emit `UNKNOWN` (with the
residual obligations) or `FAIL` (with a counterexample). Full memory safety of
arbitrary machine code is undecidable; CSolver maximizes what it can prove and
is honest about the rest.

The discharge pipeline is audited for false-PASS bugs ([docs/AUDIT.md](docs/AUDIT.md));
the path to full Rust/assembly/binary coverage is in [docs/ROADMAP.md](docs/ROADMAP.md).

### Sound by default; recall behind explicit flags

Everything **on by default is sound**: it may answer `UNKNOWN`, but never a false
`PASS`. Several UNKNOWN causes can only be closed by *assuming* something the code
does not prove — a kernel/framework invariant. Those live behind **opt-in flags**,
are **unsound in general**, and every proof that uses one names the assumption it
rests on in its proof tree, so a `PASS` is never silently bought.

| Flag | Assumes | Unsound if | Surfaced as |
|---|---|---|---|
| `--assume-valid-params` | a raw pointer **parameter** of known (DWARF) pointee size is valid | the caller passes a dangling/null pointer | `param-valid` |
| `--assume-valid-returns` | a pointer returned by an **unsummarised call** (external/unanalysed callee) is valid + non-null | the callee returns `NULL`, an `ERR_PTR` error code, or a dangling pointer | `valid-returns` |
| `--assume-valid-loop-ptrs` | a **loop-carried pointer** (a moving iterator, `iter = iter->next`) still designates a valid live object each iteration — the kernel's intrusive-container discipline | the cursor walks off its object, or a list node is already freed (UAF through the iterator) | `valid-loop-ptrs` |
| `--assume-param-buffer-len` | a C `(buf, len)` **parameter pair** — the body indexes `buf` by something `len` bounds, or by a value *derived* from `len` (`buf[len - 4]`) — really is a buffer and its length | the caller passes a length longer than the buffer (C guarantees no such pairing; Rust's `&[T]` does, and rests on `slice-abi` instead) | `param-buffer-len` |
| `--bugs` | refute on over-approximated paths when the witness is a genuine input | a branch on an over-approximated value is actually infeasible (small false-FAIL risk) | bug-finding mode |
| `--aliasing-model` | Rust borrow-stack (Stacked/Tree Borrows) reconstruction | the reference model is only partially recovered from the frontend | opt-in |
| `--closed-world` | the module's call sites are *all* call sites | a library with unseen callers | opt-in |

`--assume-valid-returns` proves `no_null_deref` and `no_use_after_free` through a call
result; its **bounds stay `UNKNOWN`**, because no size for an external callee's return
is known anywhere in the translation unit.

`--assume-valid-loop-ptrs` covers the moving iterator *fully*, bounds included: the
size of the object it designates is recovered from the type — either the `getelementptr`
that indexes it (`gep %struct.node, ptr %it` ⇒ a `struct node`), or, where clang has
canonicalised that into a byte `gep i8`, from the `#dbg_value` → `!DILocalVariable`
declared type. A `list_for_each`-style traversal then verifies `PASS` outright.

Neither is a `scan` default — assuming those pointers valid would hide exactly the
null/UAF bugs a bug-finding scan exists to find.

### Decided rate: where the UNKNOWNs come from

A function is `PASS`/`FAIL` only when *every* one of its obligations is decided, so it is
gated by its worst one. On a 50-file kernel sample (`--bugs --assume-valid-params
--closed-world --assume-valid-loop-ptrs`) the decided rate is now **45 %** of functions
(748 `PASS` / 14 `FAIL` / 912 `UNKNOWN` of 1674), up from 16 %. The dominant causes, and
what is done about each, are tracked in
[docs/decided-rate-roadmap.md](docs/decided-rate-roadmap.md):

- **safe returns left `no_dangling_deref` undecided** — *closed (sound, default)*: the
  verifier enumerates a `NoDanglingDeref` obligation at every `return`, but the executor
  only recorded a decision when the returned pointer *did* dangle. A **safe** return
  therefore produced no decision at all, so the obligation fell to `UNKNOWN` and gated the
  whole function. `check_return` now records on every return: a scalar cannot dangle, and a
  pointer that provably does not point into this frame's stack is a *proof*, not a silence.
  This one fix moved 500 kernel functions from `UNKNOWN` to `PASS` (248 → 748) with **no**
  new `FAIL`s and both differential oracles still `SOUND`.

- **opaque call result** — *closed*: an allocator wrapper returns a sized live heap region
  (`RetSummary::Alloc`, sound, default); and under `--assume-valid-params` a call result the
  caller then indexes as `gep %struct.T` gets a sized region of that type. Whole-program
  summaries (`--whole-program`) resolve cross-file callees. This residual class goes to **zero**
  on a kernel sample.
- **null / opaque provenance** — *closed*: a `if (p != null)` guard now carries to the
  dereference (stable opaque-pointer address symbols), sound and on by default.
- **loop-havocked pointer** — *closed behind a flag*: `--assume-valid-loop-ptrs` proves
  liveness, non-null **and bounds** through a moving iterator (the object size comes from
  the indexing gep's type, or the `#dbg_value` local's declared type). On a kernel sample
  it drives this residual class to **zero**; a `list_for_each` traversal verifies `PASS`.
  By default the class stays `UNKNOWN` — soundly, a moving list pointer has no proven object.
- **int-to-pointer cast** — *closed under `--assume-valid-params` when the result is typed
  by its use*: an `inttoptr` (kernel `current` read from the per-cpu base) or a
  `container_of` backward-offset pointer that a `getelementptr %struct.T` indexes designates
  a `struct T` of known size, so it gets a sized region. Drives this residual class down
  ~80% on a kernel sample. A *type-less* int-to-pointer stays `UNKNOWN` — treating an
  arbitrary integer as a valid pointer would be a false `PASS`.
- **loaded value**, **uncontracted parameter** — largely closed by DWARF field/typed-gep
  provenance recovery and `--assume-valid-params`. A typed `getelementptr %struct.T` now also
  bridges to the DWARF struct *by name*, so field pointees load through **any** typed base
  (a field load / call result / global, not only a parameter) — cutting the kernel in-bounds
  and alignment residuals ~65%.

## Build & test

```sh
cargo build            # std-only, builds offline
cargo test             # unit + integration tests across the workspace
cargo run -p csolver-cli -- --help
```

## CLI

```sh
solver verify <path>              # .rs (turnkey), .mir, .ll, .s, or a binary/container:
                                  #   ELF/PE/Mach-O object, .iso (ISO 9660), .wim (WIM)
solver verify <module.ll> --closed-world   # whole-program: synthesize contracts
solver verify <module.ll> --bugs           # bug-finding mode (find, don't prove)
solver verify <module.ll> --aliasing-model # opt-in Rust borrow-stack (write-through-&T)
solver verify <module.ll> --assume-valid-params  # trust raw-pointer params of known size
solver verify <module.ll> --pre <file>     # caller preconditions (bytes/elements/cstring)
solver verify <path> --json                # machine-readable report
solver scan <dir> [--bugs] [--assume-valid-params]   # sweep EVERY .ll under a tree:
                                            # list every violation + report coverage
                                            # (PASS/FAIL/UNKNOWN %, decided, dropped)
solver scan <dir> --cross-file --auto-entries --bugs # cross-module (link each dir),
                                            # attacker entries derived automatically
solver scan <dir> --reachable --entries <f> --bugs   # per-entry whole-program slice
solver facts <dir> [--closed-world]         # streaming whole-program facts (no linking):
                                            # extract summaries + pointer/scalar/field
                                            # contracts for a whole tree in bounded RAM,
                                            # report coverage + peak RSS
```

**Memory / parallelism knobs** (soundness-neutral — they only throttle; every unit
is still analysed identically): `CSOLVER_JOBS=<n>` caps the worker count (fewer
concurrent modules ⇒ lower peak RSS), `CSOLVER_MEM_RESERVE_MB=<n>` raises the
per-in-flight memory reserve so fewer large modules start together. Use them to fit
a whole-kernel `--cross-file` scan under a memory ceiling.

Exit codes: `verify` — `0` PASS · `1` FAIL · `2` UNKNOWN · `3` tool error.
`scan` exits `1` iff any bug was found (it is an inventory, not one verdict).

## Differential validation

```sh
differential/run.sh          # Rust vs Miri
differential/c/run.sh        # C vs ASan+UBSan (verify mode)
differential/c/run.sh --bugs # C vs ASan+UBSan (bug-finding mode)
scaling/kernel/run.sh <dir>  # sweep real kernel LLVM IR for bug candidates
```

## License

Apache-2.0.
