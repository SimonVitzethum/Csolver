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
