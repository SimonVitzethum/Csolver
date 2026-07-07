# CSolver

A **formal memory-safety verifier** for Rust (including `unsafe`), C, and C++,
operating on Rust MIR, LLVM-IR, x86-64 / AArch64 assembly, and ELF binaries.

CSolver has two modes:

- **Verification (default).** It *proves* the absence of memory errors. When a
  full proof is impossible (theory limits or missing information), it explains
  precisely why, lists the minimal extra assumptions or annotations that would
  close the proof, or produces a concrete counterexample. A false `PASS` and a
  false `FAIL` are both treated as bugs.
- **Bug-finding (`--bugs`).** A recall-oriented mode for finding real memory bugs
  in kernel-style C (out-of-bounds, use-after-free, double-free,
  `copy_from_user` overflows), each reported with a concrete triggering input.

## Status

The common IR (MSIR) and the full pipeline — symbolic execution, memory model,
loops, alias-aware heap, interprocedural summaries, and the internal bit-precise
solver — are implemented and audited for soundness. The **Rust (MIR)** and
**LLVM/C** frontends are mature: the LLVM path handles optimized IR, DWARF field
recovery, C/kernel allocators, `copy_from_user`, and inline assembly, and runs on
real Linux-kernel IR. **C++** goes through the same LLVM path.

Every verdict is checked against a **dynamic oracle**: Rust against **Miri**, C
against **AddressSanitizer + UBSan** (see [differential/](differential/)). The
`--bugs` mode finds all 8 memory-bug classes in the C differential corpus with
**zero false positives**. The **asm** and **ELF** frontends are the next major
work — see [docs/STATUS.md](docs/STATUS.md), [docs/ROADMAP.md](docs/ROADMAP.md),
and [ARCHITECTURE.md](ARCHITECTURE.md).

## Properties targeted

No out-of-bounds access · no use-after-free · no double-free · no dangling
deref · no null deref · stack integrity · valid pointer arithmetic · valid
references · valid reads/writes · no forbidden region overlap · alignment ·
valid stack frames · valid indirect branch targets.

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
solver verify <path>              # a .rs (turnkey), .mir, .ll, .s, or ELF
solver verify <module.ll> --closed-world   # whole-program: synthesize contracts
solver verify <module.ll> --bugs           # bug-finding mode (find, don't prove)
solver verify <module.ll> --pre <file>     # caller preconditions (bytes/elements/cstring)
solver verify <path> --json                # machine-readable report
```

Exit codes: `0` PASS · `1` FAIL · `2` UNKNOWN · `3` tool error.

## Differential validation

```sh
differential/run.sh          # Rust vs Miri
differential/c/run.sh        # C vs ASan+UBSan (verify mode)
differential/c/run.sh --bugs # C vs ASan+UBSan (bug-finding mode)
scaling/kernel/run.sh <dir>  # sweep real kernel LLVM IR for bug candidates
```

## License

Apache-2.0.
