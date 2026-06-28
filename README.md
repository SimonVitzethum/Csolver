# CSolver

A **formal memory-safety verifier** for Rust — including `unsafe` — operating
on Rust MIR, LLVM-IR, x86-64 / AArch64 assembly, and ELF binaries.

CSolver is **not** a bug finder. It tries to *prove* the absence of memory
errors. When a full proof is impossible (theory limits or missing
information), it explains precisely why, lists the minimal extra assumptions or
annotations that would close the proof, or produces a concrete counterexample.

## Status

**M0** (architecture + foundations) and **M1 increments 1–5** (symbolic
execution + memory model + loops + alias-aware heap + interprocedural summaries)
are done and audited for soundness. On the common IR (MSIR) CSolver already
proves spatial + temporal safety for constant, guarded, **loop**, and
**cross-call** accesses. The front-ends that consume real Rust/LLVM/asm/ELF are
the next major work — see [docs/STATUS.md](docs/STATUS.md),
[docs/ROADMAP.md](docs/ROADMAP.md), and [ARCHITECTURE.md](ARCHITECTURE.md).

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

## CLI (target surface)

```sh
solver verify <binary.elf>
solver verify <module.ll>
solver verify <asm.s>
solver verify --crate <path>
solver report <result.json>
```

## License

MIT OR Apache-2.0.
