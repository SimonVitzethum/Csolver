# Verification — csolver-elf

## Design
Object loader (M4): ELF (then PE/Mach-O) sections, symbols, relocations, DWARF,
PLT/GOT, TLS, exception tables — the context the asm frontend and memory model
need.

## Specification (target)
- Section permissions map to `Region` permissions (`.text` R-X, `.rodata` R--,
  `.data`/`.bss` RW-).
- DWARF supplies stack-frame layout and types for `StackIntegrity`/typed checks.

## Assumptions (to be added to reports)
- The `object` and `gimli` crates (first external deps) parse the formats
  correctly; this is recorded as a named assumption in every binary-level proof.

## Limits
- M0 is interface-only (`load` → `Unsupported`).
- Stripped binaries (no DWARF) lose typed/frame precision ⇒ more `UNKNOWN`.

## Proofs (arguments)
- Loader correctness is checked structurally (section/symbol counts, address
  ranges) against `readelf`/`llvm-readobj` on a corpus.

## Test strategy
Planned: parse a corpus of Rust-compiled ELF objects and cross-check
sections/symbols/relocations against `llvm-readobj` (M4).
