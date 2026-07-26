# CSolver vs Miri — capability assessment

**One line:** they are *complementary*, not competing. CSolver **proves** memory safety over **all**
inputs across **many languages** (Rust MIR, C/C++/LLVM, asm, binaries) with an explicit
named-assumption layer; Miri **observes** UB on **executed** Rust runs with unmatched fidelity on the
hard-to-model UB classes. CSolver's cardinal rule is *never a false PASS*; Miri's is *no false
positive on a run*. The `differential/` harness pits them against each other precisely to catch a
hypothetical CSolver false PASS.

Grounded in the source (`differential/run.sh`, `crates/core/src/property.rs`,
`crates/symbolic/src/exec/checks.rs`, `crates/mir/`, `README.md`, `docs/soundness-invariants.md`).

---

## The two soundness models

| | Miri | CSolver |
|---|---|---|
| Nature | **Dynamic** — interprets Rust MIR on concrete inputs | **Static** — symbolic/abstract proof |
| Guarantee | No UB on the **executed** path (needs a runnable entry + inputs) | Safe on **all** inputs, or honest `UNKNOWN` / `FAIL` |
| Failure it forbids | false *positive* on a run | false **PASS** (and, in practice, false FAIL) |
| Coverage | only inputs actually run (hence the harness fuzzes 32 inputs/fn) | every path the frontend can model; the rest → `UNKNOWN` |

The differential oracle (`differential/run.sh`) encodes exactly this: the **only** failure is
`miri=UB && cs=PASS` (a false PASS). A Rust panic is treated as safe ("CSolver proves memory safety,
not panic-freedom"). Latest corpus run: 24 fns, 0 false PASS, 10/10 UB shapes caught (as UNKNOWN,
never PASS), 11/14 safe fns precise.

---

## What CSolver does that Miri cannot

- **Proof over ALL inputs**, not a concrete run — the whole reason the harness exists.
- **Multi-language / multi-frontend** into one IR (MSIR): Rust MIR (`crates/mir`), LLVM-IR = C/C++/
  Rust-via-LLVM (`crates/llvm`), x86-64 + AArch64 asm (`crates/asm`), and ELF/PE/Mach-O binaries +
  DWARF, plus ISO/WIM containers (`crates/elf`). Miri is Rust-MIR only.
- **Whole-program scale without linking or a test harness** — streaming summaries proven
  bit-identical to the linked module (`summarize_program_equals_summarize_of_the_linked_module`).
- **Bug-finding with concrete witnesses** (`--bugs`): 8 memory-bug classes, each with a triggering
  input model.
- **Named-assumption layer**: `--assume-valid-params/-returns/-loop-ptrs/…`, `--closed-world` — each
  opt-in, unsound-in-general, and named in the proof tree. Miri has nothing analogous.
- **In-house bit-precise CDCL solver** cross-checked by a brute-force oracle; only `Unsat` is trusted.

## What Miri does that CSolver does not (or only partially)

| UB class | CSolver status | Gap vs Miri |
|---|---|---|
| **Stacked/Tree Borrows** (`&mut` uniqueness, use-after-invalidation, protectors, 2-live-`&mut`) | `NoAliasingViolation`, **opt-in `--aliasing-model`, off by default**; only "write-through-shared-`&T`" refuted | Miri far more complete. Full borrow-stack = frontend retag events + derivation trees (future). **← the biggest Rust-fidelity gap.** |
| **Value-validity invariants** (`bool ∉ {0,1}`, invalid enum discriminant, `NonNull` holding null) | none — discriminant is deliberately opaque so all arms explore | **Full gap.** Miri detects these; CSolver does not. |
| **Strict provenance / int-to-ptr exposure** | provenance is a *capability* lattice (Copy-Fail write-to-read-only), not address-exposure | Different purpose; no Miri-style provenance-UB check. |
| **General inter-thread data races** | `DataRace` = **AA self-deadlock only**; lockset/ABBA are `--bugs` heuristics (now HB-pruned) | No sound race decision procedure (the "biggest single investment"). |
| **Uninitialized reads** | `ValidRead` + `unwritten_reads` (definite/exact only) + `NoInfoLeak` (copy_to_user of unwritten) | Partial: definite-only, less aggressive than Miri's per-byte tracking. |
| **Float UB** | none found | Gap. |
| **Unwind across FFI** | none | Gap. |

## Where CSolver is strong (proven over all inputs, bit-precise)

Out-of-bounds (read/write/one-past-end), use-after-free, double-free, null deref, alignment,
div/mod-by-zero, shift-past-width, `nsw`/`nuw` integer overflow, `var*var` allocation overflow,
`copy_to_user` uninitialized-disclosure. On these the bit-blaster is proven equal to oracle
arithmetic, and the differential shows **zero false PASS** on the Rust corpus.

---

## Practical guidance

- **Proving a Rust library safe over all inputs, or analysing C/kernel/firmware/binaries** → CSolver
  (Miri can't reach non-Rust, and needs concrete runs).
- **High-fidelity `unsafe` Rust borrow/provenance/value-validity checking on a test suite** → Miri
  (CSolver's aliasing is opt-in/partial; value-validity absent).
- **Best practice** → both: CSolver for the all-inputs proof + non-Rust reach, Miri as the concrete
  ground-truth oracle (which is exactly how `differential/` uses it to guard against a false PASS).

## Roadmap implication (tracked in `TODO.md`)

To close the Miri-superior gaps in CSolver: (1) complete the Stacked/Tree-Borrows model (retag
derivation trees, `&mut` uniqueness, protectors) behind `--aliasing-model`; (2) add value-validity
obligations (bool/discriminant/`NonNull`) from MIR type info; (3) the inter-thread happens-before/
thread model for true data races; (4) float UB. Items (1)–(4) are the honest "not yet covered vs
Miri" list.
