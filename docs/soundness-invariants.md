# Machine-checked soundness invariants

The cardinal rule is **never a false PASS** (and, in practice, never a false FAIL). Most of the
argument for that lives in code comments and `docs/PROVABILITY.md`/`AUDIT.md`. This file is the
*index* of the invariants that are **executed as tests** — an oracle or an equivalence check that
would fail loudly if the property broke. It exists to lower the bus factor: when you change a load-
bearing component, this tells you which test already guards its soundness (and where a new one
belongs).

Each entry: **invariant — the check — where.**

## Decision core (`crates/solver`)

- **The bit-blaster equals plain arithmetic.** Every `w`-bit op (`Add`…`Mul`, `UDiv`/`SDiv`/
  `URem`/`SRem`, bitwise, constant *and* symbolic shifts, all comparisons) is checked against an
  independent `oracle_bin`/`oracle_cmp`: the correct result must be *provable* and a wrong result
  *not* provable. — `bitblast_tests.rs::bitblast_matches_oracle_4bit` (always on), `_6bit`
  (on-demand), `symbolic_shift_at_width_64_boundaries`, `wide_ops_at_width_128_are_bit_precise`
  (the full 128-bit domain), `division_by_zero_is_smtlib_total`. The whole engine is in-house
  (no external SMT backend); `MAX_WIDTH = 128`, and a 128-bit `udiv`/`sdiv`/`urem`/`srem` that
  exceeds the CNF cap falls back soundly to the linear procedure.
- **The CDCL SAT core only ever trusts `Unsat`.** Randomised brute-force oracle over thousands of
  instances, including ones that force restarts + clause deletion on hard 3-SAT. —
  `sat_tests.rs`.

## Frontend lowering fidelity (`crates/llvm`, `crates/symbolic`)

- **A shift's overflow is judged at the shifted value's width.** The `NoShiftOverflow`
  obligation bounds the amount by the width of the value being shifted, not the width at
  which the amount happens to be evaluated — a `lshr i64 x, zext(i32 k)` is safe iff
  `k < 64`, not `k < 32`. Guards against a false FAIL on any amount in `[32, 64)`
  (`AUDIT.md` P1). — `part_b.rs::shift_overflow_uses_the_shifted_value_width_not_the_amount_width`.
- **Integer min/max intrinsics lower to a real `select`, not an opaque scalar.**
  `llvm.{u,s}{min,max}` becomes `select(a <cmp> b, a, b)` with the comparison per the
  prefix, so a `MAKE_64BIT_MASK`-style clamp is reasoned about rather than havoc'd. —
  `part_b.rs::min_max_intrinsics_are_modelled_as_select`.
- **`fence` is a supported construct, not a dropped function.** An atomic `fence` lowers
  to a memory `Barrier` (no memory-safety obligation) instead of aborting the whole
  function as an unsupported instruction. — `part_b.rs::fence_does_not_drop_the_function`.

## Whole-program summaries (`crates/symbolic/src/summary`)

- **Link-free summaries equal the linked result.** `summarize_program(&[mods])` must equal
  `summarize_module(&merge_modules(mods))` key-for-key — proving the streaming, drop-as-you-go
  fixpoint reproduces the linked one (writes/frees, provenance, refcount, and the dangling-return
  wrapper propagation all compose identically). — `summary/tests.rs::
  summarize_program_equals_summarize_of_the_linked_module`, `summary_facts_stream_and_drop_equals_linked`,
  `wrapper_inherits_callee_dangling_stack_return`.
- **A dangling-stack claim is made only when definite.** A local on one path but not another must
  degrade to `Unknown`, never a false dangling claim. — `returning_a_local_stack_pointer_is_dangling`.

## Container / decompressor readers (`crates/elf`)

- **WIM LZX is byte-exact.** The decoder is cross-checked against 1475 real `boot.wim` resources by
  their stored SHA-1 (verified on the Win11 ISO; a self-contained chunk is embedded as a regression).
  Decompression is size-checked, so a decoder mistake is a clean failure, never garbage. —
  `wim_tests.rs`, `lzx` module. **LZMS stays a clean `Unsupported`** (no corpus to verify against —
  see `Todo.md`).
- **Every object/container read is bounds-checked.** A truncated/malformed image yields an error,
  never a panic or OOB read. — `elf_tests*.rs` (malformed-input cases).

## End-to-end oracles

- **C differential oracle.** `differential/c/run.sh` runs ASan+UBSan against CSolver on the same
  programs — the C analogue of Rust/Miri; `--selftest` positive-controls the expected count.
- **Rust/Miri differential.** Frontend fixtures cross-checked against Miri's verdict.
- **No false FAIL regressions.** Each detector added under `--bugs`/`--aliasing-model` ships with a
  *negative control* (a legitimate program that must stay PASS) alongside the positive case — e.g.
  the aliasing-model reborrow chains, the release/acquire MP robust case, the opaque-callback CFI
  control, the returned-parameter escape control.

## What is deliberately *not* machine-checked (and why)

- **Loop zone difference-bound facts** use wrapping add; sound only under `linear-no-overflow`, an
  assumption not re-recorded when a bit-precise proof consumes the fact. Pre-existing; differentials
  don't flag it; would need a zone-abstract-domain audit. (`AUDIT.md`.)
- **The exact-path refutation gate** (`state.exact`, cleared at calls/loops/merges) is *load-
  bearing*: refuting on an inexact path would fabricate false counterexamples, so strict `verify`
  trades recall for it and `--bugs` re-widens only to genuine-input goals. It cannot be relaxed in
  general without breaking soundness — this is the deliberate precision/recall boundary, not a bug.
- **StackIntegrity / ValidStackFrame** carry no dedicated emission by design: their concrete paths
  are subsumed by `InBounds` (overflow to a saved RA) and `ValidIndirectTarget` (call into data).

When you add a soundness-relevant feature, add its guard here.
