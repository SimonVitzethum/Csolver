# CSolver — Architecture

> A formal memory-safety verifier for Rust (including `unsafe`), C, and C++ at the
> MIR, LLVM-IR, x86-64/AArch64 assembly, and ELF levels — with an opt-in
> **bug-finding mode** for kernel-style C.

This document is the **authoritative architecture**. It is read *before*
implementing a component and kept current. Each component points at the
interfaces defined here.

---

## 1. Honest framing (scope & theoretical limits)

Full memory safety of arbitrary machine programs is **undecidable** (reduction to
the halting problem; Rice's theorem). CSolver therefore *cannot in principle*
return "PASS" automatically for every program. This is a mathematical limit, not
an implementation shortcoming.

CSolver's claim is stated precisely:

1. **Soundness before completeness.** A `PASS` means: *proven safe under the
   explicitly reported assumptions*. We never knowingly emit a `PASS` without a
   proof. When we cannot prove it we say `UNKNOWN` (with the open proof
   obligations) or `FAIL` (with a counterexample).
2. **Every assumption is explicit.** FFI boundaries, inline assembly, allocator
   nondeterminism, hardware memory ordering, and so on produce *named assumptions*
   that appear in the report. A proof is always relative to an assumption set.
3. **Three outcomes per proof obligation:** `PASS` (proof tree), `FAIL`
   (counterexample = a concrete model), `UNKNOWN` (residual obligations + a
   suggestion of the minimal extra annotation that would close it).

What is realistically *fully* provable: non-recursive or structurally-recursive
functions with bounded loops over linear pointer arithmetic whose indices can be
decided by interval/octagon invariants and the bit-precise solver — a large part
of real (including `unsafe`) Rust and real C. What is *not* automatically
decidable is flagged in the report with a reason.

### 1a. Two modes: verification and bug-finding

The same engine serves two goals, selected by a flag:

- **Verification (default).** Soundness-first: a false `PASS` **and** a false
  `FAIL` are both bugs. Refutation (a `FAIL`) is only emitted on an *exact* path,
  where the path condition characterizes genuinely reachable states.
- **Bug-finding (`--bugs`).** Recall-oriented: report a memory violation whose
  offending value derives only from **genuine inputs** (function parameters,
  `copy_from_user` data, or a unit-stride loop counter) even on an
  over-approximated path. Every reported `FAIL` still carries a concrete witness.
  The mode trades a small path-feasibility risk for far higher recall on real,
  call- and loop-heavy code; a false `FAIL` still matters (a bug-finder that cries
  wolf is useless), so the "no false FAIL" discipline is kept and measured against
  a dynamic oracle (see §6).

---

## 2. Core idea: one common memory-safety IR (MSIR)

The central architectural decision: **every frontend lowers into a single,
analysis-friendly intermediate form — MSIR** (`csolver-ir`). The expensive
analyses (abstract interpretation, symbolic execution, proof generation) are
written **once** against MSIR, not duplicated per frontend.

```
            ┌────────────┐  ┌────────────┐  ┌────────────┐  ┌────────────┐
  Source →  │ csolver-mir│  │csolver-llvm│  │ csolver-asm│  │ csolver-elf│
            │  (Rust MIR)│  │ (LLVM IR)  │  │ x86/ARM64  │  │ Loader/    │
            └─────┬──────┘  └─────┬──────┘  └─────┬──────┘  │ DWARF/Reloc│
                  │ lower         │ lower         │ lower   └─────┬──────┘
                  └───────┬───────┴───────┬───────┘               │ context
                          ▼               ▼                        ▼
                    ┌───────────────────────────────────────────────────┐
                    │                MSIR  (csolver-ir)                  │
                    │  typed, CFG-based IR with explicit memory ops      │
                    │  + SafetyChecks (proof obligations)                │
                    └───────────────────────────┬───────────────────────┘
                                                │
        ┌───────────────────┬───────────────────┼───────────────────┐
        ▼                   ▼                   ▼                   ▼
 ┌────────────┐     ┌──────────────┐    ┌──────────────┐    ┌──────────────┐
 │ csolver-cfg│     │csolver-absint│    │csolver-symbol│    │csolver-memory│
 │ Dom/PostDom│     │ domains +    │    │ symbolic     │    │ Region/Ptr   │
 │ Loops      │     │ fixpoint     │    │ execution    │    │ model        │
 └─────┬──────┘     └──────┬───────┘    └──────┬───────┘    └──────┬───────┘
       └───────────────────┴─────────┬─────────┴───────────────────┘
                                      ▼
                            ┌───────────────────┐     ┌──────────────┐
                            │  csolver-verifier │────▶│ csolver-solver│
                            │ builds & discharges│     │ constraint IR │
                            │ proof obligations │◀────│ simplify      │
                            └─────────┬─────────┘     └──────┬───────┘
                                      │                      ▼
                                      │               ┌──────────────┐
                                      │               │ csolver-smt  │
                                      │               │ (fallback:   │
                                      │               │  bit-precise)│
                                      ▼               └──────────────┘
                            ┌───────────────────┐
                            │  csolver-report   │  PASS / FAIL / UNKNOWN
                            │  proof tree,      │  + proof tree / counterexample
                            │  counterexample   │  + open obligations
                            └─────────┬─────────┘
                                      ▼
                            ┌───────────────────┐
                            │   csolver-cli     │  `solver verify ...`
                            └───────────────────┘
```

**Why one IR instead of N analyses?** (a) Soundness is argued in *one* place; (b)
a loop invariant expressed in MSIR holds regardless of the source level; (c)
cross-level links (e.g. MIR borrow info as a hint for the LLVM analysis) travel
through MSIR metadata rather than ad-hoc channels.

**Soundness of lowering.** Every frontend must satisfy a *refinement* property:
every concrete behaviour of the original is a concrete behaviour of the MSIR
(over-approximate states, under-approximate guarantees). This obligation is
recorded per frontend in its `Verification/`.

---

## 3. Crate topology and dependencies

Strictly acyclic layering (arrows = "depends on"):

```
                       csolver-core   (no internal deps)
                          ▲   ▲   ▲
        ┌─────────────────┘   │   └──────────────────┐
   csolver-ir            csolver-memory          (used by all)
   ▲    ▲    ▲                ▲
   │    │    └── csolver-cfg  │
   │    │            ▲        │
   │    └── csolver-absint ───┤
   │            ▲             │
   │    csolver-symbolic ─────┤
   │            ▲             │
 Frontends:     │         csolver-smt ◀── csolver-solver
 mir, llvm,     │             ▲             ▲
 asm, elf       │             └─────┬───────┘
 (→ ir)         └──────────── csolver-verifier
                                    ▲
                            csolver-report
                                    ▲
                              csolver-cli
                                    ▲
                            csolver-testsuite (dev, e2e)
```

| Crate | Responsibility | Depends on |
|---|---|---|
| `csolver-core` | verdicts, proof obligations, proof tree, IDs, diagnostics, abstract values/bit-vectors, `Result`/errors | — |
| `csolver-ir` | MSIR: types, functions, basic blocks, instructions, memory ops, `SafetyCheck` | core |
| `csolver-cfg` | CFG construction, dominator/post-dominator tree, natural loops, SCCs | core, ir |
| `csolver-parser` | shared lexer/parser infrastructure (tokens, spans, error recovery) | core |
| `csolver-mir` | Rust-MIR frontend → MSIR (uses borrow/panic info) | core, ir, parser |
| `csolver-llvm` | LLVM-IR frontend → MSIR (SSA, PHI, intrinsics, allocator/user-copy/asm modelling, DWARF field recovery) | core, ir, parser |
| `csolver-asm` | x86-64 (Intel/AT&T) + AArch64 → MSIR | core, ir, parser |
| `csolver-elf` | ELF loader, sections, reloc, symbols, DWARF, PLT/GOT/TLS | core, ir |
| `csolver-memory` | symbolic memory model: region, pointer, provenance, permissions, alignment, lifetime | core |
| `csolver-absint` | abstract-interpretation framework + domains (interval, congruence, …), induction analysis, widening/narrowing | core, ir, cfg, memory |
| `csolver-symbolic` | symbolic execution: merge-based path exploration, lazy init, interprocedural summaries, refutation | core, ir, cfg, memory, solver |
| `csolver-smt` | SMT-backend abstraction (+ a portable internal fallback solver) | core |
| `csolver-solver` | constraint IR (bit-vectors, zext, …), simplification, the bit-precise (bit-blasting) and linear procedures | core, memory, smt |
| `csolver-verifier` | orchestration: builds proof obligations from MSIR+analyses, discharges them, forms verdicts; contract synthesis; precondition sidecar | core, ir, cfg, memory, absint, symbolic, solver, smt |
| `csolver-report` | human- and machine-readable (JSON) output, proof tree, counterexample | core |
| `csolver-cli` | the `solver` binary: `verify` (`--closed-world`, `--bugs`, `--pre`) | all of the above |
| `csolver-testsuite` | real Rust/C programs with `unsafe`/raw pointers as end-to-end fixtures | verifier, cli (dev) |

The current scaffold is deliberately `std`-only and therefore reproducibly
buildable offline; external solver backends are introduced late and justified per
component in its `Verification/`.

---

## 4. The central interfaces (contracts)

These types/traits are the *contracts* between components. Details live in the
respective `lib.rs` doc comments; here is the conceptual overview.

### 4.1 Verdict & proof (`csolver-core`)

```rust
enum Verdict { Pass, Fail, Unknown }

enum SafetyProperty {            // the properties in scope
    InBounds, NoUseAfterFree, NoDoubleFree, NoDanglingDeref,
    NoNullDeref, StackIntegrity, ValidPointerArith, ValidReference,
    ValidWrite, ValidRead, NoForbiddenOverlap, Alignment,
    ValidStackFrame, ValidIndirectTarget,
}

enum Decision { Proven(ProofTree), Refuted(Model), Unknown }
```

### 4.2 MSIR (`csolver-ir`)

A typed, block-argument SSA IR. Memory operations are **explicit** and carry the
information needed for proof obligations:

```rust
enum Inst {
    Assign { dst, ty, value: RValue },
    Load  { dst, ty, ptr, align },
    Store { ty, ptr, value, align },
    Alloc { dst, region: RegionKind, elem, count, align },
    Dealloc { region: RegionKind, ptr },
    PtrOffset { dst, base, index, elem },   // byte-offset gep
    FieldPtr  { dst, base, field, size, align },
    MemIntrinsic { kind: MemKind, dst, src, len }, // memcpy/memset/UserFill
    Call { .. }, Intrinsic { .. }, Asm { .. },
    SafetyCheck { condition, .. },           // explicit proof obligation
}
```

Each `Load`/`Store`/`PtrOffset`/`Dealloc`/`MemIntrinsic` implies canonical
`SafetyCheck`s (`Inst::implied_checks`); a frontend may attach more from source
information (borrow, panic paths).

### 4.3 Frontend contract

```rust
trait Frontend { type Input; fn lower(&self, input: Self::Input) -> Result<ir::Module>; }
```

A function that fails to lower is recorded in `Module::unanalyzed` (with a reason)
and the rest of the module continues — per-function recovery, essential at kernel
scale where one unsupported construct must not drop a whole translation unit.

### 4.4 Abstract-interpretation contract (`csolver-absint`)

```rust
trait AbstractDomain: Clone + PartialEq {
    fn bottom() -> Self; fn top() -> Self;
    fn join(&self, other: &Self) -> Self;    // ⊔
    fn widen(&self, other: &Self) -> Self;   // ∇  (termination)
    fn narrow(&self, other: &Self) -> Self;  // Δ  (precision recovery)
    fn leq(&self, other: &Self) -> bool;     // ⊑
}
```

The fixpoint iterator (worklist + widening at loop headers identified by
`csolver-cfg`) is domain-generic. `csolver-absint` also carries the induction
analysis used to recognize counting loops.

### 4.5 Solver contract (`csolver-solver` / `csolver-smt`)

The engine reasons over a hash-consed bit-vector expression DAG (`ExprCtx`), with
two procedures: a **bit-precise** one (bit-blasting to SAT — exact, models
wraparound and `zext`, used for refutation) and a **linear** one (integer, used
for cheap proofs). External SMT backends (Z3/…) implement the same abstraction; a
portable internal solver is the default and keeps CI offline.

### 4.6 Verifier contract (`csolver-verifier`)

```rust
fn verify_module(module: &Module, config: &Config) -> ModuleReport;
```

Per-obligation strategy (escalating, cheapest first):
1. **Abstract interpretation** discharges the "obvious" checks (intervals).
2. **Symbolic execution + the bit-precise solver** for what AI cannot close;
   proves, or (per mode) refutes with a concrete model.
3. Anything left open → `UNKNOWN` with a residual and a suggested minimal
   annotation.

`Config` selects `closed_world` (whole-program contract synthesis) and
`bug_finding` (see §1a). A **precondition sidecar** (`--pre`) supplies caller
contracts C's types cannot express (`bytes`/`elements`/`cstring`/`sentinel`).

---

## 5. Data flow of `solver verify <input>`

1. `csolver-cli` detects the input kind (ELF/`.ll`/`.s`/`.rs`/`.mir`) and picks a
   frontend.
2. The frontend lowers to MSIR (LLVM: allocators → `Alloc`/`Dealloc`,
   `copy_from_user` → `UserFill`, inline asm → opaque havoc, DWARF → field
   pointee recovery). Un-lowerable functions go to `unanalyzed`.
3. `csolver-cfg` builds the CFG, dominators, loops.
4. `csolver-absint` computes invariants (intervals, inductions).
5. `csolver-verifier` synthesizes contracts (closed-world), builds proof
   obligations, and discharges them via AI, else via `csolver-symbolic` + the
   solver.
6. `csolver-report` renders PASS/FAIL/UNKNOWN with a proof tree or a
   counterexample, plus the assumption set the result rests on.

From MSIR onward the path is identical across source levels.

---

## 6. Differential validation (the soundness oracles)

Verdicts are checked against **dynamic** oracles that observe real UB:

- **Rust:** `differential/run.sh` runs CSolver against **Miri** over a curated,
  fuzzed corpus. `Miri UB + CSolver PASS` is a soundness violation (must be zero).
- **C:** `differential/c/run.sh` runs CSolver against **AddressSanitizer + the
  memory subset of UBSan** (spatial + temporal; arithmetic-only UB is excluded on
  purpose — CSolver proves memory safety, not overflow-freedom). It reports both
  false `PASS` and, for `--bugs`, false `FAIL`; both must be zero. `--selftest`
  positive-controls the violation detector so a reported "0" is not a broken metric.
- **Kernel:** `scaling/kernel/run.sh` sweeps LLVM IR emitted from a real Linux
  kernel build (`make LLVM=1 <file>.ll`) in `--bugs` mode and aggregates the FAIL
  candidates (see its README).

---

## 7. Cross-cutting: performance & incrementality

- **Parallelism:** functions are the natural unit (interprocedural via summaries).
- **Merge-based exploration:** joins with N predecessors are analysed once, not
  once per path, so wide CFGs do not blow up the path count.
- **Bounded exploration:** `ExecLimits` caps visits and wall-clock per function so
  an adversarial input cannot run unbounded.

---

## 8. Verification documentation per component

Each crate has a `Verification/` folder with **Design, Specification, Assumptions,
Limits, Proofs, Test strategy**. It records the component's *soundness argument*
and which assumptions it contributes to the global report.

---

## 9. Status

The common IR and the whole pipeline are implemented and audited: MSIR, CFG,
memory model, interval + induction AI, merge-based symbolic execution with an
alias-aware heap, interprocedural summaries, and the internal bit-precise/linear
solver. The **Rust (MIR)** and **LLVM/C** frontends are mature; the LLVM frontend
handles optimized IR, DWARF field recovery, C allocators, user-copies, and inline
asm. **C++** is handled through the same LLVM path (DWARF-validated with clang).
The **asm** and **ELF** frontends are the remaining frontend work.

For memory safety CSolver proves spatial + temporal safety for constant, guarded,
loop, and cross-call accesses, and — in `--bugs` mode — finds out-of-bounds,
use-after-free, double-free, and `copy_from_user`-overflow bugs on kernel-style C,
each validated against the ASan oracle. See `docs/STATUS.md` and the per-crate
`Verification/` for the authoritative, current detail.
