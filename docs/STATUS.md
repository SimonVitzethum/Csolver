# Status

Milestone **M1 — symbolic execution + SMT (increment 1 done)**, on top of the
completed **M0 — architecture + foundations**.

## Pointer-walk loops (`for x in s`): `iter != end`

The fully-optimized iterator shape — a moving pointer walked until it reaches an
end pointer — now verifies (header-test form). Two pieces make it sound: (1)
**pointer-aware comparison** — `iter == end` between two pointers into the *same*
allocation is evaluated as the offset relation `o == end_off` (differing/opaque
provenance still falls back to fresh, sound); and (2) **pointer equality-exit
induction** — `csolver-absint::induction` recognizes a pointer header-parameter
that steps by a constant element stride (`iter := iter + 1`) and exits on `iter
== end`, and the engine restores `iter`'s region provenance with a fresh offset
`o` constrained by `0 ≤ o ≤ end_off ≤ size` and the **congruence** `o ≡ 0 (mod
stride)` — but **only after proving** `0 ≤ b0 ≤ end_off ≤ size ≤ isize::MAX` and
`stride | (end_off − b0)` (the region's no-wrap premise supplied for a symbolic
slice length). The congruence is what the integer index loop did not need: a
load reads `stride` bytes, so `o ≤ end_off − 1` is insufficient — `o ≡ 0 mod
stride` with `o < end_off` gives `o ≤ end_off − stride`, hence `o + stride ≤
end_off ≤ size`. With the guard `iter != end` (`o != end_off`) the moving load is
proved in bounds (`ptr_walk_loop` → PASS); an end pointer past the buffer fails
the `end_off ≤ size` check, so the offset is never installed and the load is not
proved (`ptr_walk_loop_oob` → not PASS). The rotated `-O` (bottom-test) form,
where the exit compares the *stepped* pointer and the load precedes the check
(needing a preheader-guard analysis), is the next step.

## Equality-exit loops (`while i != n`): induction bounds

The `!=`/`==`-exit loop — the integer precursor of the pointer-walk (`iter !=
end`) — now verifies. The interval domain widens a counter governed by `i != n`
to `[0, +∞]` (a `!=` guard refines no interval), so it cannot bound the access.
A new **equality-exit induction** analysis (`csolver-absint::induction`)
recognizes, purely syntactically and conservatively, a header counter `i` that
steps by a constant positive stride and exits on `i == bound`. The symbolic
engine then asserts the invariant `start ≤ i ≤ bound` — but **only after proving
the soundness side-conditions**: `0 ≤ start ≤ bound ≤ isize::MAX`, and `stride |
(bound − start)` so `bound` lies on the counter's grid (otherwise `i` steps
*over* `bound`, never hits the `== bound` exit, and could exceed it — an unsound
bound). With the loop guard `i != bound` this yields the strict `i < bound`, so
`buf[i]` is proved in bounds (`eq_exit_loop` → PASS); an exit bound past the
buffer is still not proved (`eq_exit_loop_oob` → not PASS). This is stage 1 of
the pointer-walk loop; stage 2 carries the same reasoning to the pointer offset
plus a congruence fact (`offset ≡ 0 mod stride`).

## Definedness: no read of uninitialized memory

The symbolic engine now checks a new memory-safety property — **definedness** —
annotation-free: a freshly-allocated region (one with no caller contract) holds
*uninitialized* bytes until written, and reading them is undefined behaviour in
Rust. Resolving a `Load` against the store log now reports its origin (`Stored` /
`Uncertain` / `Unwritten`); an `Unwritten` load from a fresh allocation on an
**exact** path is a *definite* read of never-written memory and is **refuted** as
a `ValidRead` violation with a feasibility witness. The check is **sound and
additive**: it fires only when the path is exact (complete store log), the scan
saw no may-aliasing store (so the bytes are provably unwritten), and the region
is a fresh allocation (a contracted `&[T]`/`&mut [T;N]` parameter is
caller-initialized, hence never flagged) — so it adds new `FAIL`s for
uninitialized reads without turning any initialized read into `UNKNOWN`
(`uninit_read` → FAIL, `init_read` → PASS). This is the first piece of the
shape/ownership analysis: the validity *state* of allocated bytes, inferred
without any per-code annotation.

## Toward real binaries: ELF loader

`csolver-elf` now **parses real ELF64 objects** in pure Rust (no `object`/`gimli`):
the header, the section table (names, vaddr/size/file-offset, R/W/X permissions),
and the symbol table (functions and their sizes). `Image::function_code` recovers
a function's exact machine bytes. Parsing is bounds-checked throughout, so a
malformed image is a clean `Error`, never a panic.

`csolver-asm` then **decodes x86-64 machine code → MSIR** (`x86::decode_function`):
a straight-line function's bytes become MSIR instructions (registers → `RegId`s,
`[base]` memory operands → `Load`/`Store`). So the **whole binary pipeline now
runs end-to-end**: a real ELF object's `xor eax,eax; ret` is loaded, decoded,
lowered, and verified **PASS**; a raw-pointer store (`mov [rdi], rsi`) is
`UNKNOWN` (nothing proves `rdi` valid); a `syscall` (undecoded) is `UNKNOWN` —
never a false PASS (`tests/binary.rs`). The decoded subset is tiny but grows
monotonically: any unrecognized opcode makes the function `unanalyzed`
(`UNKNOWN`), never silently mis-modelled.

Crucially, the binary pipeline can now **prove a real memory access safe**, not
just decode it: `sub rsp, N` is modelled as allocating an `N`-byte stack frame
(with `rsp` the pointer), so a `[rsp + disp]` store (decoded through a SIB byte)
is checked against the frame. `sub rsp,16 ; mov [rsp+8], eax ; ret` verifies
**PASS** (the store is in the frame); the same with `[rsp+32]` is **FAIL** (a
definite out-of-bounds write).

The decoder also **reconstructs control flow**: it splits the body into basic
blocks at branch targets and lowers `jmp`→`Br`, `jcc`→`CondBr` (with the condition
taken from the preceding `cmp`/`test`), and backward branches into back-edges. So
a *branchy* binary verifies end-to-end — a guarded stack store
(`cmp edi,0 ; jne .skip ; mov [rsp+8],eax`) is **PASS** (the state-merging engine
joins the paths), and a counting loop is handled (cut + interval invariant).

**Indexed addressing** (`[rsp + rcx*4]`, a SIB index×scale) and `lea` are decoded
too, and the SysV argument registers (`rdi…r9`) are modelled as parameters (stable
symbols). So a *binary array access with a bounds check* now verifies: `sub rsp,64
; cmp ecx,16 ; jae .end ; mov [rsp+rcx*4], eax` is **PASS** (the guard `rcx < 16`
bounds the index into the 16-element frame), while the same without the check is
**FAIL** (a definite out-of-bounds write).

A second decoder handles **AArch64 (ARM64)** binaries (fixed 32-bit instructions):
`ret`, `add`/`sub` immediate (incl. the `sub sp, sp, #N` frame), `ldr`/`str` with
a scaled offset, `cmp`, and `b`/`b.cond` — control flow reconstructed by the *same*
architecture-independent block assembler the x86 decoder uses. So the same proofs
hold on ARM, including *branchy* functions: `str w0,[sp,#8]` in a frame is **PASS**,
`str w0,[sp,#32]` is **FAIL**, and a guarded `cmp w0,#0 ; b.ne .skip ;
str w1,[sp,#8]` is **PASS**. The verifier now proves stack memory safety of
compiled **x86-64 *and* ARM64** functions, branchy or not. DWARF, the full ISA,
and PE/Mach-O follow.

## Bit-precise decision procedure (pure-Rust SAT)

`csolver-solver` now carries a self-contained **bit-precise** decision procedure
alongside the linear one — no external C/C++ solver. A bit-blaster (`bitblast`)
lowers the symbolic expression IR to CNF with exact fixed-width/wrapping
bit-vector circuits, an internal DPLL solver (`sat`) refutes it, and
`bitprecise::prove_implies` proves `assumptions ⟹ goal` exactly. The combined
`prove_implies_method` tries the fast linear procedure first, then a tight-budget
bit-precise **refinement** (a goal decided exactly is reported `BitPrecise` and
**carries no `linear-no-overflow` assumption**) and a bit-precise **fallback**
that proves goals the linear fragment cannot model — exact wrap-around and
bitwise masks. A real consequence: `buf[x & 7]` over a `[i8; 8]` verifies
**PASS** (the mask bounds the index to `[0, 7]`), which the linear procedure
alone leaves UNKNOWN. The fallback is bounded by a SAT decision budget and a CNF
size cap, so it never dominates analysis time (the whole suite still runs in
~2 s). `cargo test` = 133 green, 0 clippy/build warnings.

## Counterexamples (symbolic FAIL with a witness)

The symbolic engine can now **refute** a scalar safety check and attach a
concrete counterexample, not just prove or leave it `UNKNOWN`. On an **exact**
path (one with no loop-header havoc, opaque call, or non-determined load — so its
path condition describes genuinely reachable states), a check that is *definitely*
violated — `assumptions ⟹ ¬goal`, proved **bit-precisely** — becomes a `FAIL`
whose `Model` names the violating inputs (`bitprecise::find_counterexample`). This
mirrors the interval `False` verdict but with bit-precision: e.g. `(x | 8) < 8`,
which interval analysis cannot see through, is reported `FAIL` with a witness
(e.g. `arg0 = 0`), whereas a merely under-constrained scalar check like an
unconstrained `i < 8` stays `UNKNOWN` (only *definite* violations are refuted, so
under-specified helpers are not turned into spurious failures).

**Memory-access OOB** is refuted too: because a memory access *executes*, any
reachable out-of-bounds input is a real runtime violation, so the unguarded
write `buf[i]` into a `[i32; 8]` with an unconstrained `i` is `FAIL` with a
concrete witness (e.g. `i = 8`). This is sound on an **exact** path with a
**concrete**-size region: the only free variable is the access offset, so a
satisfying violation is a genuine reachable OOB and a wrapped `count * stride`
cannot fabricate a too-small buffer. A safe access (`buf[x & 7]` into a `[i32;8]`)
is still `PASS` — it is *proved* before any refutation is attempted. This reaches
**dynamically-sized** buffers too: `buf[i]` into an `alloc [i32; n]`, or
`s.get_unchecked(i)` on a slice `&[i32]`, is `FAIL` with a witness for the length
*and* the index, because a valid allocation/slice has `n * 4 <= isize::MAX` (so
the symbolic size cannot wrap) — a premise added only to the refutation query so
proofs stay fast.

**Temporal** violations (use-after-free, double-free) are refuted as well: on an
exact path a region only reaches `Freed` through an explicit deallocation, so an
unconditional `buf = alloc; free(buf); *buf = 0` (or a second free) is `FAIL` with
a feasibility witness, while a *maybe*-freed region (after a freeing call or loop)
stays `UNKNOWN`. So the verifier now produces counterexamples for both spatial and
temporal safety.

## Relational loop invariants (zone domain)

Beyond the per-variable interval domain, a **relational** `Zone` (difference-bound)
domain (`csolver-absint`) tracks `vⱼ − vᵢ ≤ c` between registers — the invariants
intervals cannot express. The symbolic engine adds a loop header's zone invariants
as facts on the havoc'd variables, so a loop whose safety is a *relation* between
variables verifies: `for (i,j)=(0,0); i<n; i++,j++ { buf[j] = 0 }` is **PASS**
because the zone supplies `j ≤ i`, which with the guard `i < n` gives `j < n` —
something neither intervals nor the loop guard (on `i`, not `j`) can prove alone.
The zone's widening is a terminating *keep-if-equal* operator and its closure is
sound (argued in the crate's `Verification/`).

## Scaling: path-feasibility pruning + state merging

Two changes stop path explosion from forcing truncated, all-`UNKNOWN` runs.

**Pruning** drops a conditional branch whose guard is bit-precisely unsatisfiable
under the current path condition — a dead branch with no concrete execution. The
check is bit-precise (not linear), so it can never discard a branch that is
reachable only through wraparound and hide a real bug.

**State merging** processes the (back-edge-cut) CFG in reverse postorder, visiting
**each block once**: a join's incoming edge-states are merged into one entry state
— block parameters (PHIs) become an `ITE` keyed on each edge's path condition (so
an access on a merged value stays precise), regions keep the common prefix with a
conservative lifetime, and the path condition/facts weaken to the common
prefix/intersection. So a CFG with *N* independent branches is analysed in
*O(blocks)* instead of *O(2^N)* paths — a 256-path function verifies under a
40-visit budget — while single-predecessor (branch) blocks stay fully precise.

## First real front-end: LLVM-IR

`csolver-llvm` now **parses and lowers textual LLVM IR** (a practical subset) to
MSIR — the first input that is not hand-built. The audited analysis core is used
unchanged. `solver verify file.ll` works end-to-end: a guarded `[8 x i32]`
store, a `phi`-based `for i in 0..16` loop, and an out-of-bounds store verify to
PASS / PASS / not-PASS respectively (`tests/llvm_frontend.rs`). PHIs are lowered
to MSIR block parameters; unsupported constructs degrade to `UNKNOWN` (never a
silent PASS). Multi-way **`switch`** (Rust `match` / enum-discriminant dispatch)
lowers to MSIR's native `Switch` — each case is an exact edge guard
(`value == cⱼ`), the default a sound over-approximation — so a `match` that
stores into a local buffer per arm verifies **PASS** and an out-of-bounds arm is
correctly not proved. The parser tolerates real `rustc --emit=llvm-ir` shape (mangled
names, attributes, metadata, `!dbg`, `; preds` comments) and **imports pointer-
parameter contracts** (`dereferenceable(N)`/`align`/`readonly`/`writeonly`): a
real `rustc -O` function taking `&mut [i32; 8]` and writing `buf[i]` under a
`i < 8` guard verifies fully **PASS** (under the `param-contracts` assumption);
a write through a `readonly` parameter is correctly not proved. **Vectors and
`llvm.lifetime`/`dbg` intrinsics** (from `-O`) are handled too: a real `rustc -O`
function that builds a local `[i32; 8]` via `<4 x i32>` vector stores and reads
`buf[i]` under a guard verifies fully **PASS**. **Per-function recovery** lets a
whole `rustc -O` `.ll` be processed: a function with an unsupported construct is
recorded and reported `UNKNOWN` rather than failing the module. On a real
4-function compiled crate, three functions verify **PASS**. **Slice parameters**
(`&[T]` = `(ptr, usize len)`) are now imported too: a real `rustc -O`
`get(s: &[i32], i) -> if i < s.len() { s[i] }` verifies **PASS** (region size =
`len * size_of::<T>()`, under the `slice-abi` assumption), while an unguarded
slice index is correctly not proved. **Index-based slice loops**
(`while i < s.len() { … s[i] … }`) verify too — a real `rustc -C opt-level=0`
`sum_indexed` (with its `panic_bounds_check` machinery) verifies fully PASS
(51/51). The fully-optimized iterator form (`for x in s`) lowers to a vectorized
**pointer-walking** loop (`iter != end`) needing a relational pointer-offset
domain + congruence reasoning — genuinely advanced — so it stays `UNKNOWN`
(never a false PASS). **Bulk memory** (`llvm.memcpy`/`memmove`/`memset`) is
checked too: a real `rustc -O` `*dst = *src` over `&mut [u8; 16]` (a 16-byte
`memcpy`) verifies **PASS** (destination writable + in bounds for `len`, source
readable + in bounds), while copying past a region's size is not proved. This is
the shortest path to verifying compiled Rust; see [ROADMAP.md](ROADMAP.md).

## Soundness audit

The discharge pipeline was audited for **false-PASS** bugs (the only fatal
defect for a verifier). Five were found and fixed, each with a regression test;
see [AUDIT.md](AUDIT.md). The honest path from here to full Rust/assembly/binary
coverage is in [ROADMAP.md](ROADMAP.md).

## M1 increments 1–5 (current)

- **Increment 5 — interprocedural summaries.** Each function gets a summary:
  its memory **effects** (writes/frees, propagated to a call-graph fixpoint — so
  recursion is sound) and its **return value** as a parameter-relative template
  (a parameter pointer plus an affine offset, the wrapper/accessor shape). At a
  call, a pure callee no longer invalidates the caller's heap, and a returned
  pointer is rebuilt against the actual arguments **keeping its provenance**.
  The `interproc_caller` demo (`p = first(buf); *p = 0`) is **PASS** — even
  though the wrapper `first` cannot prove its own parameter-pointer arithmetic
  in isolation (it is only safe under preconditions, so it stays UNKNOWN
  standalone). `solver demo` now reports **34 PASS / 1 FAIL / 2 UNKNOWN**.

- **Increment 4 — symbolic heap + alias analysis.** Each path carries a symbolic
  store; a `Load` resolves via `AliasResult` (Must/May/No) against prior stores,
  so a pointer's provenance survives a store→load round-trip. Distinct
  allocations never alias; within one, offsets are compared by the solver. The
  raw-pointer-through-memory pattern (`indirect_store`: store `buf`→slot, load,
  deref) is fully **PASS**. Loop-modified memory is conservatively forgotten at
  headers. `solver demo` now reports **29 PASS / 1 FAIL / 1 UNKNOWN**.

- **Increment 3 — loops.** The symbolic engine no longer skips loops. Back-edges
  are cut and each loop header's parameters are havoc'd to fresh symbols
  constrained by the sound interval invariant (from `csolver-absint`); one pass
  over the body under that invariant plus the loop guard covers every iteration.
  The canonical `for i in 0..n { buf[i] = 0 }` (`loop_array_store`) is now fully
  **PASS** — `i >= 0` from the invariant, `i < n` from the guard, combined by
  the linear solver. `solver demo` reports **14 PASS / 1 FAIL / 1 UNKNOWN**.



### Increments 1–2 (symbolic foundation + memory)
sicherheit?

A sound symbolic-execution engine that **turns whole classes of UNKNOWN into
PASS** without weakening soundness:

- **Increment 1.** `csolver-solver` gained a hash-consed symbolic expression IR
  (`expr`) and a sound incomplete **linear decision procedure**
  (`linear::prove_implies`, Fourier–Motzkin). `csolver-symbolic` discharges
  scalar `SafetyCheck`s path-sensitively. `guarded_get` (`i<len` under a guard)
  is now PASS.
- **Increment 2 — symbolic memory.** `csolver-symbolic` now models pointers
  (provenance + symbolic offset + alignment, never bare integers) and a
  per-path region table (size, lifetime, permissions). It decides the canonical
  obligations of `Load`/`Store`/`PtrOffset`/`Dealloc` — non-null, no-UAF,
  in-bounds, alignment, read/write permission, valid pointer arithmetic,
  no-double-free. The verifier enumerates these from the IR
  (`Inst::implied_checks`), so a memory op is **never silently passed**.
  `solver demo`'s `safe_buffer_store` (a guarded `buf[i]` write into a freshly
  allocated `[i32; n]`) is fully **PASS**; a use-after-free stays **UNKNOWN**
  (never a false PASS). Proofs surface their `alloc-succeeds` /
  `linear-no-overflow` assumptions.

This increment is `Proven`/`Unknown` only — it never *refutes* (a sound FAIL
needs a satisfiable model on a provably-reachable path; the UNSAT-only solver
cannot supply one). Constant violations are still caught as FAIL by intervals.

Remaining M1 increments (planned, see ARCHITECTURE §8): loop summaries +
dominator-based path **merging**; heap-content/`memcpy` modelling + **alias
analysis** (Must/May/No); **function summaries** + direct/mutual **recursion**
via iterative fixpoints; counterexample **model extraction** for FAIL; external
SMT backends (Bitwuzla → Z3 → CVC5) behind the existing `SmtSolver` trait; the
large unit/integration/property/fuzz corpus.

---

## M0 — architecture + foundations (done)

## Implemented and tested

| Crate | What works now |
|---|---|
| `csolver-core` | Verdict lattice, proof obligations/results, proof trees, counterexamples, bit-vectors. |
| `csolver-ir` | MSIR types: typed block-argument SSA, explicit memory ops, `SafetyCheck`, C-style layout. |
| `csolver-cfg` | CFG, dominators, post-dominators, natural loops (Cooper–Harvey–Kennedy). |
| `csolver-memory` | Region/pointer model; concrete decision of in-bounds / UAF / double-free / alignment / null / permissions; symbolic ⇒ residual. |
| `csolver-absint` | Interval lattice + widening/narrowing, generic worklist fixpoint, MSIR transfer, sound trivalent condition evaluation. |
| `csolver-solver` | Bit-vector constraint IR + meaning-preserving simplifier. |
| `csolver-smt` | `SmtSolver` trait + sound `NullSolver` fallback. |
| `csolver-parser` | Cursor + diagnostics plumbing. |
| `csolver-verifier` | Obligation generation + interval discharge + verdict roll-up → `ModuleReport`. |
| `csolver-report` | Text + JSON rendering. |
| `csolver-cli` | `solver demo` runs the full pipeline; `verify` dispatches to frontends. |

Run `cargo test` (61 tests) and `cargo run -p csolver-cli -- demo`.

## Interface-only stubs (return `Unsupported`)

`csolver-mir`, `csolver-asm`, `csolver-elf` — public APIs fixed, lowering to
come. (`csolver-symbolic` is fully implemented since M1; `csolver-llvm` parses
and lowers a real subset since the LLVM-IR front-end landed.)

## Working end-to-end slice

`solver demo` proves an in-bounds check (PASS, with an interval proof tree),
refutes an out-of-bounds check (FAIL, with a counterexample), and reports a
symbolic check as UNKNOWN (with the residual obligation and a suggested minimal
assumption). This exercises every implemented crate.

## Next (see ARCHITECTURE.md §8)

M1 LLVM-IR frontend + branch-condition refinement → first real in-bounds proofs
of compiled Rust; M2 symbolic execution + internal BV solver + counterexample
models; M3 Z3 + heap arrays (UAF/double-free); M4 ELF+x86-64; M5 MIR + borrow
facts + interprocedural summaries.
