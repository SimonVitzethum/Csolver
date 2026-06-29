# Scaling test: CSolver over whole real crates

The [differential corpus](../differential) measures *soundness* — one hand-written
pattern per function, each verified against Miri. By construction it cannot answer a
different question: **what does real Rust actually contain, and how often?** Every
function in it is curated (and parses cleanly), so it silently assumes the front-end
is not the bottleneck.

This harness drops that assumption. It takes real, dependency-free crates straight
from the local cargo cache, emits their MIR (`rustc --emit=mir`), runs `solver
verify` over the *whole* crate, and aggregates **why** functions come back
`UNKNOWN`. The goal is not a PASS rate — it is a data-driven priority list, one level
up from the curated corpus: it tells us which construct, by frequency, would unlock
the most real code.

## Running

```
./run.sh
```

No network needed — the crates must already be unpacked under
`~/.cargo/registry/src/*/` (anything pulled in by a previous `cargo build`). Missing
crates, or crates that fail to compile to MIR, are skipped with a note. The sweep
covers a deliberate spread: arithmetic (`oorandom`, `adler2`), buffer formatting
(`itoa`, `hexf-parse`, `base64`), and — most relevant to memory safety — data
structures full of slices, indexing and `unsafe` (`smallvec`, `tinyvec`,
`arrayvec`).

## The finding (≈630 functions, 8 crates)

The first run came back **126 PASS / 0 FAIL / 513 UNKNOWN** — and the headline was
*not* the 20% PASS rate, it was **why** the rest were `UNKNOWN`:

- **≈98% of `UNKNOWN`s were front-end parse failures**, each losing a whole function
  before the analysis ever ran. The per-obligation "analyzed but a check is
  unproven" bucket was **empty** — the trusted analysis core is *not* the bottleneck
  at scale, the MIR parser is.
- **0 FAIL** across 630 real functions — no spurious refutations.

The curated differential corpus could never surface this: it is hand-written MIR
that parses by construction. The dominant gaps were all **boring parser robustness**:

| first run | parse error | real syntax |
|---|---|---|
| ~241 | `expected a word, found '<'` | **impl-method headers** `fn <impl at …>::method`, generics |
| ~101 | `expected a word, found ':'` | qualified paths `core::result::Result` |
| ~59 | `expected a local, found <ident>` | path / enum-variant operands |
| ~6 | `expected an integer, found "CAP"` | const-generic array length `[T; CAP]` |
| ~10 | unsupported construct | genuine lowering gaps (small!) |

## Acting on it: iterative parser fixes, ~4× the PASS rate

The measurement paid for itself immediately. A sequence of small, *low-TCB-risk*
front-end fixes — robust type parsing (qualified paths, generics,
`<T as Trait>::Assoc`, const-generic array lengths, `{closure@…}` types →
opaque), impl-method headers (`fn <impl at …>::m`), path/aggregate operands
(`RangeTo::<usize> { … }`, tuple aggregates, associated-const paths), and
diverging calls (`… -> unwind continue`) — lifted the whole sweep:

```
first run:  126 PASS    0 FAIL    513 UNKNOWN   (20%)
after:      486 PASS    0 FAIL    129 UNKNOWN   (79%)
```

`smallvec` alone went 1 → 151 PASS, `arrayvec` 95 → 170.

### The differential corpus earned its keep mid-iteration

One of the parser fixes made a pathological debug-MIR function
(`cond_use_after_free`, a conditional free + dangling read) *parse* for the first
time — and it came back a **vacuous PASS** (zero obligations), a false PASS the
differential corpus caught immediately (Miri UB + CSolver PASS). The root cause was
a pre-existing parser bug the new coverage exposed: a `bbN (cleanup):` block header
was not recognised, so the block loop stopped at the first cleanup block and
**silently dropped every following block** — including, here, the block holding the
dangling read. A dropped block with a memory access is exactly an unsound vacuous
PASS. Recognising the annotation fixed it (the function is now `UNKNOWN`, since its
`drop` terminators are unmodelled), and it retroactively corrected ~35 other
functions across the sweep that had been silently vacuous-PASSing — which is why the
PASS count is an honest 486, not a flattering 521. The corpus is back to **0
soundness violations**.

This is the whole methodology in one episode: measuring at scale surfaced the gap,
acting on it exposed a latent unsoundness, and the differential guard caught it
before it shipped. At this stage the parser was genuinely the bottleneck — but the
claim that the per-obligation bucket was *empty* turned out to be a measurement
artifact, corrected below once the parser gaps had been closed enough for the real
distribution to show through.

## Caveats

- Generic functions are emitted as polymorphic MIR (type parameter `T` → an opaque
  aggregate), so a generic data-structure crate is a *lower* bound on what the
  analysis could prove on a monomorphised instance.
- `solver verify` is run per crate with a timeout; a crate that produces no
  per-function output (e.g. `base64` here) is a separate front-end issue to chase,
  not a 0% result.
- The crate set and versions depend on what the cargo cache happens to hold; the
  numbers are indicative, not a fixed benchmark.

## Correction (12-crate sweep): the per-obligation bucket was never empty

Four successive sweeps reported the per-obligation residual bucket as *empty*, and
that reading hardened into a tempting architectural claim — "the engine is
overdimensioned relative to the front end; all marginal value is in parser
completeness." **A 12-crate re-measurement (after the parser tail and field-of-field
lowering landed) refuted it.** The "empty" was a bug in this script's own
aggregation: it anchored on the `UNKNOWN PO …` line with `grep -A1`, which lands on
the `predicate:` line — the `residual:` is one line *further* down — so it matched
zero residuals every time. The bucket was never empty; it was never being read.

With the grep fixed (`grep -E "residual:"`, bucketing by the parenthetical
*root cause*), the honest distribution over **3874 PASS / 0 FAIL / 342 UNKNOWN**
(4216 functions, ~92%) is:

| residual root cause | POs | what it is |
|---|---:|---|
| `pointer provenance is not tracked` | 1822 | raw-pointer obligations (UAF / in-bounds / align / valid-read) on pointers with no tracked provenance |
| `memory operation not analyzed (loops, symbolic disabled, or truncated)` | 1437 | a memory op the engine did not symbolically evaluate — inside a loop, with symbolic off, or in a truncated body |
| `pointer may be null or have opaque provenance` | 429 | nullness unprovable |
| `could not prove the access stays in bounds` | 48 | a genuine in-bounds residual the solver could not close |

Whole-function front-end losses are now **down to ~32** (operand-path parse tail:
25× `expected a local, found <ident>`, plus a handful of `fn`/`Fn`/`static`/`core`
landings). The old top bucket — `could not be lowered to a known pointer` (the
"unlowerable mem access (42)", field-of-field + double-deref) — is now **0**: the
field-of-field lowering closed it entirely, double-deref included.

So the corrected finding is the **opposite** of the parked claim: the front end is
now nearly complete, and the dominant driver of `UNKNOWN` at scale is **engine
analysis depth** — pointer provenance tracking (1822) and loop/symbolic memory
evaluation (1437). These are real, prioritisable engine capabilities, not parser
chores. The lesson is the project's own methodology turned on itself: *the
aggregation is part of the measurement; an unverified bucket count is not evidence
of an empty bucket.* The four "empty" readings were the metric lying, not the engine
being idle.
