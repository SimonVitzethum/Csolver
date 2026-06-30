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
| `memory operation not analyzed` (loop/unsupported op) | 1437 | a memory op the symbolic model reached but could not decide |
| `pointer may be null or have opaque provenance` | 429 | nullness unprovable |
| `could not prove the access stays in bounds` | 48 | a genuine in-bounds residual the solver could not close |

Whole-function front-end losses are now **down to ~32** (operand-path parse tail:
25× `expected a local, found <ident>`, plus a handful of `fn`/`Fn`/`static`/`core`
landings). The old top bucket — `could not be lowered to a known pointer` (the
"unlowerable mem access (42)", field-of-field + double-deref) — is now **0**: the
field-of-field lowering closed it entirely, double-deref included.

### Splitting the second bucket honestly (the same discipline, one level down)

That 1437 row used to read `memory operation not analyzed (loops, symbolic disabled,
or truncated)` — three very different causes lumped into one string, one of which
("truncated") could have been a *hidden front-end body cut-off* masquerading as an
engine limit. That is the soundness-critical case the Miri oracle cannot catch (an
*incompletely* analysed function is not *wrongly* modelled), so it could not be left
ambiguous. The emission site now distinguishes them — `symbolic analysis disabled`
(config) / `symbolic exploration truncated at the visit budget` (coverage cap) /
`reached but not decided by the symbolic memory model` (the genuine per-op limit) —
and the re-measured split is unambiguous:

```
   1437  reached but not decided (loop body or unsupported op)
      0  symbolic exploration truncated at the visit budget
      0  symbolic analysis disabled
```

**All 1437 are the genuine engine limit; zero are truncation, let alone a hidden
front-end cut-off.** The explorer *reached* every one of these ops (exploration ran
to completion) and simply could not discharge it — a loop body it does not summarise
or an unsupported construct — leaving it soundly `Open`. And the truncation rule it
rests on is now pinned by a positive control (`truncated_exploration_reports_no_
memory_decision` in `csolver-symbolic`): under a forced 1-visit budget the report is
`{ truncated: true, ..default }` with *every* decision map empty, so a truncated
function can never report a memory op safe — it always falls to non-`PASS`.

So the corrected finding is the **opposite** of the parked claim: the front end is
now nearly complete, and the dominant driver of `UNKNOWN` at scale is **engine
analysis depth** — pointer provenance tracking (1822, ~189 functions) and loop /
unsupported-op memory evaluation (1437, ~63 functions). Both are real, prioritisable
engine capabilities, not parser chores; the parse tail (~32 functions, 9%) is rightly
the *least* of them.

### Splitting the largest bucket honestly (and catching a mislabel doing it)

Before committing M3 ("track provenance") to a direction, the 1822 provenance bucket
was split by *origin* — each `Prov::Unknown` now carries a diagnostic tag of why
provenance is absent (`POrigin` in `csolver-symbolic`, excluded from equality so it
changes no verdict). The motivating worry was the dangerous category: a raw pointer
from `slice::from_raw_parts`/`as_ptr`, where validity rests on the caller's `unsafe`
contract, not the language — flipping those to `PASS` by "tracking provenance" would
be the worst regression possible (the corpus's `slice_oob_from_raw` is the live proof
that category is real UB). The split:

```
   1550  scalar used as pointer        (a pointer operand that evaluated to a scalar)
    223  loaded value                  (no store→load provenance — the M3 core)
     41  uncontracted pointer param
      8  loop-havocked pointer
      0  opaque call result (raw ptr)  ← the feared from_raw_parts/as_ptr category
      0  int→ptr cast
```

Two findings, one of them only because the first label was wrong. The raw-pointer
and int→ptr categories — the ones that need careful assumption discipline — are
**empty in these twelve crates**: the `slice_oob_from_raw` hazard does not arise
here, so an M3 that recovers reference/load provenance cannot accidentally flip it.
And the dominant cause is **none of the three** anticipated sub-cases: it is "a
pointer operand that evaluated to a scalar" (a pointer carried as an integer address
the engine no longer sees as a pointer), spread across *every* crate including the
non-pointer-arithmetic ones (`itoa`, `hexf-parse`) — byte iteration is universal, and
its iterator/offset pointers are where this happens.

That number was almost reported as "path-merge over-approximation": the first cut
lumped six distinct opaque-pointer sites under one `Merge` origin, and `Merge` came
out dominant. Believing it would have pointed M3 at control-flow joins — the wrong
target. Splitting `Merge` into its six sites moved all 1550 to `scalar-used-as-
pointer`; the merge/join sites were near-zero. Same mistake as the `grep -A1`
phantom, one level deeper: *a coarse bucket is a hypothesis, not a measurement.*

The lesson is the project's own methodology turned on itself, now in three layers:
*the aggregation is part of the measurement, the residual string it aggregates is
part of the measurement, and so is the granularity at which that string is bucketed.*
An unverified count is not evidence of an empty bucket (the `grep -A1` phantom), an
unsplit residual is not evidence of a single cause (the "truncated" that was zero),
and a coarse origin is not evidence of a single origin (the `Merge` that was really
`scalar-as-pointer`). Each was caught the same way — feed a known input, check the
bucket, refuse to trust a "0", an "empty", or a dominant catch-all without it — which
is why the sweep gates on `selftest.sh` before printing a single number.

### Drilling `scalar-as-pointer` to its mechanism (the M3-defining number)

The question that decides M3's *nature* (a low-risk representation fix vs. a
capability needing assumption discipline) is: of the 1550 scalar-as-pointer, how much
is "provenance exists in the source, the IR lost the pointer *type*" (recoverable, no
new assumption) vs. "genuinely integer-derived" (bit-masking, pointer arithmetic over
raw integers — stays `UNKNOWN`)? Each `ScalarPtrCause` now records the proximate
defining instruction of the scalar (with `Use`-copy chains resolved to their source).
The split:

```
  1011  unresolved scalar copy / param / const   (Use-copies; representation)
   529  call/index result typed non-pointer       (Index::index → &T; recoverable)
    10  loaded scalar (store-load dependent)
     0  bit-mask of an address (alignment)        ← the ambiguous category
     0  integer arithmetic                        ← the ambiguous category
     0  ptr-to-int cast / pointer arithmetic
```

**The genuinely-ambiguous arithmetic categories are empty.** Not one of the 1550 is
a bit-masked or integer-arithmetic address; the 529 are `Index::index`/`index_mut`
returning `&T`/`&mut T` and internal direct calls (drilled to the callee: **none** are
`from_raw_parts`/`as_ptr` — the raw-pointer hazard stays absent one level into the
calls). But the 1011 `Use`-copies were still a dominant catch-all "rooted at a
param/const", so — once more — they were resolved one level finer.

### Resolving the 1011 copy-roots — and cross-checking the root against its source

Following each `Use`-copy chain to its root and classifying the root:

```
   995  rooted in `undef`               ← FRONT-END lowering gap, not engine
    16  rooted in an integer constant   ← genuinely ambiguous (stays UNKNOWN)
     0  rooted in a symbol / pointer / scalar param / null
```

The dominant root is **`Const::Undef`** — what the MIR lowering emits when it cannot
lower a pointer's computation. The *first* attempt to attribute it counted `undef`
emissions at the source and found `&stack_local` dominant (3124), and it was tempting
to conclude "model `&local` as a stack region — 995 of the bucket, ~55%." **A
cross-check refuted that**, and it is the cleanest example in this whole document of
why a coarse number must be split before it is trusted: emission counts and
obligation counts are *different units*. Re-emitting each candidate `undef` site as a
uniquely-named marker symbol and re-aggregating shows where the `undef` that actually
reaches a *dereferenced pointer obligation* comes from:

```
   506  operand_value: `(_local).0` of a by-value aggregate not in the checked-arith map
   477  operand_value: other by-value Copy/Move projection (the `_ =>` fallback)
    12  &stack_local   ← the entire stack-local contribution to the 995
```

So `&stack_local` accounts for **12 of the 995**, not 995. Its 3124 emissions flow
almost entirely into values that are never dereferenced. The real driver is
[`operand_value`](../crates/mir/src/lower.rs)'s by-value-aggregate fallbacks: a
by-value tuple/struct/fat-pointer field used as an address — e.g. the `ptr` half of a
by-value `&[T]` read as `(_slice).0` — falls through to `undef`. A `&stack_local →
stack region` fix (the natural read of the first number) would have addressed **12 of
995** and missed the lever almost entirely — the exact "build on the unmeasured
internal distribution of a dominant bucket" failure, avoided only by the cross-check.

Measured to the verified root, the priority order is: model by-value aggregate
pointer fields in `operand_value` (≈983, the 506 + 477) and preserve pointer typing
through `index`/call results (529) — both front-end fidelity, both sound-extensible
(the provenance exists in the source; the lowering discards it). The genuine engine
lever (store→load provenance) is 223; the ambiguous `Const::Int` remainder is 16 and
stays `UNKNOWN`; the raw-pointer hazard is 0 throughout (`slice_oob_from_raw`/`raw_add`
/`raw_sub` stay `UNKNOWN`, Miri-UB).

Five reframes in one investigation, each from refusing to trust a number until it was
split one level finer: the bucket was not empty (the `grep -A1` phantom), the residual
was not one cause (the "truncated" that was 0), the origin was not one origin
(`Merge`→scalar-as-pointer), the copy-root was not representation work but a front-end
`undef`, and the `undef` was not `&stack_local` (12) but by-value aggregate
projections (983). Each *believed* catch-all would have aimed the next build at the
wrong target — the last one off by a factor of 80×. Each was caught the same way:
feed a known input, split one level finer, refuse to trust a "0"/"empty"/dominant
bucket — *especially* one whose units you have not checked against the thing you are
about to dimension a fix on. *A coarse bucket is a hypothesis, not a measurement.*

### Probing the four M3 levers before building — none is a free representation fix

With the provenance bucket split to the root, the four candidate M3 levers were each
*probed* (wired experimentally and measured, or instrumented) before committing a
build, on the axis that matters: *additive* (recover provenance the IR already holds)
vs. *assumption-laden / reconstruction* (new trust surface). Every one turned out to
need real work:

- **call/index results (529).** Typing the call result correctly (its destination
  local's declared type, now that the parser captures `let _N: T;`) is sound and
  committed — but **precision-neutral**: it moves the 529 from "scalar-as-pointer" to
  "opaque call result", still `UNKNOWN`. Flipping them to `PASS` needs a *return
  summary* (`Index::index` returns an in-bounds pointer into arg 0, via its
  panic-on-OOB), a surfaced assumption of the `slice-abi` class — not free.
- **by-value aggregate `.0` (983).** Hypothesised as the additive lever (read back a
  fat pointer's data half from a contracted region). Wired experimentally: **0
  flipped.** Instrumented: all 2320 such locals are `MType::Other` — the parser
  collapses their aggregate types to opaque, so the provenance is *not in the IR* to
  read back; it must be reconstructed (aggregate-type modelling). Reverted.
- **store→load (223).** Recommended as the one genuinely-additive lever (a stored
  pointer's provenance is a *fact*). Instrumented: **806 of the pointer-typed
  fresh loads are `Unwritten`** (the location was never written in the analysed
  function), and **0** are the refinable `May`→`Must` case. The pointers come from
  *outside* — caller memory, fields initialised elsewhere — so this is an
  interprocedural / initial-heap gap, not a local alias refinement. The `Must` case
  already carries provenance; there is nothing local to sharpen.
- **`&stack_local` (12).** Tiny, and the only lever that introduces a new region with
  a scope-bound lifetime (a dangling-stack-reference false-`PASS` risk). Deferrable.

The measured conclusion is the opposite of the hope that opened this section: **there
is no free, TCB-neutral, additive *big* lever.** Every M3 entry point costs real
design — a surfaced summary assumption (call/index), front-end aggregate-type
modelling (by-value), or interprocedural memory provenance (store→load). That is a
*good* result to enter M3 with: the optimistic "provenance is already there, just
recover it" assumption was measured and buried before it became code, so M3 starts
with the correct expectation rather than one that shatters mid-build.
