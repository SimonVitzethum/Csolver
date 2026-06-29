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

## Acting on it: two parser fixes, 2.5× the PASS rate

The measurement paid for itself immediately. Two small, *low-TCB-risk* front-end
fixes — robust type parsing (qualified paths, generics, `<T as Trait>::Assoc`,
const-generic array lengths → opaque) and impl-method headers (`fn <impl at …>::m`)
— lifted the whole sweep:

```
before:  126 PASS    0 FAIL    513 UNKNOWN   (20%)
after:   321 PASS    0 FAIL    305 UNKNOWN   (51%)
```

`smallvec` alone went 1 → 108 PASS. Parsing more real MIR cannot, by itself, turn a
bug into a PASS — it only feeds more obligations to the same trusted core, as long
as each fix *consumes* its construct rather than silently dropping a memory
operation. The differential corpus stayed at **0 soundness violations** throughout,
which is what proves that.

The next gap is now precisely characterised (and still pure parser robustness, not
the engine): **~173 `expected a local, found <ident>`** — paths in operand/place
position (path constants, enum-variant construction). The analysis core is still
not the bottleneck — the per-obligation residual bucket remains empty.

## Caveats

- Generic functions are emitted as polymorphic MIR (type parameter `T` → an opaque
  aggregate), so a generic data-structure crate is a *lower* bound on what the
  analysis could prove on a monomorphised instance.
- `solver verify` is run per crate with a timeout; a crate that produces no
  per-function output (e.g. `base64` here) is a separate front-end issue to chase,
  not a 0% result.
- The crate set and versions depend on what the cargo cache happens to hold; the
  numbers are indicative, not a fixed benchmark.
