# From provable-correct to human-usable — the validation/usability readiness

> A verifier that reports a `FAIL` at "instruction #7" and makes the user emit MIR
> by hand is correct and unused. This document maps the bridge from the soundness
> machinery (built over the preceding milestones) to a tool a person can run, and
> fixes the order of work as a *documented* decision — sorted not by value/effort
> but by **how much each axis touches the soundness-critical paths**, because the
> "usability" framing makes it easy to forget that two of three axes do.

## The shift

The question moved from "is it correct, and how do I know?" to "is it *usable*?".
That is a maturity signal — but the discipline that carried the proof layers must
not be diluted by the convenience layer. **A tool that runs turnkey must say what it
did *not* check at least as loudly as one fed by hand — louder, because the turnkey
user looks less.**

## Current state (measured)

| Axis | State today |
|---|---|
| **1. Efficient checking** | Serial `verify_module` loop; ~200–700 fns/s (debug) on most crates, outlier **nom 33 fns/s** (37.5 s / 1252 fns). Per-solve cost bounded (`DEFAULT_BUDGET=200k`, 250 ms wall-clock valve, `max_visits` truncation, `CONSTRAINT_LIMIT=4096`). **No parallelism** (a shared mutable `next_id` couples functions), **no verdict cache**. |
| **2. Show errors *where*** | A `FAIL` reports function + **MSIR instruction index** (`@ mir:fn#N`) + property + predicate + a concrete counterexample witness (`name→value`, e.g. `arg0=5`). `Location` *has* a `span: Option<Span>` field — but it is **never populated**: the MIR parser *skips* the `// … at src/lib.rs:L:C` span comments. No source file:line, no user variable names. |
| **3. Check arbitrary Rust** | The user must run `rustc --emit=mir` / cargo themselves and pass the `.mir`; the CLI "crate dir → Mir" branch is broken (`read_to_string` on a directory). Parser robustness ≈ 92 % over 12 crates; the rest are frontend parse-tails + the provenance `UNKNOWN`s. ELF later (see `ELF-BINARY-PLAN.md`). |

## The three axes, sorted by soundness-touch

### Axis 2 — source location: purely additive, soundness-neutral (start here)

Parse the spans, thread them through lowering, render `file:line:col`. This changes
**no verdict** — a `FAIL` stays a `FAIL`, a `PASS` stays a `PASS`; only a provenance
annotation is attached. No "don't-know → know" step, no new trust surface, no
assumption. The rare work that is high-value *and* zero soundness-risk: a
counterexample witness nobody can locate in their source is half wasted. Bonus:
capture the MIR debug-info (`debug x => _1`) so the witness reads `x = 5`, not
`arg0 = 5`. **~250–400 LOC.**

*Test discipline:* pin not merely that *a* line renders, but the *right* one — a
fixture with two memory accesses on different source lines, the `FAIL` on exactly
one, asserting the rendered line is the faulty access's, not the safe one. Otherwise
the test is green whenever *any* line appears — the span equivalent of the `grep -A1`
phantom: a label that looks right without being checked.

### Axis 3 — turnkey: a hidden coverage-completeness trap

"`solver verify ./crate` shells out to cargo/rustc" sounds like pure convenience. It
is not. **The moment the tool drives MIR emission, it owns emission *completeness*.**
If cargo emits MIR for 80 of 100 functions (inlining, a monomorphisation gap, a
feature gate, a partial build error) and the missing 20 silently drop, the user
reads "all checked functions PASS" and concludes "my crate is safe" — while a fifth
was never looked at. That is a false *impression of coverage*, as dangerous as a
false `PASS`, one level up. On the scaling side this class was already seen: base64
emitted 0 functions and *silently vanished upward out of the metric*.

So the turnkey pipeline **must** report, at crate level, the same never-silently-skip
discipline the MSIR layer enforces per function (per-function recovery, the
`unanalyzed` list): **"N functions found, M verified, K not emitted / not analyzed —
here is the list."** Without it, the convenience layer undermines exactly the honesty
the inner layers build. **~150–250 LOC** + the coverage report.

### Axis 1 — efficiency: mechanical, but two parts touch soundness

- **Per-function time-budget bail** (the nom outliers): tiny (~50 LOC),
  soundness-*positive* — turns a class of quasi-hangs into clean `UNKNOWN`. But it
  bails at a coarser grain than the solve valve (a whole function, more obligations
  potentially open), so it needs the same check the wall-clock valve got: prove the
  bail path falls to **non-`PASS`**, never leaving a half-analysed function as `PASS`.
- **Parallelism** (decouple the shared `next_id` into per-function id ranges, then
  rayon/threads): the right barrier — but ids are not just counters, they are the
  identity of symbols and regions in the solver. Per-function id ranges could
  interfere with `ExprCtx` hash-consing or the region table in a way that never arose
  serially. It needs a **determinism test**: the same corpus, serial vs parallel,
  **identical verdicts *and* witnesses, bit-for-bit**. A divergence is an isolation
  leak — the kind that appears under load/timing and hides in tests. The determinism
  test is the *oracle* for parallelisation, the same role Miri plays for MIR and the
  emulator for asm. **~150–300 LOC** + the test.
- **Verdict cache** (by MSIR-function hash + config): deliberately last, not only for
  effort. A *wrong* cache hit (hash collision, or a config change not folded into the
  key) returns a stale `PASS` where the edited code is `FAIL`. It needs the same
  positive control as the aggregation fix: a test proving a *changed* function does
  **not** pull the old verdict from the cache. **~200 LOC** + the test.

## Decided order (documented, not to be re-litigated)

1. **✓ Axis 2 — source spans** (additive, soundness-neutral) — done, with the
   right-line test; witness values rendered; `arg{i}`→name renaming deferred (low ROI).
2. **✓ Per-function time-budget bail** — done, but *measurement redirected it*: the
   nom outliers (`permutation`, up to 5.8 s debug / ~2 s release) that "feel like a
   hang" are not hangs — they verify to `PASS`. A tight budget would convert real
   `PASS`es to `UNKNOWN` (precision loss), so the default is generous (30 s): a pure
   *termination guarantee* for the turnkey path, not a speed knob. The perceived-speed
   lever is the release build (nom 37.5 s → 12.9 s). Soundness pinned
   (`time_budget_bail_reports_no_memory_decision`).
3. **✓ Axis 3 — turnkey (`.rs` file), with a coverage report** — done. `solver verify
   foo.rs` compiles to MIR itself (`+nightly -Z mir-include-spans`, stable fallback)
   and reports *found / analyzed (PASS/FAIL/UNKNOWN) / not-analyzed (named)*, warns on
   0 functions, and surfaces a compile error rather than a verdict. The
   coverage-completeness trap is guarded: a not-lowered function is named, never
   folded into a flattering count. **Follow-up:** a whole crate *directory* (cargo
   orchestration over dependencies/workspace, picking the crate's own MIR).
4. **Parallelism** — with the serial-vs-parallel determinism test.
5. **Verdict cache** — last, with the changed-function positive control.

## Why this is not "just usability"

This is the bridge from "provably correct" to "usable by humans" — the transition at
which most verification projects *fail*: not because the theory is wrong, but because
a correct tool that reports `FAIL` at "instruction #7" and offloads MIR emission onto
the user is simply not used. Axes 2 and 3 are the condition for the soundness work to
reach anyone at all. The one discipline to hold: the convenience layer must not
dilute the honesty of the proof layer.
