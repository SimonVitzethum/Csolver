# Verification — csolver-report

## Design
Pure renderers from `ModuleReport` to text (`render_text`) and JSON
(`render_json`, hand-rolled, dependency-free).

## Specification
- Renderers are total functions of the report; they never alter a verdict.
- JSON output escapes control characters and is a single well-formed object.

## Assumptions
- The report it renders was produced by `csolver-verifier` (trusted input).

## Limits
- JSON schema is minimal (module/function/obligation verdicts + predicates);
  full proof-tree/counterexample serialization is planned (M2).

## Proofs (arguments)
- Rendering cannot affect soundness: it has no path that changes a `Verdict`.

## Test strategy
Unit tests assert the text mentions the verdict and proof justification, and the
JSON contains the expected keys/values. Golden-file tests planned (M1).
