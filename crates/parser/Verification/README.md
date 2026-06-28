# Verification — csolver-parser

## Design
Frontend-agnostic plumbing: a byte `Cursor` with O(1) lookahead and a
`Diagnostics` sink that emits `core::Error` with spans. No grammar.

## Specification
- `Cursor` never reads out of bounds (`peek`/`bump` return `Option`).
- `span_from(start)` yields `[start, current_offset)`.

## Assumptions
- Inputs are UTF-8; the textual IR/asm grammars are ASCII for token bytes.

## Limits
- Pure plumbing; correctness of any actual parse lives in the frontend crates.

## Proofs (arguments)
- Bounds safety is guaranteed by `slice::get` returning `Option`; there is no
  indexing that can panic on input.

## Test strategy
Unit tests for cursor walking/`take_while`/whitespace and diagnostic recording.
