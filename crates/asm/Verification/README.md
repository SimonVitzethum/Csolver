# Verification — csolver-asm

## Design
x86-64 (and later AArch64) → MSIR frontend. Registers, flags and the stack
pointer are explicit; DWARF (from `csolver-elf`) supplies frame layout.

The **machine-code decoder** (`x86::decode_function`) lowers a straight-line
x86-64 function — recovered from an ELF `.text` by `csolver-elf` — into MSIR, so
the audited analysis core verifies a compiled binary with no source. x86 registers
become MSIR `RegId`s (the encoding number); a memory operand `[base]` becomes a
`Load`/`Store` through the base register (a flat-memory pointer). Currently
decoded: the REX prefix, `ret`/`nop`, `mov r,imm`, the reg/reg ALU ops
(`xor`/`add`/`sub`/`and`/`or`, with `xor r,r` recognised as zeroing), and
`mov` reg↔reg / simple `[base]` load/store.

## Soundness by graceful degradation
The decoded subset is intentionally tiny and **grows monotonically**: an
unrecognized opcode or addressing mode makes the *whole function* `unanalyzed`
(reported `UNKNOWN`), never a guessed or skipped instruction. A decoder that
silently mis-modelled or dropped an instruction could fabricate a false `PASS` —
the one outcome a verifier must never produce — so this layer can only be
incomplete, never unsound. End-to-end: a real ELF `xor eax,eax; ret` verifies
`PASS`; a raw-pointer store (`mov [rdi], rsi`) is `UNKNOWN` (no provenance for
`rdi`); a `syscall` is `UNKNOWN` (undecoded). See
`csolver-testsuite/tests/binary.rs`.

## Specification (target)
- Refinement: every concrete machine execution is a concrete MSIR execution.
- Memory operands lower to `PtrOffset` + `Load`/`Store` with the canonical
  checks, including `StackIntegrity`/`ValidStackFrame` around the frame.

## Assumptions
- The decoded semantics matches the target manual; indirect-branch targets
  outside the analyzable set yield `ValidIndirectTarget` obligations/assumptions.

## Limits
- M0 is interface-only (`lower` → `Unsupported`).
- Self-modifying code and unmodelled instructions become explicit assumptions.

## Proofs (arguments)
- Per-instruction semantics validated against a reference (differential testing
  vs an emulator) on a sample corpus.

## Test strategy
Planned: decode/lower unit tests per opcode class; differential execution tests
on small assembled snippets (M4).
