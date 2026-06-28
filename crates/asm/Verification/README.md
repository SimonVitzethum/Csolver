# Verification — csolver-asm

## Design
x86-64 (Intel/AT&T) and AArch64 → MSIR frontend (M4). Registers, flags and the
stack pointer are explicit; DWARF (from `csolver-elf`) supplies frame layout.

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
