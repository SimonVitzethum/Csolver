# Verification — csolver-asm

## Design
x86-64 (and later AArch64) → MSIR frontend. Registers, flags and the stack
pointer are explicit; DWARF (from `csolver-elf`) supplies frame layout.

The **machine-code decoder** (`x86::decode_function`) lowers an x86-64 function —
recovered from an ELF `.text` by `csolver-elf` — into MSIR, **reconstructing its
control-flow graph**, so the audited analysis core verifies a compiled binary with
no source. x86 registers become MSIR `RegId`s (the encoding number); a memory
operand `[base + disp]` (including a SIB byte and an 8/32-bit displacement) lowers
to a `PtrOffset` then a `Load`/`Store`. Currently decoded: the REX prefix,
`ret`/`nop`, `mov r,imm`, the reg/reg ALU ops (`xor`/`add`/`sub`/`and`/`or`, with
`xor r,r` recognised as zeroing), the group-1 `add`/`sub r, imm8`, `mov` reg↔reg /
`[base+disp]` load/store, `cmp`/`test`, and the branches `jmp`/`jcc`.

### Control flow
The body is decoded linearly, then split into basic blocks at the leaders — the
entry, every branch target, and the instruction after every branch/return.
`jmp`→`Br`, `ret`→`Return`, and `jcc`→`CondBr`. A `jcc`'s condition is taken from
the preceding `cmp`/`test` (the condition code maps `cmp a,b` to `a <op> b`: `je`→
`a==b`, `jl`→`a<ₛb`, `jb`→`a<ᵤb`, …); with no preceding compare or an unmodelled
code the condition is an unconstrained boolean, so the engine soundly explores
both arms. Backward branches become back-edges, which the symbolic engine already
handles (cut + interval invariant), so **binary loops** work. A branch target that
is not an instruction boundary (into the middle of an instruction, or data) makes
the function `unanalyzed` — never a guessed CFG. So a guarded stack store
(`cmp edi,0 ; jne .skip ; mov [rsp+8],eax`) verifies **PASS**, and a counting loop
is handled end-to-end.

### Stack frame model
`sub rsp, N` is recognised as **allocating the function's frame**: it lowers to an
`Alloc` of an `N`-byte `Stack` region with `rsp` as the pointer, so a subsequent
`[rsp + disp]` access (via a SIB byte) is checked against the frame — `disp +
size ≤ N` is in bounds. `add rsp, N` tears the frame down (a no-op for the
analysis, as nothing accesses it after). This is what lets a binary's stack store
be *proved* safe: `sub rsp,16 ; mov [rsp+8], eax` is `PASS`, while `mov [rsp+32]`
into the same frame is `FAIL` (a definite out-of-bounds write). It is a sound
over-approximation of the real `rsp` arithmetic for frame-local accesses (under
`alloc-succeeds`, i.e. no stack overflow).

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
