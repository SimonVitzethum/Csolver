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
`[base + index*scale + disp]` load/store, `lea`, `cmp`/`test`, and the branches
`jmp`/`jcc`. **Indexed addressing** (a SIB index register with a 1/2/4/8 scale)
lowers to a `PtrOffset` by `index * scale` (then the displacement), so an array
access `[rsp + rcx*4]` is modelled exactly.

### Argument registers as parameters
The x86-64 System V integer argument registers (`rdi, rsi, rdx, rcx, r8, r9`) are
modelled as the function's **parameters**, so each is a *stable* symbol: a value
read before it is written (a function input) refers to one symbol across all its
uses. This is what lets a guard (`cmp rcx, 16`) constrain a later indexed access
(`[rsp + rcx*4]`) — without it, each use would be an independent unknown.

## AArch64
A second decoder (`arm64::decode_function`) handles **ARM64** binaries. AArch64
instructions are fixed 32-bit little-endian words decoded by field extraction (no
prefixes/ModR/M). Decoded: `ret`, `add`/`sub` immediate (with `sub sp, sp, #N`
modelling the stack frame exactly as on x86; the `S` bit disambiguates register
31 = `sp` from the zero register), `ldr`/`str` with an unsigned scaled offset
(`[base, #off]` → `PtrOffset` + `Load`/`Store`), `cmp` (`SUBS xzr`), and the
branches `b`/`b.cond`. The PCS argument registers `x0..x7` are the parameters.

**Control flow** is reconstructed by the *same* architecture-independent block
assembler the x86 decoder uses (`blocks::build_blocks`): both produce a linear
list of `(offset, MSIR, control effect)` and share the leader-finding and block
splitting. A `b.cond`'s condition comes from the preceding `cmp` (the AArch64
condition codes map to the same comparisons). So the same proofs hold on ARM and
extend to *branchy* ARM functions: `sub sp,sp,#16 ; str w0,[sp,#8] ; ret` is
**PASS**, `str w0,[sp,#32]` is **FAIL**, and a guarded store
(`cmp w0,#0 ; b.ne .skip ; str w1,[sp,#8]`) is **PASS**. Unrecognized encodings
make the function `unanalyzed` (never guessed). The broader ISA, register-offset
addressing, and `cbz`/`tbz` follow.

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
Decoding is **recursive descent**: only bytes reachable from the entry are decoded
(a worklist over `jmp`/`jcc` targets and fall-through), so trailing padding or data
between functions is never mis-decoded. An unrecognized **register-only, non-control-flow** opcode is
no longer fatal to the function — it is **bridged** to an opaque call + a general-purpose
register/flags havoc (`bridge_unmodeled`), a sound over-approximation, so a stripped or
padded binary is still analysed instead of dropped wholesale. A `call` is modelled as an
opaque call with fall-through. An unmodeled instruction that **touches memory** (an explicit
memory operand, or the implicit stack/string accesses — checked by an exhaustive
`touches_memory`) is **NOT** bridged: havocing registers would silently drop its memory access,
which could hide an unsafe load/store and yield a false PASS, so it declines the bridge and the
function drops to `UNKNOWN`. Only a genuinely undecodable / memory-touching shape leaves the
function `unanalyzed`.

**Automatic decoder validation.** The decoder's byte length — the property recursive descent
and the bridge both depend on — is differentially tested against **llvm-objdump** over ~1k real
instructions (`tests/x86_length_diff.rs`, corpus in `tests/data/`, regen via `regen.sh`): every
decoded instruction's length must equal the true length (a mismatch desyncs the stream), asserted
as **0 mismatches**. This directly de-risks the hand-written decoder — the project's highest
residual false-`PASS` surface. A decoder that silently *mis-modelled* an instruction
could fabricate a false `PASS` — the one outcome a verifier must never produce — so a
handled opcode is modelled exactly or bridged, never guessed. End-to-end: a real ELF `xor
eax,eax; ret` verifies `PASS`; a raw-pointer store (`mov [rdi], rsi`) is `UNKNOWN` (no
provenance for `rdi`). See `csolver-testsuite/tests/binary.rs`.

### The residual risk graceful degradation does *not* cover
Degradation protects against a *missing* instruction, not a *mis-modelled* one.
The semantics of every **handled** opcode is hand-written and **not yet validated**
against the hardware, and a subtly wrong rule produces a silent false `PASS`:

- partial-register writes — a 32-bit `mov eax, …` zeroes the upper 32 bits of
  `rax`, an 8/16-bit write does not;
- flag computation, sign- vs. zero-extension, one-past-the-end pointer rules.

This makes the decoders the **highest residual false-`PASS` risk in the project**.
Accordingly the binary/ASM track is **frozen as a research demonstrator** (see
`docs/ROADMAP.md`): it must not be relied on for safety-critical claims until its
per-instruction semantics are **translation-validated against a reference
emulator** (the "Proofs" item below) — the same measured discipline the bit-blaster
(exhaustive oracle test) and the verdict pipeline (Miri differential corpus)
already have.

## Specification (target)
- Refinement: every concrete machine execution is a concrete MSIR execution.
- Memory operands lower to `PtrOffset` + `Load`/`Store` with the canonical
  checks, including `StackIntegrity`/`ValidStackFrame` around the frame.

## Assumptions
- The decoded semantics matches the target manual; indirect-branch targets
  outside the analyzable set yield `ValidIndirectTarget` obligations/assumptions.

## Limits
- The **machine-code (byte) decoder** `x86::decode_function` / `arm64::decode_function`
  is functional (→ MSIR; ~197 x86 mnemonics incl. VEX/EVEX/ModRM/SIB, 147 tests). The
  **textual-assembly** frontend `AsmFrontend::lower` (source `.s` / GCC inline-asm
  templates → MSIR) is **still a stub** (`Unsupported`, planned M4). So a C inline-asm
  block (`Inst::Asm`) is currently treated as an **opaque havoc** by the executor —
  modelling its side effects needs the text parser + a template→effect mapping, which
  could reuse the byte decoder's per-mnemonic MSIR lowering.
- Self-modifying code and unmodelled instructions become explicit assumptions.

## Proofs (arguments)
- Per-instruction semantics validated against a reference (differential testing
  vs an emulator) on a sample corpus.

## Test strategy
Planned: decode/lower unit tests per opcode class; differential execution tests
on small assembled snippets (M4).
