# Binary → MSIR: what a complete ELF analysis path would take

> An investigation + plan for turning the existing ELF/asm scaffolding into a
> pipeline that loads a compiled binary and lowers it to MSIR for verification.
> Grounded in the current code, not aspiration. Effort and line counts are honest
> estimates with their assumptions stated.

> **STATUS (2026-07): largely BUILT — this plan is now mostly historical.** The
> binary path is wired end-to-end (`solver verify <binary>` → `lower_elf`): the
> loader reads **ELF (incl. ELF32/BE) + PE/COFF + Mach-O** via `load_object`, with
> relocations, DWARF `.debug_info`/`.debug_line`, and container unpacking (ISO 9660
> incl. Rock Ridge/El Torito, WIM with XPRESS). The x86-64 decoder is far past the
> teaching subset (SSE/VEX, `call`/`push`/`pop`, RIP-relative, sub-registers, recursive
> descent, and an **unmodeled-instruction bridge** so unknown opcodes havoc opaquely
> instead of dropping the function). The **hand-written decoder semantics remain the
> top residual false-PASS risk** (see the scope banner in §2 / ROADMAP) — that caveat
> stands. The tables below reflect the *original* starting point, not today's code.

## 1. Current state (measured)

| Piece | State | Wired to CLI? |
|---|---|---|
| ELF loader (`crates/elf`, 386 LOC) | ELF64-LE: header, sections, **one** symtab, `function_code()`. Bounds-checked, tested. | **No** — CLI ELF path is a stub (`main.rs`: `unreachable!("stub always errors")`) |
| x86 decoder (`crates/asm/x86.rs`, 583 LOC) | ~30 opcodes: nop/ret/mov/ALU-reg-reg/lea/cmp/test/jmp/jcc/`sub rsp` frame. CFG reconstruction. | **No** — only reached from its own tests |
| arm64 decoder (`crates/asm/arm64.rs`, 293 LOC) | RET/B.cond/ADD-SUB-imm/LDR-STR-uoffset/cmp. | **No** |
| `AsmFrontend::lower` | **Stub** (`Unsupported`) | text `.s` path is dead |

**The pieces exist but nothing is connected** — the whole binary→MSIR path is
disconnected from the CLI today. And the decoder is a teaching subset: **no
`call`/`push`/`pop`, no RIP-relative addressing, no SSE/SIMD, no sub-register
aliasing (al/ax/eax/rax), no string ops, no real flags model** (only a
"last `cmp`/`test`" heuristic). Soundness holds by *graceful degradation*: any
unrecognized opcode marks the whole function `unanalyzed` → `UNKNOWN`. So the path
is never unsound, but on real binaries it is almost always `UNKNOWN` today.

## 2. The honest scope boundary

"Load any binary and convert it fully to MSIR" conflates two very different tasks:

1. **Load the ELF** (parse everything) — tractable.
2. **Fully recover MSIR from machine code** — this is reverse engineering at the
   level of angr / BAP / Ghidra. For *arbitrary* real binaries (stripped,
   dynamically linked, SIMD, jump tables) it is **multiple person-years and partly
   an open research problem**: function-boundary recovery in stripped binaries,
   indirect jumps (jump tables), and indirect calls are unsolved in general.

A realistic definition of "complete" for this project: **statically linked,
non-stripped, x86-64, integer code, with a faithful decoder + a real flags model +
ABI + relocations.** That is reachable. Everything past it (SIMD, stripped,
dynamic, indirect control flow) is incremental and partly research-grade, and the
graceful-degradation rule keeps every intermediate state sound.

## 3. The plan, in phases (with effort and where the debugging lives)

**Phase 0 — Wiring (1–2 days, low debugging).** ELF → `functions()` →
`decode_function` per symbol → one multi-function `Module` → verifier. Replace the
CLI ELF stub. Gives the end-to-end path immediately for the *current* (tiny)
decoder coverage. Low risk (glue).

**Phase 1 — x86-64 decoder completeness (DOMINANT, 4–8 weeks, heavy debugging).**
The mountain. Decision: **adopt the pure-Rust `yaxpeax-x86` disassembler** (offline-
capable; already listed in `ARCHITECTURE.md` as a planned external dep) rather than
writing decode from scratch (which adds ~2–3 months). yaxpeax solves *decoding*;
you still write the **soundness-critical semantic lowering** per instruction: full
ALU forms, mul/div/shift, push/pop/call/ret/leave, movzx/movsx, setcc/cmovcc,
RIP-relative, operand sizes + **sub-register aliasing**, and above all a **real
flags model** (CF/OF/SF/ZF) instead of the `cmp` heuristic. *Every instruction is a
potential false-`PASS` source* — this is the most expensive debugging item in the
whole idea.

**Phase 2 — A soundness oracle for the binary path (2–3 weeks, a sub-project).**
The `differential`/Miri pattern does **not** apply here — there is no Miri for
machine code. You need a **CPU-emulator oracle** (a pure-Rust x86 integer executor;
embedding QEMU/Unicorn would break the pure-Rust/offline rule) to differentially
validate decode→MSIR semantics. Without it, Phase 1 is not soundness-validatable.
This is the extra cost the machine-code path carries that the MIR path got for free
(Miri).

**Phase 3 — ELF loader completeness for real static binaries (3–5 weeks).**
Relocations (`.rela.*`) → resolve call targets / global accesses; **multi-function +
call graph**; `.rodata`/`.data`/`.bss` as memory regions with known contents;
program headers / segments (for the section-less view); ABI model (SysV args, `rax`
return, callee-saved). PLT/GOT + `.dynsym` for dynamically-linked: +weeks.
**Stripped binaries** (function-boundary recovery) + DWARF (via `gimli`, for
types / stack layout): +4–8 weeks, partly research-grade.

**Phase 4 — Control/data-flow recovery (open-ended).** Jump tables
(`switch` → `jmp [tbl + idx*8]`), indirect calls (vtables / function pointers),
function boundaries. This is where "complete" ends and research begins.

## 4. Line-count estimate (production + error-analysis), grounded

Baseline density measured in-repo: project test fraction **16%** inline
(test:prod ≈ 1:5), plus separate harnesses (`differential/` ~700, `scaling/` ~600).
For the binary path the validation fraction is **higher** because the emulator
oracle is a co-equal build, not free like Miri.

Two production scenarios: **(A) adopt `yaxpeax-x86` + `gimli`** vs **(B) decoder
from scratch**. New LOC on top of today's 1429 (elf+asm):

| Component | (A) adopt | (B) scratch |
|---|---:|---:|
| Phase 0 wiring + multi-fn module + call graph | 300 | 300 |
| x86 *decode* (integer ISA) | 0 (external) | 5000 |
| x86 *semantic lowering* → MSIR (ALU/mul/div/shift/push/pop/call/ret/str) | 2000 | 2000 |
| Real flags model (CF/OF/SF/ZF, per-op) | (≈400, incl. above) | (same) |
| Sub-register aliasing semantics | (≈200, incl. above) | (same) |
| ELF completeness (reloc, segments, .data/.rodata/.bss, .dynsym, PLT/GOT) | 1000 | 1000 |
| DWARF via `gimli` (integration glue) | 500 | 500 |
| ABI / calling convention / call graph | 400 | 400 |
| **Production subtotal (x86, no arm64, no stripped)** | **~4200** | **~9200** |

Error-analysis / validation LOC (what "eingerechnet Fehleranalyse" asks for):

| Item | LOC |
|---|---:|
| Inline unit tests (~1:4 on new prod — soundness-critical, denser than the 1:5 average) | 1000–1500 |
| **Emulator oracle** (pure-Rust x86 integer executor) | 1500–3000 |
| Binary differential harness (fuzz → emulator vs MSIR-symbolic, compare) | 600–1000 |
| Binary corpus + golden fixtures (real `.o`/ELF inputs, per-instruction) | 400–800 |
| **Validation subtotal** | **~3500–6300** |

**Totals (new LOC, error-analysis included):**

- **Minimal end-to-end** (Phase 0 + small decoder growth + basic tests): **~1000–1500**.
- **Realistic complete** (x86, static, non-stripped, integer; route A = yaxpeax+gimli):
  **~4200 production + ~4500 validation ≈ 8000–9000 LOC**, of which **~50% is
  test/oracle/debugging**.
- **From-scratch decoder** (route B): **~13000–15000 LOC**.
- **+ arm64 parity:** +~2500–5000.
- **+ stripped / dynamic / SIMD / jump tables:** open-ended (research) — each adds
  thousands and some have no general solution.

So: *complete ELF analysis for the realistic scope, error-analysis included, is on
the order of **8–9k new lines** (≈ double if the decoder is hand-written), roughly
half of it validation code.* "Truly any binary" is not a line-count question — it
is open-ended research.

## 5. Resources

- **External crates** (a policy call, but anticipated by `ARCHITECTURE.md`):
  `yaxpeax-x86`/`yaxpeax-arm` (disassembly, pure Rust ✓ offline), `gimli` (DWARF,
  pure Rust ✓). ELF parsing can stay in-house (it already exists). **A QEMU/Unicorn
  oracle would break the pure-Rust/offline rule** — the central open question; the
  pure-Rust emulator avoids it at the cost of writing it.
- **TCB / soundness:** each instruction's semantics *extends the trusted base*
  (unlike the graceful-degradation shell, which only ever loses precision). This is
  the qualitative difference from the MIR frontend, and why the oracle is not
  optional.

## 6. Recommendation

Do not attack "complete" head-on. **Phase 0 (wiring) + Phase 2 (the emulator oracle
first, in small)** lay the foundation on which the decoder can grow
*soundness-validated* — exactly the pattern this project has used elsewhere (build
the measurement/validation instrument before the capability). Then grow the decoder
incrementally via yaxpeax + the oracle, with graceful degradation as the safety net
so every intermediate state stays sound.
