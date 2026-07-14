//! A minimal x86-64 machine-code decoder → MSIR.
//!
//! It decodes a *small, growing* subset of x86-64 from raw bytes (as recovered
//! from an ELF `.text` by [`csolver_elf`]) and lowers a straight-line function to
//! MSIR, so the audited analysis core can verify a compiled binary with no
//! source. Registers are MSIR `RegId`s (the x86 encoding number), memory accesses
//! become `Load`/`Store` through the address register (a flat-memory pointer).
//!
//! ## Soundness by graceful degradation
//! The supported subset is intentionally tiny. Any unrecognized opcode or
//! addressing mode makes the *whole function* `unanalyzed` (reported `UNKNOWN` by
//! the verifier) rather than guessed at — a decoder that silently skipped or
//! mis-modelled an instruction could fabricate a false `PASS`, the one outcome a
//! verifier must never produce. So this layer can only ever be incomplete, never
//! unsound.

use crate::blocks::{build_blocks, Ctrl, DecodedInsn};
use csolver_core::{Error as CoreError, RegionKind};
use csolver_ir::{
    BinOp, Callee, CastOp, CmpOp, FuncId, Function, Inst, Module, Operand, RValue, RegId, Type,
};

/// Decode an x86-64 function from its machine bytes into a one-function
/// [`Module`], reconstructing its control-flow graph (branches/loops). On any
/// unsupported construct the function is recorded as `unanalyzed` (⇒ `UNKNOWN`),
/// never silently mis-modelled.
pub fn decode_function(name: &str, code: &[u8]) -> Module {
    // No relocations available (raw bytes): RIP-relative accesses resolve to nothing
    // and become opaque-global sentinels (the function still decodes).
    decode_function_reloc(name, code, &|_| None, &|_| None)
}

/// As [`decode_function`], with a **relocation resolver**: `resolve(disp_pos)` maps a
/// `disp32`'s function-relative byte position to `(global symbol, offset)` so a
/// RIP-relative / absolute access is checked against that global's region, and
/// `resolve_call(disp_pos)` maps a `call rel32`'s position to the callee's name so a
/// direct call to a contracted API is recognised (see [`CallResolver`]).
pub fn decode_function_reloc(
    name: &str,
    code: &[u8],
    resolve: RelocResolver,
    resolve_call: CallResolver,
) -> Module {
    let mut m = Module::new("bin");
    match decode_cfg(code, resolve, resolve_call).and_then(build_blocks) {
        Ok((blocks, entry)) => m.functions.push(Function {
            id: FuncId(0),
            name: name.into(),
            params: arg_registers(),
            ret_ty: Type::Unit,
            blocks,
            entry,
        }),
        Err(reason) => m.unanalyzed.push((name.into(), reason.to_string())),
    }
    m
}

/// The x86-64 System V integer argument registers, modelled as the function's
/// parameters so each is a *stable* symbol: a value read before it is written
/// (an input) then refers to one symbol across all its uses, which is what lets a
/// guard (`cmp rcx, 16`) constrain a later access (`[rsp + rcx*4]`). The order is
/// the SysV order (`rdi, rsi, rdx, rcx, r8, r9`), so the model names them
/// `arg0..arg5`.
pub(crate) fn arg_registers() -> Vec<(RegId, Type)> {
    [7u8, 6, 2, 1, 8, 9]
        .iter()
        .map(|&r| (reg(r), Type::int(64)))
        .collect()
}

/// The result of decoding one instruction (before block assembly).
struct Decoded {
    insts: Vec<Inst>,
    next: usize,
    ctrl: Ctrl,
}

/// **Recursive-descent** decode: decode only the bytes REACHABLE from the entry by
/// following control flow (fall-through + branch targets), not a blind linear sweep.
/// So trailing padding (`int3`/`nop`) after a function's `ret`, and other unreachable
/// bytes, are never decoded — they cannot drop the whole function on a bad opcode (the
/// bane of stripped images whose function sizes overshoot into padding).
///
/// `flags` (the last `cmp`/`test` operands) is threaded within each straight-line run
/// and reset at each run's start: a `cmp; jcc` pair is always in one run (adjacent), so
/// the condition stays exact; a block entered via a jump conservatively starts with no
/// flags (its `jcc`, if any, uses the unconstrained fallback — sound).
fn decode_cfg(
    code: &[u8],
    resolve: RelocResolver,
    resolve_call: CallResolver,
) -> csolver_core::Result<Vec<DecodedInsn>> {
    use std::collections::BTreeMap;
    let mut decoded: BTreeMap<usize, DecodedInsn> = BTreeMap::new();
    let mut work: Vec<usize> = vec![0];
    while let Some(start) = work.pop() {
        let mut pos = start;
        let mut flags: Option<(Operand, Operand)> = None;
        while pos < code.len() && !decoded.contains_key(&pos) {
            // Any decode failure — an unsupported opcode OR a sub-construct the precise
            // decoder declines (group-1 imm-to-memory, …) — falls back to the typed
            // decoder for the instruction length + a conservative havoc, so one unmodeled
            // instruction does not drop the whole (reachable) function.
            let d = match decode_one(code, pos, &mut flags, resolve, resolve_call) {
                Ok(d) => d,
                Err(e) => lower::bridge_unmodeled(code, pos, e)?,
            };
            let (next, ctrl) = (d.next, d.ctrl);
            decoded.insert(
                pos,
                DecodedInsn {
                    offset: pos,
                    next,
                    insts: d.insts,
                    ctrl,
                },
            );
            match ctrl {
                Ctrl::Ret => break,
                Ctrl::Jmp(t) => {
                    work.push(t);
                    break;
                }
                Ctrl::Jcc(t, _) => {
                    work.push(t);
                    pos = next;
                }
                Ctrl::Fall => pos = next,
            }
        }
    }
    Ok(decoded.into_values().collect())
}

pub(crate) fn reg(num: u8) -> RegId {
    RegId(num as u32)
}

// --- module split (mechanical refactor) ---
mod cond;
mod decode;
mod display;
mod lower;
mod opcode;
mod sse;
#[cfg(test)]
mod tests;
mod typed;
mod vex;
use cond::*;
pub use decode::*;
pub use typed::*;

use lower::*;
use opcode::*;
use sse::*;
use vex::*;

/// A decoded ModR/M byte (with REX register-number extensions applied).
struct ModRm {
    mode: u8,
    reg: u8,
    rm: u8,
}

/// A fresh MSIR register for the address computed by a memory operand. The byte
/// position is unique per instruction, so the temporaries never clash (and stay
/// clear of the x86 register numbers 0..15).
pub(crate) fn temp_reg(pos: usize) -> RegId {
    RegId(1000 + pos as u32)
}

/// `target = target <op> imm`.
fn add_imm(target: RegId, ty: Type, op: BinOp, imm: u128, width: u32) -> Inst {
    Inst::Assign {
        dst: target,
        ty,
        value: RValue::Bin {
            op,
            lhs: Operand::Reg(target),
            rhs: Operand::int(width, imm),
            flags: Default::default(),
        },
    }
}

/// The absolute byte offset a relative branch (`rel`, measured from `np`, the end
/// of the branch instruction) targets; an error if it falls before the function.
fn branch_target(np: usize, rel: i64) -> csolver_core::Result<usize> {
    let t = np as i64 + rel;
    if t < 0 {
        Err(CoreError::parse("x86: branch target before the function"))
    } else {
        Ok(t as usize)
    }
}

/// Lower a `jcc` to a condition assignment plus a `Jcc` control effect. With a
/// known `cmp`/`test` and a modelled condition code the condition is exact;
/// otherwise it is an unconstrained boolean (so the engine explores both arms).
fn jcc(
    pos: usize,
    np: usize,
    target: usize,
    cc: u8,
    flags: &Option<(Operand, Operand)>,
) -> csolver_core::Result<Decoded> {
    let cond = temp_reg(pos);
    let (op, lhs, rhs) = match (cc_cmpop(cc), flags) {
        (Some(op), Some((a, b))) => (op, a.clone(), b.clone()),
        // Unknown flags / condition code: compare a never-defined register with
        // 0, an unconstrained boolean.
        _ => (
            CmpOp::Ne,
            Operand::Reg(RegId(2000 + pos as u32)),
            Operand::int(64, 0),
        ),
    };
    Ok(Decoded {
        insts: vec![Inst::Assign {
            dst: cond,
            ty: Type::Bool,
            value: RValue::Cmp { op, lhs, rhs },
        }],
        next: np,
        ctrl: Ctrl::Jcc(target, cond),
    })
}

/// The comparison a condition code tests: `cmp a, b` then `jcc` jumps iff
/// `a <op> b`. `None` for codes we do not model (parity / sign / overflow).
pub(crate) fn cc_cmpop(cc: u8) -> Option<CmpOp> {
    Some(match cc {
        0x2 => CmpOp::Ult, // jb / jc
        0x3 => CmpOp::Uge, // jae / jnc
        0x4 => CmpOp::Eq,  // je / jz
        0x5 => CmpOp::Ne,  // jne / jnz
        0x6 => CmpOp::Ule, // jbe
        0x7 => CmpOp::Ugt, // ja
        0xc => CmpOp::Slt, // jl
        0xd => CmpOp::Sge, // jge
        0xe => CmpOp::Sle, // jle
        0xf => CmpOp::Sgt, // jg
        _ => return None,
    })
}

/// A decoded `[base + index*scale + disp]` memory operand.
pub(crate) struct MemOperand {
    pub(crate) base: RegId,
    /// `(index register, scale in bytes ∈ {1,2,4,8})`, if an index is present.
    pub(crate) index: Option<(RegId, u8)>,
    pub(crate) disp: i64,
    pub(crate) next: usize,
    /// A **global symbol base** instead of a register (a resolved RIP-relative
    /// access): the address is `@symbol + disp`. The executor resolves the symbol
    /// to the global's region (known size), so `[rip+disp]` is bounds-checked.
    pub(crate) symbol: Option<String>,
}

impl MemOperand {
    /// Emit the `PtrOffset` chain computing the address and return the register
    /// holding it: `base (+ index*scale) (+ disp)`.
    pub(crate) fn lower(&self, pos: usize) -> (Vec<Inst>, RegId) {
        let mut insts = Vec::new();
        // A resolved RIP-relative access uses the global symbol as its base (the
        // executor turns `@symbol` into that global's region); otherwise a register.
        let mut ptr = match &self.symbol {
            Some(name) => {
                let dst = RegId(3500 + pos as u32);
                insts.push(Inst::Assign {
                    dst,
                    ty: Type::ptr(Type::Unit),
                    value: RValue::Use(Operand::Const(csolver_ir::Const::Symbol(name.clone()))),
                });
                dst
            }
            None => self.base,
        };
        if let Some((index, scale)) = self.index {
            let dst = temp_reg(pos);
            insts.push(Inst::PtrOffset {
                dst,
                base: Operand::Reg(ptr),
                index: Operand::Reg(index),
                elem: Type::int(8 * scale as u32),
            });
            ptr = dst;
        }
        // A bare `[base]` or any displacement needs a final byte offset (also so
        // the result is a pointer when there was no index).
        if self.index.is_none() || self.disp != 0 {
            let dst = RegId(1500 + pos as u32);
            insts.push(Inst::PtrOffset {
                dst,
                base: Operand::Reg(ptr),
                index: Operand::int(64, self.disp as u64 as u128),
                elem: Type::int(8),
            });
            ptr = dst;
        }
        (insts, ptr)
    }
}

/// Maps the function-relative byte position of a `disp32` to the global it
/// addresses — `(symbol name, byte offset within the symbol)` — from the ELF
/// relocations. `None` when no relocation names it (then the access is modelled
/// through an opaque sentinel symbol, so the function still decodes).
pub type RelocResolver<'a> = &'a dyn Fn(usize) -> Option<(String, i64)>;

/// Maps the function-relative byte position of a `call rel32`'s `disp32` to the **name of
/// the called function symbol** — from the ELF/PLT relocation. Unlike [`RelocResolver`] this
/// returns even a size-0 *undefined* symbol (an imported `malloc`/`free`/`copy_from_user`),
/// because a call target is a function, not a sized data object. `None` when the target is
/// not statically named (an unrelocated / indirect call → an opaque call, as before). Lets
/// the binary path resolve a direct call's callee so the caller can match it against an API
/// contract (allocator / deallocator / user-copy), exactly as the LLVM front-end does.
pub type CallResolver<'a> = &'a dyn Fn(usize) -> Option<String>;

/// The SysV integer argument registers as MSIR operands, in ABI order
/// (`rdi, rsi, rdx, rcx, r8, r9`) — the actual arguments of a decoded `call`, so a
/// contract can read its size/pointer arguments (`arg0 = rdi`, …) off the call site.
pub(crate) fn arg_operands() -> Vec<Operand> {
    [7u8, 6, 2, 1, 8, 9].iter().map(|&r| Operand::Reg(reg(r))).collect()
}

/// Decode the `[base + index*scale + disp]` memory operand of a ModR/M
/// (mode ≠ 11), including a SIB byte. RIP-relative and base-less `disp32` forms
/// resolve to a **global symbol base** (via `resolve`) — an access to that
/// global's region — or an opaque sentinel symbol when unresolved (so the
/// function decodes rather than dropping).
fn mem_operand(
    code: &[u8],
    p: usize,
    m: &ModRm,
    rex_x: bool,
    rex_b: bool,
    resolve: RelocResolver,
) -> csolver_core::Result<MemOperand> {
    let mut p = p;
    let mut base = m.rm; // low 3 bits + REX.B (from `modrm`)
    let mut index = None;
    let rm_low = m.rm & 7;
    if rm_low == 4 {
        let sib = *code
            .get(p)
            .ok_or_else(|| CoreError::parse(format!("x86: truncated SIB at offset {p}")))?;
        p += 1;
        let scale = 1u8 << (sib >> 6);
        let index_field = (sib >> 3) & 7;
        let base_field = (sib & 7) + if rex_b { 8 } else { 0 };
        // index field 100 with REX.X clear means "no index"; otherwise it is a
        // register (r12 when REX.X is set).
        if index_field != 4 || rex_x {
            index = Some((reg(index_field + if rex_x { 8 } else { 0 }), scale));
        }
        if m.mode == 0b00 && base_field & 7 == 5 {
            // base-less disp32: an absolute / global base (optionally `+ index`).
            let (name, off) = resolve(p).unwrap_or_else(|| ("<abs-unknown>".to_string(), 0));
            return Ok(MemOperand {
                base: reg(0),
                index,
                disp: off,
                next: p + 4,
                symbol: Some(name),
            });
        }
        base = base_field;
    } else if rm_low == 5 && m.mode == 0b00 {
        // RIP-relative `[rip + disp32]` → a global.
        let (name, off) = resolve(p).unwrap_or_else(|| ("<rip-unknown>".to_string(), 0));
        return Ok(MemOperand {
            base: reg(0),
            index: None,
            disp: off,
            next: p + 4,
            symbol: Some(name),
        });
    }
    let disp = match m.mode {
        0b00 => 0i64,
        0b01 => {
            let d = read_imm(code, p, 1)? as u8 as i8 as i64;
            p += 1;
            d
        }
        0b10 => {
            let d = read_imm(code, p, 4)? as u32 as i32 as i64;
            p += 4;
            d
        }
        _ => {
            return Err(CoreError::unsupported(
                "x86: register operand has no memory form",
            ))
        }
    };
    Ok(MemOperand {
        base: reg(base),
        index,
        disp,
        next: p,
        symbol: None,
    })
}

fn modrm(code: &[u8], at: usize, rex_r: bool, rex_b: bool) -> csolver_core::Result<ModRm> {
    let b = *code
        .get(at)
        .ok_or_else(|| CoreError::parse(format!("x86: truncated ModR/M at offset {at}")))?;
    Ok(ModRm {
        mode: b >> 6,
        reg: ((b >> 3) & 7) + if rex_r { 8 } else { 0 },
        rm: (b & 7) + if rex_b { 8 } else { 0 },
    })
}

/// Read a little-endian immediate of `len` bytes (4 or 8), sign/zero handling
/// left to the consumer (we keep the raw unsigned value).
fn read_imm(code: &[u8], at: usize, len: usize) -> csolver_core::Result<u128> {
    let bytes = code.get(at..at + len).ok_or_else(|| {
        CoreError::parse(format!(
            "x86: truncated immediate of len {len} at offset {at}"
        ))
    })?;
    let mut v: u128 = 0;
    for (i, &byte) in bytes.iter().enumerate() {
        v |= (byte as u128) << (8 * i);
    }
    Ok(v)
}

// ============================================================================
// Typed instruction/operand representation (MSIR-independent)
// ============================================================================

/// x86-64 general-purpose registers (64-bit mode encoding).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(missing_docs)]
pub enum Reg {
    RAX = 0,
    RCX = 1,
    RDX = 2,
    RBX = 3,
    RSP = 4,
    RBP = 5,
    RSI = 6,
    RDI = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    R12 = 12,
    R13 = 13,
    R14 = 14,
    R15 = 15,
}
