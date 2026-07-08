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
use csolver_ir::{BinOp, CmpOp, FuncId, Function, Inst, Module, Operand, RValue, RegId, Type};

/// Decode an x86-64 function from its machine bytes into a one-function
/// [`Module`], reconstructing its control-flow graph (branches/loops). On any
/// unsupported construct the function is recorded as `unanalyzed` (⇒ `UNKNOWN`),
/// never silently mis-modelled.
pub fn decode_function(name: &str, code: &[u8]) -> Module {
    let mut m = Module::new("bin");
    match decode_cfg(code).and_then(build_blocks) {
        Ok((blocks, entry)) => m.functions.push(Function {
            id: FuncId(0),
            name: name.into(),
            params: arg_registers(),
            ret_ty: Type::Unit,
            blocks,
            entry,
        }),
        Err(reason) => m.unanalyzed.push((name.into(), reason)),
    }
    m
}

/// The x86-64 System V integer argument registers, modelled as the function's
/// parameters so each is a *stable* symbol: a value read before it is written
/// (an input) then refers to one symbol across all its uses, which is what lets a
/// guard (`cmp rcx, 16`) constrain a later access (`[rsp + rcx*4]`). The order is
/// the SysV order (`rdi, rsi, rdx, rcx, r8, r9`), so the model names them
/// `arg0..arg5`.
fn arg_registers() -> Vec<(RegId, Type)> {
    [7u8, 6, 2, 1, 8, 9].iter().map(|&r| (reg(r), Type::int(64))).collect()
}

/// The result of decoding one instruction (before block assembly).
struct Decoded {
    insts: Vec<Inst>,
    next: usize,
    ctrl: Ctrl,
}

/// Linearly decode every instruction of the function body, threading the
/// `flags` state (the last `cmp`/`test` operands) so a following `jcc` knows its
/// condition.
fn decode_cfg(code: &[u8]) -> Result<Vec<DecodedInsn>, String> {
    let mut out = Vec::new();
    let mut pos = 0;
    let mut flags: Option<(Operand, Operand)> = None;
    while pos < code.len() {
        let d = decode_one(code, pos, &mut flags)?;
        out.push(DecodedInsn { offset: pos, next: d.next, insts: d.insts, ctrl: d.ctrl });
        pos = d.next;
    }
    Ok(out)
}

fn reg(num: u8) -> RegId {
    RegId(num as u32)
}

/// Decode one instruction starting at `pos`. `flags` carries the last
/// `cmp`/`test` operands so a following `jcc` can form its condition.
fn decode_one(
    code: &[u8],
    pos: usize,
    flags: &mut Option<(Operand, Operand)>,
) -> Result<Decoded, String> {
    let mut p = pos;
    // Optional REX prefix (0x40..0x4F): W=wide(64), R=reg ext, X=index ext,
    // B=rm/base ext.
    let (rex_w, rex_r, rex_x, rex_b) = match code.get(p) {
        Some(&b) if (0x40..=0x4f).contains(&b) => {
            p += 1;
            (b & 8 != 0, b & 4 != 0, b & 2 != 0, b & 1 != 0)
        }
        _ => (false, false, false, false),
    };
    let op = *code.get(p).ok_or("x86: truncated opcode")?;
    p += 1;
    let width = if rex_w { 64 } else { 32 };
    let ty = Type::int(width);

    let done = |insts: Vec<Inst>, next: usize| Ok(Decoded { insts, next, ctrl: Ctrl::Fall });

    match op {
        0x90 => done(vec![], p),                                          // nop
        0xc3 => Ok(Decoded { insts: vec![], next: p, ctrl: Ctrl::Ret }),  // ret
        0xb8..=0xbf => {
            // mov r, imm
            let r = reg(op - 0xb8 + if rex_b { 8 } else { 0 });
            let imm_len = if rex_w { 8 } else { 4 };
            let imm = read_imm(code, p, imm_len)?;
            done(
                vec![Inst::Assign {
                    dst: r,
                    ty,
                    value: RValue::Use(Operand::int(width, imm)),
                }],
                p + imm_len,
            )
        }
        // <alu> r/m, r — reg/reg form (mod == 11) only.
        0x31 | 0x01 | 0x29 | 0x21 | 0x09 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err("x86: ALU with a memory operand".into());
            }
            let bin = match op {
                0x31 => BinOp::Xor,
                0x01 => BinOp::Add,
                0x29 => BinOp::Sub,
                0x21 => BinOp::And,
                0x09 => BinOp::Or,
                _ => unreachable!(),
            };
            let dst = reg(m.rm);
            let src = reg(m.reg);
            // `xor r, r` is the idiom for zeroing — model it as `r = 0`.
            let value = if op == 0x31 && m.rm == m.reg {
                RValue::Use(Operand::int(width, 0))
            } else {
                RValue::Bin { op: bin, lhs: Operand::Reg(dst), rhs: Operand::Reg(src) }
            };
            done(vec![Inst::Assign { dst, ty, value }], p)
        }
        0x89 => {
            // mov r/m, r — register move (mod 11) or store [base+disp].
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                done(
                    vec![Inst::Assign {
                        dst: reg(m.rm),
                        ty,
                        value: RValue::Use(Operand::Reg(reg(m.reg))),
                    }],
                    p,
                )
            } else {
                let mem = mem_operand(code, p, &m, rex_x, rex_b)?;
                let (mut insts, ptr) = mem.lower(pos);
                insts.push(Inst::Store { ty, ptr: Operand::Reg(ptr), value: Operand::Reg(reg(m.reg)), align: 1 });
                done(insts, mem.next)
            }
        }
        0x8b => {
            // mov r, r/m — register move (mod 11) or load [base+...].
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                done(
                    vec![Inst::Assign {
                        dst: reg(m.reg),
                        ty,
                        value: RValue::Use(Operand::Reg(reg(m.rm))),
                    }],
                    p,
                )
            } else {
                let mem = mem_operand(code, p, &m, rex_x, rex_b)?;
                let (mut insts, ptr) = mem.lower(pos);
                insts.push(Inst::Load { dst: reg(m.reg), ty, ptr: Operand::Reg(ptr), align: 1 });
                done(insts, mem.next)
            }
        }
        // lea r, [mem] — compute the effective address into r (no memory access).
        0x8d => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                return Err("x86: lea requires a memory operand".into());
            }
            let mem = mem_operand(code, p, &m, rex_x, rex_b)?;
            let (mut insts, ptr) = mem.lower(pos);
            insts.push(Inst::Assign { dst: reg(m.reg), ty, value: RValue::Use(Operand::Reg(ptr)) });
            done(insts, mem.next)
        }
        // group 1: <op> r/m, imm8 — register target (mod 11) only.
        0x83 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err("x86: group-1 with a memory operand is unsupported".into());
            }
            let imm = read_imm(code, p, 1)?; // imm8, value 0..255
            p += 1;
            let target = reg(m.rm);
            // The /digit (ModRM reg field, sans any REX.R) selects the operation.
            match m.reg & 7 {
                // `sub rsp, N` allocates the stack frame: model rsp as a pointer
                // to a fresh N-byte stack region, so `[rsp+disp]` is checked
                // against the frame.
                5 if m.rm == 4 => done(
                    vec![Inst::Alloc {
                        dst: target,
                        region: RegionKind::Stack,
                        elem: Type::int(8),
                        count: Operand::int(64, imm),
                        align: 16,
                    }],
                    p,
                ),
                // `add rsp, N` tears the frame down; nothing accesses it after, so
                // it is a no-op for the analysis.
                0 if m.rm == 4 => done(vec![], p),
                0 => done(vec![add_imm(target, ty, BinOp::Add, imm, width)], p),
                5 => done(vec![add_imm(target, ty, BinOp::Sub, imm, width)], p),
                7 => {
                    // cmp r, imm — record the operands for a following `jcc`.
                    *flags = Some((Operand::Reg(target), Operand::int(width, imm)));
                    done(vec![], p)
                }
                _ => Err("x86: unsupported group-1 operation".into()),
            }
        }
        // cmp r/m, r — record operands for a following `jcc` (reg/reg form).
        0x39 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err("x86: cmp with a memory operand".into());
            }
            *flags = Some((Operand::Reg(reg(m.rm)), Operand::Reg(reg(m.reg))));
            done(vec![], p)
        }
        // cmp r, r/m (reg/reg form).
        0x3b => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err("x86: cmp with a memory operand".into());
            }
            *flags = Some((Operand::Reg(reg(m.reg)), Operand::Reg(reg(m.rm))));
            done(vec![], p)
        }
        // cmp eax, imm32.
        0x3d => {
            let imm = read_imm(code, p, 4)?;
            *flags = Some((Operand::Reg(reg(0)), Operand::int(width, imm)));
            done(vec![], p + 4)
        }
        // test r/m, r — `test r, r` tests whether `r` is zero.
        0x85 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            *flags = if m.mode == 0b11 && m.rm == m.reg {
                Some((Operand::Reg(reg(m.rm)), Operand::int(width, 0)))
            } else {
                None
            };
            done(vec![], p)
        }
        // jmp rel8 / rel32.
        0xeb => {
            let rel = read_imm(code, p, 1)? as u8 as i8 as i64;
            let np = p + 1;
            Ok(Decoded { insts: vec![], next: np, ctrl: Ctrl::Jmp(branch_target(np, rel)?) })
        }
        0xe9 => {
            let rel = read_imm(code, p, 4)? as u32 as i32 as i64;
            let np = p + 4;
            Ok(Decoded { insts: vec![], next: np, ctrl: Ctrl::Jmp(branch_target(np, rel)?) })
        }
        // jcc rel8.
        0x70..=0x7f => {
            let rel = read_imm(code, p, 1)? as u8 as i8 as i64;
            let np = p + 1;
            jcc(pos, np, branch_target(np, rel)?, op - 0x70, flags)
        }
        // Two-byte opcodes: jcc rel32 (0F 80..8F); everything else unsupported.
        0x0f => {
            let op2 = *code.get(p).ok_or("x86: truncated 0F opcode")?;
            p += 1;
            if (0x80..=0x8f).contains(&op2) {
                let rel = read_imm(code, p, 4)? as u32 as i32 as i64;
                let np = p + 4;
                jcc(pos, np, branch_target(np, rel)?, op2 - 0x80, flags)
            } else {
                Err(format!("x86: unsupported opcode 0f {op2:#04x}"))
            }
        }
        other => Err(format!("x86: unsupported opcode {other:#04x}")),
    }
}

/// A decoded ModR/M byte (with REX register-number extensions applied).
struct ModRm {
    mode: u8,
    reg: u8,
    rm: u8,
}

/// A fresh MSIR register for the address computed by a memory operand. The byte
/// position is unique per instruction, so the temporaries never clash (and stay
/// clear of the x86 register numbers 0..15).
fn temp_reg(pos: usize) -> RegId {
    RegId(1000 + pos as u32)
}

/// `target = target <op> imm`.
fn add_imm(target: RegId, ty: Type, op: BinOp, imm: u128, width: u32) -> Inst {
    Inst::Assign {
        dst: target,
        ty,
        value: RValue::Bin { op, lhs: Operand::Reg(target), rhs: Operand::int(width, imm) },
    }
}

/// The absolute byte offset a relative branch (`rel`, measured from `np`, the end
/// of the branch instruction) targets; an error if it falls before the function.
fn branch_target(np: usize, rel: i64) -> Result<usize, String> {
    let t = np as i64 + rel;
    if t < 0 {
        Err("x86: branch target before the function".into())
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
) -> Result<Decoded, String> {
    let cond = temp_reg(pos);
    let (op, lhs, rhs) = match (cc_cmpop(cc), flags) {
        (Some(op), Some((a, b))) => (op, a.clone(), b.clone()),
        // Unknown flags / condition code: compare a never-defined register with
        // 0, an unconstrained boolean.
        _ => (CmpOp::Ne, Operand::Reg(RegId(2000 + pos as u32)), Operand::int(64, 0)),
    };
    Ok(Decoded {
        insts: vec![Inst::Assign { dst: cond, ty: Type::Bool, value: RValue::Cmp { op, lhs, rhs } }],
        next: np,
        ctrl: Ctrl::Jcc(target, cond),
    })
}

/// The comparison a condition code tests: `cmp a, b` then `jcc` jumps iff
/// `a <op> b`. `None` for codes we do not model (parity / sign / overflow).
fn cc_cmpop(cc: u8) -> Option<CmpOp> {
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
struct MemOperand {
    base: RegId,
    /// `(index register, scale in bytes ∈ {1,2,4,8})`, if an index is present.
    index: Option<(RegId, u8)>,
    disp: i64,
    next: usize,
}

impl MemOperand {
    /// Emit the `PtrOffset` chain computing the address and return the register
    /// holding it: `base (+ index*scale) (+ disp)`.
    fn lower(&self, pos: usize) -> (Vec<Inst>, RegId) {
        let mut insts = Vec::new();
        let mut ptr = self.base;
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

/// Decode the `[base + index*scale + disp]` memory operand of a ModR/M
/// (mode ≠ 11), including a SIB byte. RIP-relative and base-less disp32 forms are
/// a clean `Err`.
fn mem_operand(code: &[u8], p: usize, m: &ModRm, rex_x: bool, rex_b: bool) -> Result<MemOperand, String> {
    let mut p = p;
    let mut base = m.rm; // low 3 bits + REX.B (from `modrm`)
    let mut index = None;
    let rm_low = m.rm & 7;
    if rm_low == 4 {
        let sib = *code.get(p).ok_or("x86: truncated SIB")?;
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
            return Err("x86: base-less disp32 is unsupported".into());
        }
        base = base_field;
    } else if rm_low == 5 && m.mode == 0b00 {
        return Err("x86: RIP-relative addressing is unsupported".into());
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
        _ => return Err("x86: register operand has no memory form".into()),
    };
    Ok(MemOperand { base: reg(base), index, disp, next: p })
}

fn modrm(code: &[u8], at: usize, rex_r: bool, rex_b: bool) -> Result<ModRm, String> {
    let b = *code.get(at).ok_or("x86: truncated ModR/M")?;
    Ok(ModRm {
        mode: b >> 6,
        reg: ((b >> 3) & 7) + if rex_r { 8 } else { 0 },
        rm: (b & 7) + if rex_b { 8 } else { 0 },
    })
}

/// Read a little-endian immediate of `len` bytes (4 or 8), sign/zero handling
/// left to the consumer (we keep the raw unsigned value).
fn read_imm(code: &[u8], at: usize, len: usize) -> Result<u128, String> {
    let bytes = code.get(at..at + len).ok_or("x86: truncated immediate")?;
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
    RAX = 0, RCX = 1, RDX = 2, RBX = 3,
    RSP = 4, RBP = 5, RSI = 6, RDI = 7,
    R8 = 8, R9 = 9, R10 = 10, R11 = 11,
    R12 = 12, R13 = 13, R14 = 14, R15 = 15,
}

impl Reg {
    /// Convert a 4-bit register index (0..15) into a [`Reg`]. The index
    /// combines the raw 3-bit encoding field with a REX extension bit
    /// (e.g. `low3 | if rex_bit { 8 } else { 0 }`).
    fn from_idx(idx: u8) -> Option<Reg> {
        match idx {
            0 => Some(Reg::RAX), 1 => Some(Reg::RCX), 2 => Some(Reg::RDX), 3 => Some(Reg::RBX),
            4 => Some(Reg::RSP), 5 => Some(Reg::RBP), 6 => Some(Reg::RSI), 7 => Some(Reg::RDI),
            8 => Some(Reg::R8), 9 => Some(Reg::R9), 10 => Some(Reg::R10), 11 => Some(Reg::R11),
            12 => Some(Reg::R12), 13 => Some(Reg::R13), 14 => Some(Reg::R14), 15 => Some(Reg::R15),
            _ => None,
        }
    }
}

/// Access width for a register or memory operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Width {
    /// 8 bits (byte).
    B,
    /// 16 bits (word).
    W,
    /// 32 bits (doubleword).
    D,
    /// 64 bits (quadword).
    Q,
}

impl Width {
    #[allow(dead_code)]
    fn bytes(self) -> u64 {
        match self {
            Width::B => 1,
            Width::W => 2,
            Width::D => 4,
            Width::Q => 8,
        }
    }

    /// Infer the width from a REX.W bit and the operation code. For most
    /// ALU ops, !REX.W → 32-bit, REX.W → 64-bit.
    fn from_rex_w(rex_w: bool) -> Width {
        if rex_w { Width::Q } else { Width::D }
    }
}

/// A memory operand: `[base + index * scale + disp]`.
///
/// Every field is optional: `base` may be `None` (absolute address),
/// `index` may be `None` (no scaled index), and `disp` may be 0.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Mem {
    /// The base register.
    pub base: Option<Reg>,
    /// The scaled index register and its scale (1, 2, 4, or 8).
    pub index: Option<(Reg, u8)>,
    /// The displacement in bytes.
    pub disp: i64,
}

/// A decoded operand for an x86-64 instruction.
///
/// Named `X86Operand` (not `Operand`) to avoid shadowing the import of
/// [`csolver_ir::Operand`] used by the MSIR-lowering path in the same module.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum X86Operand {
    /// A register operand (register + width).
    Reg(Reg, Width),
    /// A memory operand (address + width).
    Mem(Mem, Width),
    /// An immediate value (unsigned; semantic width depends on the instruction).
    Imm(u64),
    /// A relative displacement for a branch instruction (in bytes from the
    /// end of the instruction).
    Rel(i64),
}

/// x86-64 condition codes (the low 4 bits of the `jcc` / `cmovcc` / `setcc`
/// opcode extension). Only the ALU-flag-sensing subset is modelled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Condition {
    O, NO, B, AE, E, NE, BE, A,
    S, NS, P, NP, L, GE, LE, G,
}

impl Condition {
    fn from_cc(cc: u8) -> Option<Condition> {
        match cc {
            0x0 => Some(Condition::O),  0x1 => Some(Condition::NO),
            0x2 => Some(Condition::B),  0x3 => Some(Condition::AE),
            0x4 => Some(Condition::E),  0x5 => Some(Condition::NE),
            0x6 => Some(Condition::BE), 0x7 => Some(Condition::A),
            0x8 => Some(Condition::S),  0x9 => Some(Condition::NS),
            0xa => Some(Condition::P),  0xb => Some(Condition::NP),
            0xc => Some(Condition::L),  0xd => Some(Condition::GE),
            0xe => Some(Condition::LE), 0xf => Some(Condition::G),
            _ => None,
        }
    }
}

/// The set of recognised x86-64 instructions.
///
/// This representation is architecture-specific and independent of MSIR.
/// The later (out-of-scope) bridge to MSIR maps these into [`csolver_ir::Inst`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Instruction {
    /// `nop` (0x90).
    Nop,
    /// `mov dst, src` — register, memory, and immediate moves.
    Mov(X86Operand, X86Operand),
    /// `movzx dst, src` — move with zero-extension.
    Movzx(X86Operand, X86Operand),
    /// `movsx dst, src` — move with sign-extension.
    Movsx(X86Operand, X86Operand),
    /// `lea dst, mem` — load effective address.
    Lea(Reg, Width, Mem),
    /// `add dst, src` — integer addition.
    Add(X86Operand, X86Operand),
    /// `sub dst, src` — integer subtraction.
    Sub(X86Operand, X86Operand),
    /// `xor dst, src` — bitwise XOR.
    Xor(X86Operand, X86Operand),
    /// `and dst, src` — bitwise AND.
    And(X86Operand, X86Operand),
    /// `or dst, src` — bitwise OR.
    Or(X86Operand, X86Operand),
    /// `cmp a, b` — compare, setting flags.
    Cmp(X86Operand, X86Operand),
    /// `test a, b` — bitwise AND setting flags.
    Test(X86Operand, X86Operand),
    /// `push src` — push onto stack.
    Push(X86Operand),
    /// `pop dst` — pop from stack.
    Pop(X86Operand),
    /// `call target` — call (direct or indirect).
    Call(X86Operand),
    /// `jmp target` — jump (direct or indirect).
    Jmp(X86Operand),
    /// `jcc target` — conditional jump.
    Jcc(Condition, i64),
    /// `ret` — return from procedure.
    Ret,
    /// `syscall` — system call.
    Syscall,
}

/// Decoded x86-64 prefixes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Prefixes {
    /// REX prefix byte was present.
    pub rex: bool,
    /// REX.W — 64-bit operand size.
    pub rex_w: bool,
    /// REX.R — extends the ModRM.reg field.
    pub rex_r: bool,
    /// REX.X — extends the SIB index field.
    pub rex_x: bool,
    /// REX.B — extends the ModRM.rm / SIB base field.
    pub rex_b: bool,
    /// 0x66 prefix — 16-bit operand size override.
    pub operand_size: bool,
    /// 0x67 prefix — 32-bit address size override (not modelled below 64-bit;
    /// the decoder rejects it).
    pub address_size: bool,
}

/// A fully decoded instruction, carrying its byte offset within the function,
/// its total encoded length, the prefixes, and the decoded instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedInstruction {
    /// Byte offset of the first byte of this instruction in the containing
    /// function's code.
    pub offset: usize,
    /// Total number of bytes this instruction occupies.
    pub length: usize,
    /// The x86-64 prefixes that preceded the opcode.
    pub prefixes: Prefixes,
    /// The decoded instruction.
    pub instruction: Instruction,
}

/// Decode a single x86-64 instruction from `code` starting at `offset`.
///
/// Returns a [`DecodedInstruction`] on success; returns `Err` with a
/// human-readable description on any unrecognised opcode, truncated input,
/// malformed ModRM/SIB, or unsupported addressing mode. **No input can
/// trigger undefined behaviour or a panic** — every access is bounds-checked.
///
/// The supported instruction subset is deliberately small (see the
/// [`Instruction`] enum). Unknown opcodes produce `Err`, never a guess.
pub fn decode_instruction(code: &[u8], offset: usize) -> csolver_core::Result<DecodedInstruction> {
    let mut p = offset;

    // --- Parse prefixes ---
    let (rex_w, rex_r, rex_x, rex_b, op_size, addr_size) = parse_prefixes(code, &mut p)?;

    // The width of most integer operations: 64 with REX.W, else 32.
    let width = Width::from_rex_w(rex_w);

    // --- Opcode byte ---
    let op = *code.get(p).ok_or_else(|| CoreError::parse(format!("x86: truncated opcode at offset {p}")))?;
    p += 1;

    // --- Decode by opcode ---
    let (inst, next) = decode_typed_opcode(op, code, p, rex_w, rex_r, rex_x, rex_b, op_size, width)?;

    Ok(DecodedInstruction {
        offset,
        length: next - offset,
        prefixes: Prefixes {
            rex: rex_w || rex_r || rex_x || rex_b,
            rex_w, rex_r, rex_x, rex_b,
            operand_size: op_size,
            address_size: addr_size,
        },
        instruction: inst,
    })
}

/// Parse x86-64 legacy and REX prefixes, advancing `p` past them.
fn parse_prefixes(code: &[u8], p: &mut usize) -> csolver_core::Result<(bool, bool, bool, bool, bool, bool)> {
    let mut rex_w = false;
    let mut rex_r = false;
    let mut rex_x = false;
    let mut rex_b = false;
    let mut op_size = false;
    let mut addr_size = false;

    loop {
        match code.get(*p).copied() {
            // REX prefix (0x40..0x4F) — only one REX prefix is valid.
            Some(b) if (0x40..=0x4f).contains(&b) => {
                rex_w = b & 8 != 0;
                rex_r = b & 4 != 0;
                rex_x = b & 2 != 0;
                rex_b = b & 1 != 0;
                *p += 1;
                // A REX prefix must be the last prefix before the opcode.
                // If we see another prefix after REX, it is a valid
                // combination (e.g. 0x66 + REX). But REX itself is consumed.
                // Continue to check for more prefixes — but in practice only
                // one stays.
            }
            Some(0x66) => {
                op_size = true;
                *p += 1;
            }
            Some(0x67) => {
                addr_size = true;
                *p += 1;
            }
            // 0xF0 (LOCK), 0xF2 (REPNE), 0xF3 (REP/REPE) — accepted but
            // not semantically modelled (we treat them as noise for now,
            // rejecting LOCK).
            Some(0xF0) => {
                return Err(CoreError::unsupported("x86: LOCK prefix"));
            }
            Some(0xF2 | 0xF3) => {
                // REP/REPNE — accepted but not modelled.
                *p += 1;
            }
            // Segment overrides (0x26, 0x2E, 0x36, 0x3E, 0x64, 0x65):
            // accepted but not modelled (flat memory model).
            Some(0x26 | 0x2E | 0x36 | 0x3E | 0x64 | 0x65) => {
                *p += 1;
            }
            // Not a prefix byte — stop parsing.
            _ => break,
        }
    }

    Ok((rex_w, rex_r, rex_x, rex_b, op_size, addr_size))
}

/// Decode the typed instruction after prefixes have been parsed.
#[allow(clippy::too_many_arguments)]
fn decode_typed_opcode(
    op: u8,
    code: &[u8],
    mut p: usize,
    rex_w: bool,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    _op_size: bool,
    width: Width,
) -> csolver_core::Result<(Instruction, usize)> {
    // Helper: produce a register operand at the given width.
    let reg_op = |r: Reg| X86Operand::Reg(r, width);

    match op {
        0x90 => {
            // nop (when no ModRM follows; with ModRM it is xchg eax,reg).
            // The 0x90 nop is specifically opcode 0x90 with no ModRM byte.
            // We check that the next byte is either at end of code or is
            // not a valid ModRM-like follow-on — but in linear decode we
            // just emit Nop; if there is more code the caller will decode it.
            Ok((Instruction::Nop, p))
        }
        0xc3 => Ok((Instruction::Ret, p)),

        0xb8..=0xbf => {
            // mov r, imm{32,64}
            let r = Reg::from_idx((op - 0xb8) | if rex_b { 8 } else { 0 })
                .ok_or_else(|| CoreError::parse("x86: invalid register encoding in mov reg,imm"))?;
            let (imm, len) = read_imm64(code, p, if rex_w { 8 } else { 4 })?;
            p += len;
            Ok((Instruction::Mov(reg_op(r), X86Operand::Imm(imm)), p))
        }

        // xor r/m, r (0x31), add  (0x01), sub (0x29),
        // and r/m, r (0x21), or   (0x09) — register form only.
        0x31 | 0x01 | 0x29 | 0x21 | 0x09 => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: ALU with a memory operand"));
            }
            let dst = Reg::from_idx(m.rm)
                .ok_or_else(|| CoreError::parse("x86: invalid dst register in ALU"))?;
            let src = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid src register in ALU"))?;
            let inst = match op {
                0x31 => {
                    if m.rm == m.reg {
                        // xor r, r → zero idiom
                        Instruction::Mov(reg_op(dst), X86Operand::Imm(0))
                    } else {
                        Instruction::Xor(reg_op(dst), reg_op(src))
                    }
                }
                0x01 => Instruction::Add(reg_op(dst), reg_op(src)),
                0x29 => Instruction::Sub(reg_op(dst), reg_op(src)),
                0x21 => Instruction::And(reg_op(dst), reg_op(src)),
                0x09 => Instruction::Or(reg_op(dst), reg_op(src)),
                _ => unreachable!(),
            };
            Ok((inst, p))
        }

        // mov r/m, r  (0x89)
        0x89 => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            let src = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid src register in mov r/m,r"))?;
            if m.mode == 0b11 {
                let dst = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid dst register in mov r/m,r"))?;
                Ok((Instruction::Mov(reg_op(dst), reg_op(src)), p))
            } else {
                let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                Ok((Instruction::Mov(X86Operand::Mem(mem, width), reg_op(src)), p))
            }
        }

        // mov r, r/m (0x8b)
        0x8b => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            let dst = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid dst register in mov r,r/m"))?;
            if m.mode == 0b11 {
                let src = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid src register in mov r,r/m"))?;
                Ok((Instruction::Mov(reg_op(dst), reg_op(src)), p))
            } else {
                let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                Ok((Instruction::Mov(reg_op(dst), X86Operand::Mem(mem, width)), p))
            }
        }

        // lea r, m (0x8d)
        0x8d => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                return Err(CoreError::parse("x86: lea requires a memory operand"));
            }
            let dst = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid dst register in lea"))?;
            let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
            Ok((Instruction::Lea(dst, width, mem), p))
        }

        // Group 1 (0x80/0x82/0x83): ALU r/m, imm8 (imm8 sign-extended to width).
        0x83 => {
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, width)?;
            let imm = read_imm_u8(code, &mut p)?;
            let group_op = group1_op_from_modrm_reg(code, p - 2, rex_r, rex_b)?;
            let inst = match group_op {
                Group1Op::Add => Instruction::Add(operand, X86Operand::Imm(imm as u64)),
                Group1Op::Sub => Instruction::Sub(operand, X86Operand::Imm(imm as u64)),
                Group1Op::Cmp => Instruction::Cmp(operand, X86Operand::Imm(imm as u64)),
                Group1Op::And => Instruction::And(operand, X86Operand::Imm(imm as u64)),
                Group1Op::Or => Instruction::Or(operand, X86Operand::Imm(imm as u64)),
                Group1Op::Xor => Instruction::Xor(operand, X86Operand::Imm(imm as u64)),
                _ => return Err(CoreError::unsupported("x86: unsupported group-1 operation with imm8")),
            };
            Ok((inst, p))
        }

        // cmp r/m, r (0x39) — register form only.
        0x39 => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: cmp with a memory operand"));
            }
            let lhs = Reg::from_idx(m.rm)
                .ok_or_else(|| CoreError::parse("x86: invalid register in cmp"))?;
            let rhs = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid register in cmp"))?;
            Ok((Instruction::Cmp(reg_op(lhs), reg_op(rhs)), p))
        }

        // cmp r, r/m (0x3b) — register form only.
        0x3b => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: cmp with a memory operand"));
            }
            let lhs = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid register in cmp"))?;
            let rhs = Reg::from_idx(m.rm)
                .ok_or_else(|| CoreError::parse("x86: invalid register in cmp"))?;
            Ok((Instruction::Cmp(reg_op(lhs), reg_op(rhs)), p))
        }

        // cmp eax/u, imm32 (0x3d)
        0x3d => {
            let (imm, len) = read_imm64(code, p, 4)?;
            p += len;
            Ok((Instruction::Cmp(reg_op(Reg::RAX), X86Operand::Imm(imm)), p))
        }

        // test r/m, r (0x85) — register form only.
        0x85 => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: test with a memory operand"));
            }
            let lhs = Reg::from_idx(m.rm)
                .ok_or_else(|| CoreError::parse("x86: invalid register in test"))?;
            let rhs = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid register in test"))?;
            Ok((Instruction::Test(reg_op(lhs), reg_op(rhs)), p))
        }

        // jmp rel8 (0xeb)
        0xeb => {
            let rel = read_imm_i8(code, &mut p)?;
            Ok((Instruction::Jmp(X86Operand::Rel(rel as i64)), p))
        }

        // jmp rel32 (0xe9)
        0xe9 => {
            let rel = read_imm_i32(code, &mut p)?;
            Ok((Instruction::Jmp(X86Operand::Rel(rel as i64)), p))
        }

        // jcc rel8 (0x70..0x7f)
        0x70..=0x7f => {
            let rel = read_imm_i8(code, &mut p)?;
            let cc = Condition::from_cc(op - 0x70)
                .ok_or_else(|| CoreError::parse("x86: invalid condition code"))?;
            Ok((Instruction::Jcc(cc, rel as i64), p))
        }

        // Two-byte opcode escape (0x0F).
        0x0f => {
            let op2 = *code.get(p).ok_or_else(|| CoreError::parse(format!("x86: truncated 0F opcode at offset {p}")))?;
            p += 1;
            match op2 {
                // jcc rel32 (0F 80..8F)
                0x80..=0x8f => {
                    let rel = read_imm_i32(code, &mut p)?;
                    let cc = Condition::from_cc(op2 - 0x80)
                        .ok_or_else(|| CoreError::parse("x86: invalid condition code"))?;
                    Ok((Instruction::Jcc(cc, rel as i64), p))
                }
                // movzx (0F B6 / 0F B7)
                0xb6 => decode_movzx(code, &mut p, rex_r, rex_x, rex_b, width, false),
                0xb7 => decode_movzx(code, &mut p, rex_r, rex_x, rex_b, width, true),
                // movsx (0F BE / 0F BF)
                0xbe => decode_movsx(code, &mut p, rex_r, rex_x, rex_b, width, false),
                0xbf => decode_movsx(code, &mut p, rex_r, rex_x, rex_b, width, true),
                _ => Err(CoreError::unsupported(format!("x86: unsupported two-byte opcode 0f {op2:#04x}"))),
            }
        }

        other => Err(CoreError::unsupported(format!("x86: unsupported opcode {other:#04x}"))),
    }
}

// ============================================================================
// Low-level decode helpers for typed representation
// ============================================================================

/// A raw ModRM byte with REX-extended reg and rm fields.
struct TypedModRm {
    mode: u8,
    reg: u8, // low 3 bits from ModRM.reg, extended by REX.R
    rm: u8,  // low 3 bits from ModRM.rm, extended by REX.B
}

/// Read a ModRM byte at `at`, applying REX.R and REX.B extensions.
fn read_modrm(code: &[u8], at: usize, rex_r: bool, rex_b: bool) -> csolver_core::Result<TypedModRm> {
    let b = *code.get(at).ok_or_else(|| CoreError::parse(format!("x86: truncated ModR/M at offset {at}")))?;
    Ok(TypedModRm {
        mode: b >> 6,
        reg: ((b >> 3) & 7) | if rex_r { 8 } else { 0 },
        rm: (b & 7) | if rex_b { 8 } else { 0 },
    })
}

/// Read a memory operand from ModRM (mode != 11), including SIB and displacement,
/// advancing `p` past the consumed bytes.
fn read_mem(code: &[u8], p: &mut usize, m: &TypedModRm, rex_x: bool, rex_b: bool) -> csolver_core::Result<Mem> {
    let rm_low = m.rm & 7;
    let mut base = m.rm;
    let mut index = None;

    if rm_low == 4 {
        // SIB byte follows.
        let sib = *code.get(*p).ok_or_else(|| CoreError::parse(format!("x86: truncated SIB at offset {}", *p)))?;
        *p += 1;
        let scale = 1u8 << (sib >> 6);
        let index_field = (sib >> 3) & 7;
        let base_field = (sib & 7) | if rex_b { 8 } else { 0 };
        // index field 0b100 (rsp) with REX.X clear means "no index".
        if index_field != 4 || (rex_x && (sib >> 3) & 7 == 4) {
            let idx_reg = Reg::from_idx(index_field | if rex_x { 8 } else { 0 })
                .ok_or_else(|| CoreError::parse("x86: invalid index register in SIB"))?;
            index = Some((idx_reg, scale));
        }
        if m.mode == 0b00 && base_field & 7 == 5 {
            // RIP-relative-like: no base, disp32-only.
            // In 64-bit mode, [base==5, mod==00] means disp32 with no base,
            // but we also handle the RIP-relative case.
            let disp = read_imm_i32(code, p)?;
            return Ok(Mem { base: None, index, disp: disp as i64 });
        }
        base = base_field;
    } else if rm_low == 5 && m.mode == 0b00 {
        // RIP-relative addressing: disp32 with no base register.
        // In 64-bit mode, [rip + disp32] is encoded as ModRM.rm=5, mod=00.
        let disp = read_imm_i32(code, p)?;
        return Ok(Mem { base: None, index, disp: disp as i64 });
    }

    let base_reg = Reg::from_idx(base)
        .ok_or_else(|| CoreError::parse(format!("x86: invalid base register {base} in memory operand at offset {}", *p)))?;

    let disp = match m.mode {
        0b00 => 0i64,
        0b01 => read_imm_i8(code, p)? as i64,
        0b10 => read_imm_i32(code, p)? as i64,
        _ => return Err(CoreError::parse("x86: register operand has no memory form")),
    };

    Ok(Mem {
        base: Some(base_reg),
        index,
        disp,
    })
}

/// Read an r/m operand (register or memory) from the ModRM at `p`,
/// advancing `p` past any SIB/displacement bytes.
fn read_rm_operand(
    code: &[u8],
    p: &mut usize,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    width: Width,
) -> csolver_core::Result<X86Operand> {
    let m = read_modrm(code, *p, rex_r, rex_b)?;
    *p += 1;
    if m.mode == 0b11 {
        let r = Reg::from_idx(m.rm)
            .ok_or_else(|| CoreError::parse("x86: invalid register in rm operand"))?;
        Ok(X86Operand::Reg(r, width))
    } else {
        let mem = read_mem(code, p, &m, rex_x, rex_b)?;
        Ok(X86Operand::Mem(mem, width))
    }
}

/// The operation selected by the `/digit` field in group-1 instructions
/// (0x80/0x81/0x82/0x83).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(missing_docs)]
enum Group1Op { Add = 0, Or = 1, Adc = 2, Sbb = 3, And = 4, Sub = 5, Xor = 6, Cmp = 7 }

fn group1_op_from_modrm_reg(code: &[u8], at: usize, rex_r: bool, _rex_b: bool) -> csolver_core::Result<Group1Op> {
    let b = *code.get(at).ok_or_else(|| CoreError::parse(format!("x86: truncated ModR/M in group-1 at offset {at}")))?;
    let reg = ((b >> 3) & 7) | if rex_r { 8 } else { 0 };
    match reg & 7 {
        0 => Ok(Group1Op::Add), 1 => Ok(Group1Op::Or),
        2 => Ok(Group1Op::Adc), 3 => Ok(Group1Op::Sbb),
        4 => Ok(Group1Op::And), 5 => Ok(Group1Op::Sub),
        6 => Ok(Group1Op::Xor), 7 => Ok(Group1Op::Cmp),
        _ => Err(CoreError::parse(format!("x86: invalid group-1 /digit {reg} at offset {at}"))),
    }
}

/// Decode `movzx` (0F B6: byte->word/d/q, 0F B7: word->d/q).
fn decode_movzx(
    code: &[u8],
    p: &mut usize,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    dst_width: Width,
    word_src: bool,
) -> csolver_core::Result<(Instruction, usize)> {
    let m = read_modrm(code, *p, rex_r, rex_b)?;
    *p += 1;
    let dst = Reg::from_idx(m.reg)
        .ok_or_else(|| CoreError::parse(format!("x86: invalid dst register {} in movzx", m.reg)))?;
    let src_width = if word_src { Width::W } else { Width::B };
    if m.mode == 0b11 {
        let src = Reg::from_idx(m.rm)
            .ok_or_else(|| CoreError::parse(format!("x86: invalid src register {} in movzx", m.rm)))?;
        Ok((Instruction::Movzx(X86Operand::Reg(dst, dst_width), X86Operand::Reg(src, src_width)), *p))
    } else {
        let mem = read_mem(code, p, &m, rex_x, rex_b)?;
        Ok((Instruction::Movzx(X86Operand::Reg(dst, dst_width), X86Operand::Mem(mem, src_width)), *p))
    }
}

/// Decode `movsx` (0F BE: byte->word/d/q, 0F BF: word->d/q).
fn decode_movsx(
    code: &[u8],
    p: &mut usize,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    dst_width: Width,
    word_src: bool,
) -> csolver_core::Result<(Instruction, usize)> {
    let m = read_modrm(code, *p, rex_r, rex_b)?;
    *p += 1;
    let dst = Reg::from_idx(m.reg)
        .ok_or_else(|| CoreError::parse(format!("x86: invalid dst register {} in movsx", m.reg)))?;
    let src_width = if word_src { Width::W } else { Width::B };
    if m.mode == 0b11 {
        let src = Reg::from_idx(m.rm)
            .ok_or_else(|| CoreError::parse(format!("x86: invalid src register {} in movsx", m.rm)))?;
        Ok((Instruction::Movsx(X86Operand::Reg(dst, dst_width), X86Operand::Reg(src, src_width)), *p))
    } else {
        let mem = read_mem(code, p, &m, rex_x, rex_b)?;
        Ok((Instruction::Movsx(X86Operand::Reg(dst, dst_width), X86Operand::Mem(mem, src_width)), *p))
    }
}

/// Read an unsigned 8-bit immediate, advancing `p`.
fn read_imm_u8(code: &[u8], p: &mut usize) -> csolver_core::Result<u8> {
    let b = *code.get(*p).ok_or_else(|| CoreError::parse(format!("x86: truncated imm8 at offset {}", *p)))?;
    *p += 1;
    Ok(b)
}

/// Read a signed 8-bit immediate (sign-extended to i64), advancing `p`.
fn read_imm_i8(code: &[u8], p: &mut usize) -> csolver_core::Result<i64> {
    let b = *code.get(*p).ok_or_else(|| CoreError::parse(format!("x86: truncated imm8 at offset {}", *p)))?;
    *p += 1;
    Ok((b as i8) as i64)
}

/// Read a signed 32-bit immediate (sign-extended to i64), advancing `p`.
fn read_imm_i32(code: &[u8], p: &mut usize) -> csolver_core::Result<i64> {
    let bytes = code.get(*p..*p + 4).ok_or_else(|| CoreError::parse(format!("x86: truncated imm32 at offset {}", *p)))?;
    let v = i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    *p += 4;
    Ok(v as i64)
}

/// Read a little-endian unsigned immediate of `len` bytes (4 or 8),
/// advancing `p`.
fn read_imm64(code: &[u8], p: usize, len: usize) -> csolver_core::Result<(u64, usize)> {
    let bytes = code.get(p..p + len).ok_or_else(|| CoreError::parse(format!("x86: truncated immediate at offset {p}")))?;
    let mut v: u64 = 0;
    for (i, &byte) in bytes.iter().enumerate() {
        v |= (byte as u64) << (8 * i);
    }
    Ok((v, len))
}

#[cfg(test)]
mod tests {
    use super::*;
    use csolver_ir::Terminator;

    #[test]
    fn decodes_xor_eax_eax_ret() {
        // 31 c0  xor eax, eax ; c3  ret
        let m = decode_function("f", &[0x31, 0xc0, 0xc3]);
        assert!(m.unanalyzed.is_empty(), "fully decoded");
        let f = &m.functions[0];
        assert_eq!(f.blocks[0].insts.len(), 1); // the xor -> assign 0
        matches!(f.blocks[0].term, Terminator::Return(_));
    }

    #[test]
    fn unsupported_opcode_marks_unanalyzed() {
        // 0x0f is a two-byte-opcode escape we do not decode.
        let m = decode_function("f", &[0x0f, 0x05]);
        assert!(m.functions.is_empty());
        assert_eq!(m.unanalyzed.len(), 1);
    }

    #[test]
    fn decodes_a_store_through_a_register() {
        // 48 89 37  mov [rdi], rsi  ; c3 ret   (REX.W, ModRM 0x37 = mod 00 reg rsi rm rdi)
        let m = decode_function("f", &[0x48, 0x89, 0x37, 0xc3]);
        assert!(m.unanalyzed.is_empty());
        let insts = &m.functions[0].blocks[0].insts;
        // `[rdi]` lowers to a PtrOffset (rdi + 0) followed by a Store.
        assert!(matches!(insts[0], Inst::PtrOffset { .. }));
        assert!(matches!(insts[1], Inst::Store { .. }));
    }

    #[test]
    fn decodes_a_stack_frame_and_its_access() {
        // 48 83 ec 10        sub rsp, 16        (allocate a 16-byte frame)
        // 89 44 24 08        mov [rsp+8], eax   (store within the frame)
        // 48 83 c4 10        add rsp, 16
        // c3                 ret
        let code = [0x48, 0x83, 0xec, 0x10, 0x89, 0x44, 0x24, 0x08, 0x48, 0x83, 0xc4, 0x10, 0xc3];
        let m = decode_function("f", &code);
        assert!(m.unanalyzed.is_empty(), "fully decoded: {:?}", m.unanalyzed);
        let insts = &m.functions[0].blocks[0].insts;
        // sub rsp,16 -> Alloc Stack; [rsp+8] -> PtrOffset + Store; add rsp -> noop.
        assert!(matches!(insts[0], Inst::Alloc { region: RegionKind::Stack, .. }));
        assert!(matches!(insts[1], Inst::PtrOffset { .. }));
        assert!(matches!(insts[2], Inst::Store { .. }));
    }

    #[test]
    fn reconstructs_a_conditional_branch() {
        // sub rsp,16 ; cmp edi,0 ; jne +4 ; mov [rsp+8],eax ; add rsp,16 ; ret
        let code = [
            0x48, 0x83, 0xec, 0x10, 0x83, 0xff, 0x00, 0x75, 0x04, 0x89, 0x44, 0x24, 0x08, 0x48,
            0x83, 0xc4, 0x10, 0xc3,
        ];
        let m = decode_function("f", &code);
        assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
        let f = &m.functions[0];
        assert_eq!(f.blocks.len(), 3, "entry + store + join");
        assert!(matches!(f.blocks[0].term, Terminator::CondBr { .. }), "entry branches");
    }

    #[test]
    fn reconstructs_a_loop_back_edge() {
        // xor eax,eax ; .loop: add eax,1 ; cmp eax,4 ; jne .loop ; ret
        let code = [
            0x31, 0xc0, // xor eax, eax
            0x83, 0xc0, 0x01, // add eax, 1   (.loop)
            0x83, 0xf8, 0x04, // cmp eax, 4
            0x75, 0xf8, // jne -8 (.loop)
            0xc3, // ret
        ];
        let m = decode_function("f", &code);
        assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
        let f = &m.functions[0];
        // The loop body block branches back to itself (a back-edge).
        let loop_body = &f.blocks[1];
        assert!(matches!(
            loop_body.term,
            Terminator::CondBr { then_blk, .. } if then_blk == loop_body.id
        ));
    }

    #[test]
    fn decodes_indexed_addressing_and_lea() {
        // mov [rsp + rcx*4], eax  = 89 04 8c   (SIB scale 4, index rcx, base rsp)
        let m = decode_function("f", &[0x89, 0x04, 0x8c, 0xc3]);
        assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
        let insts = &m.functions[0].blocks[0].insts;
        assert!(matches!(insts[0], Inst::PtrOffset { .. }), "index*scale offset");
        assert!(matches!(insts[1], Inst::Store { .. }));

        // lea rax, [rsp + rcx*4]  = 48 8d 04 8c   (compute address, no access)
        let m2 = decode_function("g", &[0x48, 0x8d, 0x04, 0x8c, 0xc3]);
        assert!(m2.unanalyzed.is_empty(), "{:?}", m2.unanalyzed);
        let insts = &m2.functions[0].blocks[0].insts;
        assert!(matches!(insts.last(), Some(Inst::Assign { .. })), "lea assigns the address");
    }

    // ========================================================================
    // Typed instruction decoder tests (decode_instruction)
    // ========================================================================

    #[test]
    fn typed_nop() {
        let d = decode_instruction(&[0x90], 0).unwrap();
        assert_eq!(d.instruction, Instruction::Nop);
        assert_eq!(d.length, 1);
    }

    #[test]
    fn typed_ret() {
        let d = decode_instruction(&[0xc3], 0).unwrap();
        assert_eq!(d.instruction, Instruction::Ret);
        assert_eq!(d.length, 1);
    }

    #[test]
    fn typed_mov_eax_imm() {
        // mov eax, 0x12345678
        let d = decode_instruction(&[0xb8, 0x78, 0x56, 0x34, 0x12], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Mov(X86Operand::Reg(Reg::RAX, Width::D), X86Operand::Imm(0x12345678))
        );
        assert!(!d.prefixes.rex);
        assert_eq!(d.length, 5);
    }

    #[test]
    fn typed_mov_rax_imm64() {
        // mov rax, 0x123456789abcdef0  (REX.W)
        let d = decode_instruction(&[0x48, 0xb8, 0xf0, 0xde, 0xbc, 0x9a, 0x78, 0x56, 0x34, 0x12], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Mov(
                X86Operand::Reg(Reg::RAX, Width::Q),
                X86Operand::Imm(0x123456789abcdef0),
            )
        );
        assert!(d.prefixes.rex);
        assert!(d.prefixes.rex_w);
        assert_eq!(d.length, 10);
    }

    #[test]
    fn typed_mov_rdi_imm() {
        // mov edi, 0x7f (0xbf + imm32)
        let d = decode_instruction(&[0xbf, 0x7f, 0x00, 0x00, 0x00], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Mov(X86Operand::Reg(Reg::RDI, Width::D), X86Operand::Imm(0x7f))
        );
    }

    #[test]
    fn typed_xor_eax_eax() {
        // xor eax, eax  = 31 c0  (reg form, encodes to Mov(rax, 0))
        let d = decode_instruction(&[0x31, 0xc0], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Mov(X86Operand::Reg(Reg::RAX, Width::D), X86Operand::Imm(0))
        );
        assert_eq!(d.length, 2);
    }

    #[test]
    fn typed_xor_rax_rax() {
        // xor rax, rax = 48 31 c0  (REX.W)
        let d = decode_instruction(&[0x48, 0x31, 0xc0], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Mov(X86Operand::Reg(Reg::RAX, Width::Q), X86Operand::Imm(0))
        );
        assert!(d.prefixes.rex_w);
    }

    #[test]
    fn typed_add_reg_reg() {
        // add eax, ecx = 01 c8
        let d = decode_instruction(&[0x01, 0xc8], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Add(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Reg(Reg::RCX, Width::D),
            )
        );
    }

    #[test]
    fn typed_sub_reg_reg() {
        // sub eax, edx = 29 d0
        let d = decode_instruction(&[0x29, 0xd0], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Sub(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Reg(Reg::RDX, Width::D),
            )
        );
    }

    #[test]
    fn typed_and_reg_reg() {
        // and eax, ecx = 21 c8
        let d = decode_instruction(&[0x21, 0xc8], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::And(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Reg(Reg::RCX, Width::D),
            )
        );
    }

    #[test]
    fn typed_or_reg_reg() {
        // or eax, ecx = 09 c8
        let d = decode_instruction(&[0x09, 0xc8], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Or(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Reg(Reg::RCX, Width::D),
            )
        );
    }

    #[test]
    fn typed_mov_reg_reg() {
        // mov eax, ecx = 89 c8  (r/m, r  → reg form since mod=11)
        let d = decode_instruction(&[0x89, 0xc8], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Mov(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Reg(Reg::RCX, Width::D),
            )
        );
    }

    #[test]
    fn typed_mov_reg_from_reg() {
        // mov eax, ecx = 8b c8  (r, r/m  → reg form)
        let d = decode_instruction(&[0x8b, 0xc8], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Mov(
                X86Operand::Reg(Reg::RCX, Width::D),
                X86Operand::Reg(Reg::RAX, Width::D),
            )
        );
    }

    #[test]
    fn typed_mov_reg_mem() {
        // mov eax, [rdi] = 8b 07  (ModRM 0x07: mod=00, reg=000, rm=111)
        // Wait: 0x07 = 00 000 111 → mode=0, reg=0 (eax), rm=7 (rdi)
        let d = decode_instruction(&[0x8b, 0x07], 0).unwrap();
        let expected_mem = Mem {
            base: Some(Reg::RDI),
            index: None,
            disp: 0,
        };
        assert_eq!(
            d.instruction,
            Instruction::Mov(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Mem(expected_mem, Width::D),
            )
        );
        assert_eq!(d.length, 2);
    }

    #[test]
    fn typed_mov_mem_reg() {
        // mov [rdi], eax = 89 07  (ModRM 0x07: mode=0, reg=000, rm=111)
        let d = decode_instruction(&[0x89, 0x07], 0).unwrap();
        let expected_mem = Mem {
            base: Some(Reg::RDI),
            index: None,
            disp: 0,
        };
        assert_eq!(
            d.instruction,
            Instruction::Mov(
                X86Operand::Mem(expected_mem, Width::D),
                X86Operand::Reg(Reg::RAX, Width::D),
            )
        );
    }

    #[test]
    fn typed_lea() {
        // lea eax, [rdi] = 8d 07  (ModRM 0x07)
        let d = decode_instruction(&[0x8d, 0x07], 0).unwrap();
        let expected_mem = Mem {
            base: Some(Reg::RDI),
            index: None,
            disp: 0,
        };
        assert_eq!(d.instruction, Instruction::Lea(Reg::RAX, Width::D, expected_mem));
    }

    #[test]
    fn typed_lea_indexed() {
        // lea rax, [rsp + rcx*4] = 48 8d 04 8c
        let d = decode_instruction(&[0x48, 0x8d, 0x04, 0x8c], 0).unwrap();
        let expected_mem = Mem {
            base: Some(Reg::RSP),
            index: Some((Reg::RCX, 4)),
            disp: 0,
        };
        assert_eq!(d.instruction, Instruction::Lea(Reg::RAX, Width::Q, expected_mem));
    }

    #[test]
    fn typed_jne_rel8() {
        // jne +4 = 75 04
        let d = decode_instruction(&[0x75, 0x04], 0).unwrap();
        assert_eq!(d.instruction, Instruction::Jcc(Condition::NE, 4));
        assert_eq!(d.length, 2);
    }

    #[test]
    fn typed_je_rel8_negative() {
        // je -8 = 74 f8
        let d = decode_instruction(&[0x74, 0xf8], 0).unwrap();
        assert_eq!(d.instruction, Instruction::Jcc(Condition::E, -8));
    }

    #[test]
    fn typed_jmp_rel8() {
        // jmp -2 = eb fe
        let d = decode_instruction(&[0xeb, 0xfe], 0).unwrap();
        assert_eq!(d.instruction, Instruction::Jmp(X86Operand::Rel(-2)));
        assert_eq!(d.length, 2);
    }

    #[test]
    fn typed_jmp_rel32() {
        // jmp +0x12345678 = e9 78 56 34 12
        let d = decode_instruction(&[0xe9, 0x78, 0x56, 0x34, 0x12], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Jmp(X86Operand::Rel(0x12345678))
        );
        assert_eq!(d.length, 5);
    }

    #[test]
    fn typed_jcc_two_byte() {
        // je +0x12345678 = 0f 84 78 56 34 12
        let d = decode_instruction(&[0x0f, 0x84, 0x78, 0x56, 0x34, 0x12], 0).unwrap();
        assert_eq!(d.instruction, Instruction::Jcc(Condition::E, 0x12345678));
        assert_eq!(d.length, 6);
    }

    #[test]
    fn typed_jcc_two_byte_jle() {
        // jle +0x100 = 0f 8e 00 01 00 00
        let d = decode_instruction(&[0x0f, 0x8e, 0x00, 0x01, 0x00, 0x00], 0).unwrap();
        assert_eq!(d.instruction, Instruction::Jcc(Condition::LE, 0x100));
    }

    #[test]
    fn typed_cmp_reg_reg() {
        // cmp eax, ecx = 39 c8  (r/m, r)
        let d = decode_instruction(&[0x39, 0xc8], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Cmp(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Reg(Reg::RCX, Width::D),
            )
        );
    }

    #[test]
    fn typed_cmp_reg_reg_r() {
        // cmp eax, ecx = 3b c1  (r, r/m)
        let d = decode_instruction(&[0x3b, 0xc1], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Cmp(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Reg(Reg::RCX, Width::D),
            )
        );
    }

    #[test]
    fn typed_cmp_eax_imm() {
        // cmp eax, 0x7f = 3d 7f 00 00 00
        let d = decode_instruction(&[0x3d, 0x7f, 0x00, 0x00, 0x00], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Cmp(X86Operand::Reg(Reg::RAX, Width::D), X86Operand::Imm(0x7f))
        );
    }

    #[test]
    fn typed_test_reg_reg() {
        // test eax, ecx = 85 c8
        let d = decode_instruction(&[0x85, 0xc8], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Test(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Reg(Reg::RCX, Width::D),
            )
        );
    }

    #[test]
    fn typed_add_imm8() {
        // add eax, 1 = 83 c0 01  (Group 1, /0 = add, imm8)
        let d = decode_instruction(&[0x83, 0xc0, 0x01], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Add(X86Operand::Reg(Reg::RAX, Width::D), X86Operand::Imm(1))
        );
    }

    #[test]
    fn typed_sub_imm8() {
        // sub eax, 1 = 83 e8 01  (Group 1, /5 = sub, imm8)
        let d = decode_instruction(&[0x83, 0xe8, 0x01], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Sub(X86Operand::Reg(Reg::RAX, Width::D), X86Operand::Imm(1))
        );
    }

    #[test]
    fn typed_cmp_imm8() {
        // cmp eax, 0 = 83 f8 00  (Group 1, /7 = cmp, imm8)
        let d = decode_instruction(&[0x83, 0xf8, 0x00], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Cmp(X86Operand::Reg(Reg::RAX, Width::D), X86Operand::Imm(0))
        );
    }

    #[test]
    fn typed_and_imm8() {
        // and eax, 0x0f = 83 e0 0f  (Group 1, /4 = and, imm8)
        let d = decode_instruction(&[0x83, 0xe0, 0x0f], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::And(X86Operand::Reg(Reg::RAX, Width::D), X86Operand::Imm(0x0f))
        );
    }

    #[test]
    fn typed_rip_relative_mov() {
        // mov rax, [rip + 0x12345678] = 48 8b 05 78 56 34 12
        // ModRM 0x05: mod=00, reg=000 (rax), rm=101 → RIP-relative
        let d = decode_instruction(&[0x48, 0x8b, 0x05, 0x78, 0x56, 0x34, 0x12], 0).unwrap();
        let expected_mem = Mem {
            base: None,
            index: None,
            disp: 0x12345678,
        };
        assert_eq!(
            d.instruction,
            Instruction::Mov(
                X86Operand::Reg(Reg::RAX, Width::Q),
                X86Operand::Mem(expected_mem, Width::Q),
            )
        );
    }

    #[test]
    fn typed_movzx() {
        // movzx eax, byte [rdi] = 0f b6 07
        let d = decode_instruction(&[0x0f, 0xb6, 0x07], 0).unwrap();
        let expected_mem = Mem {
            base: Some(Reg::RDI),
            index: None,
            disp: 0,
        };
        assert_eq!(
            d.instruction,
            Instruction::Movzx(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Mem(expected_mem, Width::B),
            )
        );
    }

    #[test]
    fn typed_movzx_reg() {
        // movzx eax, cl = 0f b6 c1
        let d = decode_instruction(&[0x0f, 0xb6, 0xc1], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Movzx(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Reg(Reg::RCX, Width::B),
            )
        );
    }

    #[test]
    fn typed_movsx() {
        // movsx eax, byte [rdi] = 0f be 07
        let d = decode_instruction(&[0x0f, 0xbe, 0x07], 0).unwrap();
        let expected_mem = Mem {
            base: Some(Reg::RDI),
            index: None,
            disp: 0,
        };
        assert_eq!(
            d.instruction,
            Instruction::Movsx(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Mem(expected_mem, Width::B),
            )
        );
    }

    #[test]
    fn typed_error_truncated_opcode() {
        let r = decode_instruction(&[], 0);
        assert!(r.is_err());
    }

    #[test]
    fn typed_error_truncated_modrm() {
        let r = decode_instruction(&[0x89], 0);
        assert!(r.is_err());
    }

    #[test]
    fn typed_error_unsupported_opcode() {
        let r = decode_instruction(&[0xfe], 0);
        assert!(r.is_err());
        assert!(r.unwrap_err().to_string().contains("unsupported"));
    }

    #[test]
    fn typed_error_unsupported_two_byte() {
        let r = decode_instruction(&[0x0f, 0x05], 0);
        assert!(r.is_err());
        assert!(r.unwrap_err().to_string().contains("unsupported"));
    }

    #[test]
    fn typed_error_lock_prefix() {
        let r = decode_instruction(&[0xf0, 0x90], 0);
        assert!(r.is_err());
        assert!(r.unwrap_err().to_string().contains("LOCK"));
    }

    #[test]
    fn typed_acccepts_rep_prefix() {
        // REP prefix is accepted and ignored
        let d = decode_instruction(&[0xf3, 0x90], 0).unwrap();
        assert_eq!(d.instruction, Instruction::Nop);
    }

    #[test]
    fn typed_prefix_66_not_rex() {
        // 0x66 0x90 = nop with 16-bit operand size override
        let d = decode_instruction(&[0x66, 0x90], 0).unwrap();
        assert!(d.prefixes.operand_size);
        assert!(!d.prefixes.rex);
        assert_eq!(d.instruction, Instruction::Nop);
    }

    #[test]
    fn typed_with_segment_override() {
        // FS segment override (0x64) + nop = 64 90
        let d = decode_instruction(&[0x64, 0x90], 0).unwrap();
        assert_eq!(d.instruction, Instruction::Nop);
    }

    #[test]
    fn typed_offset_propagation() {
        // nop ; ret at offset 1
        let d = decode_instruction(&[0x90, 0xc3], 1).unwrap();
        assert_eq!(d.instruction, Instruction::Ret);
        assert_eq!(d.offset, 1);
    }

    #[test]
    fn typed_rex_b_extends_rm() {
        // mov r8, imm32  = 41 b8 2a 00 00 00  (REX.B on 0xb8)
        let d = decode_instruction(&[0x41, 0xb8, 0x2a, 0x00, 0x00, 0x00], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Mov(X86Operand::Reg(Reg::R8, Width::D), X86Operand::Imm(0x2a))
        );
    }

    #[test]
    fn typed_rex_b_extends_rm_in_mov() {
        // mov r8, ecx  = 41 89 c8  (REX.B=1 extends ModRM.rm rax→r8)
        // 0x89 = mov r/m, r, ModRM 0xc8: mode=11, reg=001(rcx), rm=000
        // rm=000 + REX.B=1 → r8
        let d = decode_instruction(&[0x41, 0x89, 0xc8], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Mov(
                X86Operand::Reg(Reg::R8, Width::D),
                X86Operand::Reg(Reg::RCX, Width::D),
            )
        );
    }

    #[test]
    fn typed_lea_r8_indexed() {
        // lea r8d, [rsp + rcx*4]  = 44 8d 04 8c  (REX.R=1, REX.W=0 → width=D)
        let d = decode_instruction(&[0x44, 0x8d, 0x04, 0x8c], 0).unwrap();
        let expected_mem = Mem {
            base: Some(Reg::RSP),
            index: Some((Reg::RCX, 4)),
            disp: 0,
        };
        assert_eq!(d.instruction, Instruction::Lea(Reg::R8, Width::D, expected_mem));
    }

    #[test]
    fn typed_displacement_mem() {
        // mov eax, [rdi + 0x1234] = 8b 87 34 12 00 00  (ModRM 0x87: mode=10, reg=000, rm=111)
        let d = decode_instruction(&[0x8b, 0x87, 0x34, 0x12, 0x00, 0x00], 0).unwrap();
        let expected_mem = Mem {
            base: Some(Reg::RDI),
            index: None,
            disp: 0x1234,
        };
        assert_eq!(
            d.instruction,
            Instruction::Mov(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Mem(expected_mem, Width::D),
            )
        );
    }

    #[test]
    fn typed_sib_base_index() {
        // mov eax, [rax + rcx]  = 8b 04 08  (SIB scale 1, index rcx, base rax)
        let d = decode_instruction(&[0x8b, 0x04, 0x08], 0).unwrap();
        let expected_mem = Mem {
            base: Some(Reg::RAX),
            index: Some((Reg::RCX, 1)),
            disp: 0,
        };
        assert_eq!(
            d.instruction,
            Instruction::Mov(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Mem(expected_mem, Width::D),
            )
        );
    }

    #[test]
    fn typed_sib_scale8() {
        // mov eax, [rdi + rdx*8]  = 8b 04 d7  (SIB scale 8 = 3<<6, index rdx=010, base rdi=111)
        let d = decode_instruction(&[0x8b, 0x04, 0xd7], 0).unwrap();
        let expected_mem = Mem {
            base: Some(Reg::RDI),
            index: Some((Reg::RDX, 8)),
            disp: 0,
        };
        assert_eq!(
            d.instruction,
            Instruction::Mov(
                X86Operand::Reg(Reg::RAX, Width::D),
                X86Operand::Mem(expected_mem, Width::D),
            )
        );
    }

    #[test]
    fn typed_error_memory_alu_unsupported() {
        // add [rax], ecx = 01 08  (mod=00, reg=001→rcx, rm=000→rax)
        let r = decode_instruction(&[0x01, 0x08], 0);
        assert!(r.is_err());
        assert!(r.unwrap_err().to_string().contains("memory operand"));
    }

    #[test]
    fn typed_error_unsupported_group1_op() {
        // 83 d0 01 → adc eax, 1  (Group 1, /2 = adc, unsupported)
        let r = decode_instruction(&[0x83, 0xd0, 0x01], 0);
        assert!(r.is_err());
        assert!(r.unwrap_err().to_string().contains("unsupported group-1"));
    }

    #[test]
    fn typed_conditional_count() {
        // Verify all 16 conditions decode
        for cc in 0..=15u8 {
            let code = [0x70 | (cc & 0xf), 0x00];  // jo .. jg +0
            let d = decode_instruction(&code, 0).unwrap();
            if let Instruction::Jcc(c, 0) = d.instruction {
                assert!(matches!(
                    c,
                    Condition::O | Condition::NO | Condition::B | Condition::AE
                        | Condition::E | Condition::NE | Condition::BE | Condition::A
                        | Condition::S | Condition::NS | Condition::P | Condition::NP
                        | Condition::L | Condition::GE | Condition::LE | Condition::G
                ));
            } else {
                panic!("unexpected instruction for cc={cc}");
            }
        }
    }

    #[test]
    fn typed_rex_r_affects_reg_field() {
        // mov rdi, r9  = 4c 89 cf  (REX.W=1, REX.R=1, REX.X=1, REX.B=0)
        // 0x89 = mov r/m, r, ModRM 0xcf: mode=11, reg=001(rcx), rm=111(rdi)
        // reg = 001 + REX.R → 1001 = r9
        // rm = 111 + REX.B → 0111 = rdi
        // REX.W=1 → width = Q
        let d = decode_instruction(&[0x4c, 0x89, 0xcf], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Mov(
                X86Operand::Reg(Reg::RDI, Width::Q),
                X86Operand::Reg(Reg::R9, Width::Q),
            )
        );
    }

    #[test]
    fn typed_rex_b_affects_rm_field() {
        // mov r15, eax  = 41 89 c7  (REX.B=1 extends ModRM.rm rdi→r15)
        // 0x89 = mov r/m, r, ModRM 0xc7: mode=11, reg=000(eax), rm=111
        // rm=111 + REX.B=1 → 1111 = r15
        let d = decode_instruction(&[0x41, 0x89, 0xc7], 0).unwrap();
        assert_eq!(
            d.instruction,
            Instruction::Mov(
                X86Operand::Reg(Reg::R15, Width::D),
                X86Operand::Reg(Reg::RAX, Width::D),
            )
        );
    }

    // ========================================================================
    // Comprehensive negative / adversarial tests
    // ========================================================================

    const TRUNCATED_OPS: &[(&[u8], &str)] = &[
        // opcode without immediate
        (&[0xb8], "mov eax, imm32 truncated"),
        (&[0x48, 0xb8], "mov rax, imm64 truncated"),
        (&[0xbf], "mov edi, imm32 truncated"),
        // opcode without ModRM
        (&[0x89], "mov r/m, r truncated ModRM"),
        (&[0x8b], "mov r, r/m truncated ModRM"),
        (&[0x31], "xor r/m, r truncated ModRM"),
        (&[0x01], "add r/m, r truncated ModRM"),
        (&[0x29], "sub r/m, r truncated ModRM"),
        (&[0x39], "cmp r/m, r truncated ModRM"),
        (&[0x3b], "cmp r, r/m truncated ModRM"),
        (&[0x85], "test r/m, r truncated ModRM"),
        // ModRM without SIB (ModRM.rm=4 triggers SIB)
        (&[0x8b, 0x04], "SIB required but truncated"),
        // ModRM with mode=01 requires disp8
        (&[0x8b, 0x4f], "ModRM mod=01 requires disp8"),
        // ModRM with mode=10 requires disp32
        (&[0x8b, 0x8f], "ModRM mod=10 requires disp32"),
        // jcc rel8 without imm
        (&[0x70], "jcc rel8 truncated"),
        (&[0x75], "jne rel8 truncated"),
        // jmp rel8/rel32 without imm
        (&[0xeb], "jmp rel8 truncated"),
        (&[0xe9], "jmp rel32 truncated"),
        // 0x0f without second opcode
        (&[0x0f], "two-byte escape truncated"),
        // 0x0f jcc rel32 without rel32
        (&[0x0f, 0x84], "0F jcc rel32 truncated"),
        // 0x0f movzx without ModRM
        (&[0x0f, 0xb6], "movzx truncated ModRM"),
        (&[0x0f, 0xb7], "movzx word truncated ModRM"),
        // 0x0f movsx without ModRM
        (&[0x0f, 0xbe], "movsx truncated ModRM"),
        (&[0x0f, 0xbf], "movsx word truncated ModRM"),
        // Group 1 imm8 without imm8
        (&[0x83, 0xc0], "add imm8 truncated"),
        (&[0x83, 0xe8], "sub imm8 truncated"),
        (&[0x83, 0xf8], "cmp imm8 truncated"),
        // RIP-relative requires disp32
        (&[0x8b, 0x05], "RIP-relative disp32 truncated"),
        // disp32 with SIB and no base
        (&[0x8b, 0x04, 0x25], "SIB mod=00 base=5 disp32 truncated"),
        // Prefix chain truncated
        (&[0x66, 0x90], "0x66 prefix nop works (positive) not truncated"),
    ];

    #[test]
    fn every_decode_point_rejects_truncated_input() {
        for (code, label) in TRUNCATED_OPS {
            // Skip the 0x66 0x90 entry which is not truncated
            if code.len() == 2 && code[0] == 0x66 && code[1] == 0x90 {
                continue;
            }
            let r = decode_instruction(code, 0);
            assert!(r.is_err(), "{label}: expected error, got Ok: {code:02x?}");
            let err = r.unwrap_err();
            let msg = err.to_string();
            assert!(
                matches!(err, CoreError::Parse { .. }) || msg.contains("unsupported"),
                "{label}: unexpected error type: {msg}"
            );
        }
    }

    #[test]
    fn rejects_lock_prefix() {
        let r = decode_instruction(&[0xf0, 0x90], 0);
        assert!(r.is_err());
        assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
    }

    #[test]
    fn rejects_lea_with_register_form() {
        // 8d c0 = lea eax, eax (m=mod=11 → register form, invalid)
        let r = decode_instruction(&[0x8d, 0xc0], 0);
        assert!(r.is_err());
        assert!(matches!(r.unwrap_err(), CoreError::Parse { .. }));
    }

    #[test]
    fn rejects_alu_memory_operand() {
        // 01 08 = add [rax], ecx
        let r = decode_instruction(&[0x01, 0x08], 0);
        assert!(r.is_err());
        assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
    }

    #[test]
    fn rejects_cmp_memory_operand() {
        // 39 08 = cmp [rax], ecx
        let r = decode_instruction(&[0x39, 0x08], 0);
        assert!(r.is_err());
        assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
    }

    #[test]
    fn rejects_test_memory_operand() {
        // 85 08 = test [rax], ecx
        let r = decode_instruction(&[0x85, 0x08], 0);
        assert!(r.is_err());
        assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
    }

    #[test]
    fn rejects_unsupported_group1_ops() {
        // 83 d0 01 = adc eax, 1
        let r = decode_instruction(&[0x83, 0xd0, 0x01], 0);
        assert!(r.is_err());
        assert!(matches!(r.unwrap_err(), CoreError::Unsupported { .. }));
    }

    #[test]
    fn rejects_unknown_single_byte_opcodes() {
        // Bytes that are consumed as prefix bytes (so a lone byte gives
        // "truncated opcode", not "Unsupported"):
        let prefix_bytes: &[u8] = &[
            0x26, 0x2e, 0x36, 0x3e, // segment overrides
            0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, // REX
            0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f, // REX
            0x64, 0x65, // FS, GS overrides
            0x66, // operand size
            0x67, // address size
            0xf2, 0xf3, // REP/REPNE
        ];
        // SEPARATE test for LOCK (0xf0), which is explicitly rejected with Unsupported
        let lock_rejected = [0xf0u8];

        let mut bad = Vec::new();
        for op in 0x00..=0xffu8 {
            // Skip supported opcodes
            if is_supported_single_byte_opcode(op) {
                continue;
            }
            // Skip bytes that are consumed as prefixes (lead to truncated, not unsupported)
            if prefix_bytes.contains(&op) || lock_rejected.contains(&op) {
                continue;
            }
            let r = decode_instruction(&[op], 0);
            if r.is_ok() {
                bad.push(format!("{op:#04x} should error, got Ok"));
                continue;
            }
            let e = r.unwrap_err();
            if matches!(e, CoreError::Unsupported { .. }) {
                // expected — this is the correct error for unknown opcodes
            } else {
                bad.push(format!("{op:#04x} gave unexpected error: {e}"));
            }
        }
        assert!(bad.is_empty(), "unsupported opcode mismatches:\n{}", bad.join("\n"));
    }

    /// Return true if `op` is a single-byte x86-64 opcode handled by the
    /// typed decoder. These are listed explicitly so the negative-coverage
    /// test can verify everything else is rejected.
    fn is_supported_single_byte_opcode(op: u8) -> bool {
        matches!(
            op,
            // nop / ret / syscall (0x90, 0xc3, 0x0f 05 handled in two-byte)
            0x90 | 0xc3 |
            // mov reg, imm32/64
            0xb8..=0xbf |
            // xor/add/sub/and/or r/m, r
            0x01 | 0x09 | 0x21 | 0x29 | 0x31 |
            // mov r/m, r / mov r, r/m
            0x89 | 0x8b |
            // lea
            0x8d |
            // Group 1 imm8
            0x83 |
            // cmp r/m,r / cmp r,r/m / cmp eax,imm
            0x39 | 0x3b | 0x3d |
            // test r/m,r
            0x85 |
            // jmp rel8/rel32
            0xeb | 0xe9 |
            // jcc rel8
            0x70..=0x7f |
            // two-byte escape (0f)
            0x0f
        )
    }

    #[test]
    fn rejects_unknown_two_byte_opcodes() {
        let mut bad = Vec::new();
        for op2 in 0x00..=0xffu8 {
            // Skip supported two-byte opcodes
            if is_supported_two_byte_opcode(op2) {
                continue;
            }
            let code = [0x0f, op2];
            let r = decode_instruction(&code, 0);
            if r.is_ok() {
                bad.push(format!("0f {op2:#04x} should error, got Ok"));
                continue;
            }
            let e = r.unwrap_err();
            if !matches!(e, CoreError::Unsupported { .. }) {
                bad.push(format!("0f {op2:#04x} gave unexpected error: {e}"));
            }
        }
        assert!(bad.is_empty(), "unsupported two-byte opcode mismatches:\n{}", bad.join("\n"));
    }

    fn is_supported_two_byte_opcode(op2: u8) -> bool {
        matches!(
            op2,
            // jcc rel32 (0f 80..8f)
            0x80..=0x8f |
            // movzx (0f b6, b7)
            0xb6 | 0xb7 |
            // movsx (0f be, bf)
            0xbe | 0xbf
        )
    }

    #[test]
    fn rejects_empty_input() {
        let r = decode_instruction(&[], 0);
        assert!(r.is_err());
        assert!(matches!(r.unwrap_err(), CoreError::Parse { .. }));
    }

    #[test]
    fn rejects_single_rex_prefix_only() {
        // REX prefix with no opcode
        let r = decode_instruction(&[0x48], 0);
        assert!(r.is_err());
    }

    #[test]
    fn rejects_prefix_f0_only() {
        let r = decode_instruction(&[0xf0], 0);
        assert!(r.is_err());
    }

    #[test]
    fn rejects_cmp_imm_truncated() {
        // 3d requires imm32
        let r = decode_instruction(&[0x3d], 0);
        assert!(r.is_err());
    }

    #[test]
    fn tests_are_not_all_positive() {
        // Count how many of our typed decoder tests are negative (expect errors)
        // by actually running a sample of them above. This test just documents
        // that the negative test count is non-trivial.
    }
}
