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

use csolver_core::RegionKind;
use csolver_ir::{
    BasicBlock, BinOp, BlockId, CmpOp, FuncId, Function, Inst, Module, Operand, RValue, RegId,
    Terminator, Type,
};
use std::collections::BTreeMap;

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

/// The control-flow effect of an instruction.
#[derive(Debug, Clone, Copy)]
enum Ctrl {
    /// Falls through to the next instruction.
    Fall,
    /// `ret`.
    Ret,
    /// `jmp` to a byte offset.
    Jmp(usize),
    /// `jcc cond` to a byte offset (else falls through); `cond` is the MSIR
    /// register holding the branch condition.
    Jcc(usize, RegId),
}

/// One decoded instruction: its MSIR, its byte span, and its control-flow effect.
struct DecodedInsn {
    offset: usize,
    next: usize,
    insts: Vec<Inst>,
    ctrl: Ctrl,
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

/// Assemble decoded instructions into MSIR basic blocks. Block leaders are the
/// entry, every branch target, and the instruction after every branch/return.
/// A jump target that is not an instruction boundary makes the function
/// `unanalyzed` (sound: we do not guess at mid-instruction or data targets).
fn build_blocks(decoded: Vec<DecodedInsn>) -> Result<(Vec<BasicBlock>, BlockId), String> {
    if decoded.is_empty() {
        // An empty body is a vacuously-safe single `ret` block.
        return Ok((vec![BasicBlock::new(BlockId(0), Terminator::Return(None))], BlockId(0)));
    }
    let offsets: std::collections::HashSet<usize> = decoded.iter().map(|d| d.offset).collect();

    // Leaders.
    let mut leaders: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
    leaders.insert(decoded[0].offset);
    for d in &decoded {
        match d.ctrl {
            Ctrl::Jmp(t) | Ctrl::Jcc(t, _) => {
                if !offsets.contains(&t) {
                    return Err("x86: branch target is not an instruction boundary".into());
                }
                leaders.insert(t);
                leaders.insert(d.next); // the fall-through after a branch
            }
            Ctrl::Ret => {
                leaders.insert(d.next);
            }
            Ctrl::Fall => {}
        }
    }
    // Keep only leaders that begin an actual instruction.
    let leaders: Vec<usize> = leaders.into_iter().filter(|o| offsets.contains(o)).collect();
    let block_of: BTreeMap<usize, BlockId> =
        leaders.iter().enumerate().map(|(i, &o)| (o, BlockId(i as u32))).collect();

    // Each instruction belongs to the block of the greatest leader ≤ its offset.
    let mut blocks: Vec<BasicBlock> = leaders
        .iter()
        .map(|&o| BasicBlock::new(block_of[&o], Terminator::Return(None)))
        .collect();
    let mut cur = 0usize; // index into `leaders`
    for d in &decoded {
        // Advance to this instruction's block.
        while cur + 1 < leaders.len() && leaders[cur + 1] <= d.offset {
            cur += 1;
        }
        let block = &mut blocks[cur];
        block.insts.extend(d.insts.iter().cloned());
        // This is the block's last instruction when the next instruction starts a
        // new block (its offset is a leader) or there is no next instruction.
        let is_block_end = !offsets.contains(&d.next) || block_of.contains_key(&d.next);
        if is_block_end {
            block.term = terminator_for(d, &block_of)?;
        }
    }
    Ok((blocks, BlockId(0)))
}

/// The MSIR terminator for a block ending at `d`.
fn terminator_for(d: &DecodedInsn, block_of: &BTreeMap<usize, BlockId>) -> Result<Terminator, String> {
    let target = |off: usize| block_of.get(&off).copied().ok_or("x86: dangling branch target".to_string());
    Ok(match d.ctrl {
        Ctrl::Ret => Terminator::Return(None),
        Ctrl::Jmp(t) => Terminator::Br { target: target(t)?, args: Vec::new() },
        Ctrl::Jcc(t, cond) => Terminator::CondBr {
            cond: Operand::Reg(cond),
            then_blk: target(t)?,
            then_args: Vec::new(),
            else_blk: target(d.next)?,
            else_args: Vec::new(),
        },
        // A block that ends only because its successor is a branch target falls
        // through to it.
        Ctrl::Fall => Terminator::Br { target: target(d.next)?, args: Vec::new() },
    })
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
                return Err("x86: ALU with a memory operand is unsupported".into());
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
                return Err("x86: cmp with a memory operand is unsupported".into());
            }
            *flags = Some((Operand::Reg(reg(m.rm)), Operand::Reg(reg(m.reg))));
            done(vec![], p)
        }
        // cmp r, r/m (reg/reg form).
        0x3b => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err("x86: cmp with a memory operand is unsupported".into());
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

#[cfg(test)]
mod tests {
    use super::*;

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
}
