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

use csolver_ir::{
    BasicBlock, BinOp, BlockId, FuncId, Function, Inst, Module, Operand, RValue, RegId, Terminator,
    Type,
};

/// Decode a single straight-line x86-64 function from its machine bytes into a
/// one-function [`Module`]. On any unsupported construct the function is recorded
/// as `unanalyzed` (⇒ `UNKNOWN`), never silently mis-modelled.
pub fn decode_function(name: &str, code: &[u8]) -> Module {
    let mut m = Module::new("bin");
    match decode_block(code) {
        Ok(insts) => {
            let mut bb = BasicBlock::new(BlockId(0), Terminator::Return(None));
            bb.insts = insts;
            m.functions.push(Function {
                id: FuncId(0),
                name: name.into(),
                params: Vec::new(),
                ret_ty: Type::Unit,
                blocks: vec![bb],
                entry: BlockId(0),
            });
        }
        Err(reason) => m.unanalyzed.push((name.into(), reason)),
    }
    m
}

/// Decode a straight-line instruction sequence up to the first `ret`.
fn decode_block(code: &[u8]) -> Result<Vec<Inst>, String> {
    let mut insts = Vec::new();
    let mut pos = 0;
    while pos < code.len() {
        let decoded = decode_one(code, pos)?;
        insts.extend(decoded.insts);
        pos = decoded.next;
        if decoded.is_ret {
            break;
        }
    }
    Ok(insts)
}

/// The result of decoding one instruction.
struct Decoded {
    insts: Vec<Inst>,
    next: usize,
    is_ret: bool,
}

fn reg(num: u8) -> RegId {
    RegId(num as u32)
}

/// Decode one instruction starting at `pos`.
fn decode_one(code: &[u8], pos: usize) -> Result<Decoded, String> {
    let mut p = pos;
    // Optional REX prefix (0x40..0x4F): W=wide(64), R=reg ext, B=rm ext.
    let (rex_w, rex_r, rex_b) = match code.get(p) {
        Some(&b) if (0x40..=0x4f).contains(&b) => {
            p += 1;
            (b & 8 != 0, b & 4 != 0, b & 1 != 0)
        }
        _ => (false, false, false),
    };
    let op = *code.get(p).ok_or("x86: truncated opcode")?;
    p += 1;
    let width = if rex_w { 64 } else { 32 };
    let ty = Type::int(width);

    let done = |insts: Vec<Inst>, next: usize| Ok(Decoded { insts, next, is_ret: false });

    match op {
        0x90 => done(vec![], p),                                  // nop
        0xc3 => Ok(Decoded { insts: vec![], next: p, is_ret: true }), // ret
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
            // mov r/m, r — register move (mod 11) or store ([base], mod 00).
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
            } else if m.is_simple_base() {
                done(
                    vec![Inst::Store {
                        ty,
                        ptr: Operand::Reg(reg(m.rm)),
                        value: Operand::Reg(reg(m.reg)),
                        align: 1,
                    }],
                    p,
                )
            } else {
                Err("x86: unsupported addressing mode".into())
            }
        }
        0x8b => {
            // mov r, r/m — register move (mod 11) or load ([base], mod 00).
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
            } else if m.is_simple_base() {
                done(
                    vec![Inst::Load { dst: reg(m.reg), ty, ptr: Operand::Reg(reg(m.rm)), align: 1 }],
                    p,
                )
            } else {
                Err("x86: unsupported addressing mode".into())
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

impl ModRm {
    /// A plain `[base]` memory operand: `mod == 00` with a base register that is
    /// neither a SIB escape (`rm low == 100`) nor RIP-relative (`rm low == 101`).
    fn is_simple_base(&self) -> bool {
        self.mode == 0b00 && (self.rm & 7) != 4 && (self.rm & 7) != 5
    }
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
        assert!(matches!(m.functions[0].blocks[0].insts[0], Inst::Store { .. }));
    }
}
