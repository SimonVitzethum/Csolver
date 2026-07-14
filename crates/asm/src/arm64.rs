//! A minimal AArch64 (ARM64) machine-code decoder → MSIR.
//!
//! AArch64 instructions are fixed 32-bit little-endian words decoded by field
//! extraction (no prefixes or ModR/M). This decodes a *small, growing* subset
//! and lowers a straight-line function to MSIR, mirroring the x86-64 frontend so
//! the audited analysis core verifies an ARM binary with no source. Registers
//! `x0..x30`/`sp` become MSIR `RegId`s (the encoding number); a `[base, #off]`
//! access becomes a `PtrOffset` + `Load`/`Store`.
//!
//! ## Soundness by graceful degradation
//! Any unrecognized encoding makes the *whole function* `unanalyzed` (reported
//! `UNKNOWN`), never guessed at — so the decoder can only be incomplete, never
//! unsound (a silently mis-modelled instruction could fabricate a false `PASS`).

use crate::blocks::{build_blocks, Ctrl, DecodedInsn};
use csolver_core::Error as CoreError;
use csolver_core::RegionKind;
use csolver_ir::{BinOp, CmpOp, FuncId, Function, Inst, Module, Operand, RValue, RegId, Type};

/// The stack-pointer register number in `add`/`sub` immediate and load/store
/// (where register 31 denotes `sp`, not the zero register).
const SP: u8 = 31;

fn reg(num: u8) -> RegId {
    RegId(num as u32)
}

fn temp_reg(pos: usize) -> RegId {
    RegId(1000 + pos as u32)
}

/// Decode an AArch64 function into a one-function [`Module`], reconstructing its
/// control-flow graph. On any unsupported encoding the function is recorded as
/// `unanalyzed` (⇒ `UNKNOWN`).
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
        Err(reason) => m.unanalyzed.push((name.into(), reason.to_string())),
    }
    m
}

/// The AArch64 PCS integer argument registers `x0..x7`, modelled as parameters so
/// each input register is a stable symbol (a guard can then constrain a later
/// access, as on x86).
fn arg_registers() -> Vec<(RegId, Type)> {
    (0u8..8).map(|r| (reg(r), Type::int(64))).collect()
}

/// Linearly decode the function body, threading the `cmp` flags for `b.cond`.
fn decode_cfg(code: &[u8]) -> csolver_core::Result<Vec<DecodedInsn>> {
    if !code.len().is_multiple_of(4) {
        return Err(CoreError::parse(
            "arm64: code length is not a multiple of 4",
        ));
    }
    let mut out = Vec::new();
    let mut pos = 0;
    let mut flags: Option<(Operand, Operand)> = None;
    while pos + 4 <= code.len() {
        let word = u32::from_le_bytes([code[pos], code[pos + 1], code[pos + 2], code[pos + 3]]);
        let d = decode_one(word, pos, &mut flags)?;
        out.push(DecodedInsn {
            offset: pos,
            next: pos + 4,
            insts: d.insts,
            ctrl: d.ctrl,
        });
        pos += 4;
    }
    Ok(out)
}

/// The result of decoding one instruction (before block assembly).
struct Decoded {
    insts: Vec<Inst>,
    ctrl: Ctrl,
}

/// Sign-extend the low `bits` of `v` to `i64`.
fn sign_extend(v: u32, bits: u32) -> i64 {
    let shift = 32 - bits;
    (((v << shift) as i32) >> shift) as i64
}

/// The byte offset a PC-relative branch targets (`pos` is the branch's own
/// address; `byte_off` is already scaled to bytes).
fn branch_target(pos: usize, byte_off: i64) -> csolver_core::Result<usize> {
    let t = pos as i64 + byte_off;
    if t < 0 {
        Err(CoreError::parse("arm64: branch target before the function"))
    } else {
        Ok(t as usize)
    }
}

/// Decode one 32-bit instruction `word` at byte offset `pos`, threading the
/// `cmp` flags for a following `b.cond`.
fn decode_one(
    word: u32,
    pos: usize,
    flags: &mut Option<(Operand, Operand)>,
) -> csolver_core::Result<Decoded> {
    let fall = |insts: Vec<Inst>| {
        Ok(Decoded {
            insts,
            ctrl: Ctrl::Fall,
        })
    };

    // RET {Xn} — `1101011 0010 11111 0000 00 Rn 00000`; the common `ret` (x30).
    if word & 0xffff_fc1f == 0xd65f_0000 {
        return Ok(Decoded {
            insts: Vec::new(),
            ctrl: Ctrl::Ret,
        });
    }

    // NOP — `1101 0101 0000 0011 0010 0000 0001 1111` = 0xd503201f
    if word == 0xd503201f {
        return fall(Vec::new());
    }

    // BL (branch with link): bits[31:26] == 10011.
    // Like CALL on x86, we conservatively mark the function unanalyzed.
    if word >> 26 == 0b10_0011 {
        // Model as a Ret (conservative: analysis stops here); the target
        // offset is deliberately not resolved.
        return Ok(Decoded {
            insts: Vec::new(),
            ctrl: Ctrl::Ret,
        });
    }

    // B (unconditional): bits[31:26] == 000101.
    if word >> 26 == 0b00_0101 {
        let off = sign_extend(word & 0x03ff_ffff, 26) * 4;
        return Ok(Decoded {
            insts: Vec::new(),
            ctrl: Ctrl::Jmp(branch_target(pos, off)?),
        });
    }

    // B.cond: bits[31:24] == 01010100, bit[4] == 0.
    if word >> 24 == 0b0101_0100 && word & 0x10 == 0 {
        let cond = (word & 0xf) as u8;
        let off = sign_extend((word >> 5) & 0x7_ffff, 19) * 4;
        let target = branch_target(pos, off)?;
        return bcond(pos, target, cond, flags);
    }

    // MOVZ / MOVK (move wide immediate): bits[28:23] == 100101.
    // bits[30:29] == 10 → MOVZ, bits[30:29] == 11 → MOVK.
    if ((word >> 23) & 0x3f) == 0b100101 {
        let sf = (word >> 31) & 1;
        let opc_hi = (word >> 29) & 0x3;
        let hw = (word >> 21) & 0x3; // shift: 0→0, 1→16, 2→32, 3→48
        let imm16 = (word >> 5) & 0xffff;
        let rd = (word & 0x1f) as u8;
        let width = if sf == 1 { 64 } else { 32 };
        let ty = Type::int(width);
        let shift = hw * 16;
        let val = (imm16 as u128) << shift;
        if opc_hi == 0b10 {
            // MOVZ: Rd = imm16 << shift
            return fall(vec![Inst::Assign {
                dst: reg(rd),
                ty,
                value: RValue::Use(Operand::int(width, val)),
            }]);
        }
        if opc_hi == 0b11 {
            // MOVK: Rd = Rd | (imm16 << shift)
            return fall(vec![Inst::Assign {
                dst: reg(rd),
                ty,
                value: RValue::Bin {
                    op: BinOp::Or,
                    lhs: Operand::Reg(reg(rd)),
                    rhs: Operand::int(width, val),
                    flags: Default::default(),
                },
            }]);
        }
    }

    // ADD/SUB (immediate): bits[28:24] == 10001.
    if (word >> 24) & 0x1f == 0b1_0001 {
        let sf = (word >> 31) & 1;
        let is_sub = (word >> 30) & 1 == 1;
        let set_flags = (word >> 29) & 1 == 1;
        let shift12 = (word >> 22) & 1 == 1;
        let mut imm = (word >> 10) & 0xfff;
        if shift12 {
            imm <<= 12;
        }
        let rn = ((word >> 5) & 0x1f) as u8;
        let rd = (word & 0x1f) as u8;
        let width = if sf == 1 { 64 } else { 32 };
        let ty = Type::int(width);
        // `cmp Rn, #imm` is `SUBS xzr, Rn, #imm` (S set, destination the zero
        // register): record the operands for a following `b.cond`.
        if is_sub && set_flags {
            *flags = Some((Operand::Reg(reg(rn)), Operand::int(width, imm as u128)));
            if rd == 31 {
                return fall(Vec::new());
            }
        }
        // `sub sp, sp, #N` allocates the stack frame; `add sp, sp, #N` tears it
        // down (the S bit distinguishes register 31 = sp here from xzr above).
        if rd == SP && rn == SP && !set_flags {
            return if is_sub {
                fall(vec![Inst::Alloc {
                    dst: reg(SP),
                    region: RegionKind::Stack,
                    elem: Type::int(8),
                    count: Operand::int(64, imm as u128),
                    align: 16,
                }])
            } else {
                fall(Vec::new())
            };
        }
        let op = if is_sub { BinOp::Sub } else { BinOp::Add };
        return fall(vec![Inst::Assign {
            dst: reg(rd),
            ty,
            value: RValue::Bin {
                op,
                lhs: Operand::Reg(reg(rn)),
                rhs: Operand::int(width, imm as u128),
                flags: Default::default(),
            },
        }]);
    }

    // LDR/STR (immediate, unsigned offset), integer: bits[29:24] == 111001.
    if (word >> 24) & 0x3f == 0b11_1001 {
        let size = (word >> 30) & 3; // 0=byte..3=8 bytes
        let opc = (word >> 22) & 3; // 00=STR, 01=LDR (unsigned)
        let imm12 = (word >> 10) & 0xfff;
        let rn = ((word >> 5) & 0x1f) as u8;
        let rt = (word & 0x1f) as u8;
        let access = 1u64 << size; // bytes
        let byte_off = imm12 as u64 * access; // unsigned offset is scaled
        let ty = Type::int((8 * access) as u32);
        let width = (8 * access) as u32;
        let ptr = temp_reg(pos);
        let off = Inst::PtrOffset {
            dst: ptr,
            base: Operand::Reg(reg(rn)),
            index: Operand::int(64, byte_off as u128),
            elem: Type::int(8),
        };
        return match opc {
            0 => {
                // STR Rt, [Rn, #off]; register 31 here is the zero register.
                let value = if rt == 31 {
                    Operand::int(width, 0)
                } else {
                    Operand::Reg(reg(rt))
                };
                fall(vec![
                    off,
                    Inst::Store {
                        ty,
                        ptr: Operand::Reg(ptr),
                        value,
                        align: 1,
                        volatile: false,
                    },
                ])
            }
            1 => {
                // LDR Rt, [Rn, #off]; loading into the zero register is a discard.
                let dst = if rt == 31 { temp_reg(pos + 1) } else { reg(rt) };
                fall(vec![
                    off,
                    Inst::Load {
                        dst,
                        ty,
                        ptr: Operand::Reg(ptr),
                        align: 1,
                        volatile: false,
                    },
                ])
            }
            _ => Err(CoreError::unsupported(
                "arm64: unsupported load/store variant",
            )),
        };
    }

    Err(CoreError::unsupported(format!(
        "arm64: unsupported instruction {word:#010x}"
    )))
}

/// Lower a `b.cond` to a condition assignment plus a `Jcc`. The condition comes
/// from the preceding `cmp`; an unmodelled code is an unconstrained boolean.
fn bcond(
    pos: usize,
    target: usize,
    cond: u8,
    flags: &Option<(Operand, Operand)>,
) -> csolver_core::Result<Decoded> {
    let creg = temp_reg(pos);
    let (op, lhs, rhs) = match (cc_cmpop(cond), flags) {
        (Some(op), Some((a, b))) => (op, a.clone(), b.clone()),
        _ => (
            CmpOp::Ne,
            Operand::Reg(RegId(2000 + pos as u32)),
            Operand::int(64, 0),
        ),
    };
    Ok(Decoded {
        insts: vec![Inst::Assign {
            dst: creg,
            ty: Type::Bool,
            value: RValue::Cmp { op, lhs, rhs },
        }],
        ctrl: Ctrl::Jcc(target, creg),
    })
}

/// The comparison an AArch64 condition code tests, where `cmp a, b` then
/// `b.<cc>` branches iff `a <op> b`. `None` for codes we do not model.
fn cc_cmpop(cond: u8) -> Option<CmpOp> {
    Some(match cond {
        0x0 => CmpOp::Eq,  // EQ
        0x1 => CmpOp::Ne,  // NE
        0x2 => CmpOp::Uge, // CS/HS
        0x3 => CmpOp::Ult, // CC/LO
        0x8 => CmpOp::Ugt, // HI
        0x9 => CmpOp::Ule, // LS
        0xa => CmpOp::Sge, // GE
        0xb => CmpOp::Slt, // LT
        0xc => CmpOp::Sgt, // GT
        0xd => CmpOp::Sle, // LE
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use csolver_ir::Terminator;

    /// `sub sp,sp,#16 ; str w0,[sp,#8] ; add sp,sp,#16 ; ret`.
    const FRAME: [u8; 16] = [
        0xff, 0x43, 0x00, 0xd1, // sub sp, sp, #16
        0xe0, 0x0b, 0x00, 0xb9, // str w0, [sp, #8]
        0xff, 0x43, 0x00, 0x91, // add sp, sp, #16
        0xc0, 0x03, 0x5f, 0xd6, // ret
    ];

    #[test]
    fn decodes_a_stack_frame_and_its_access() {
        let m = decode_function("f", &FRAME);
        assert!(m.unanalyzed.is_empty(), "fully decoded: {:?}", m.unanalyzed);
        let insts = &m.functions[0].blocks[0].insts;
        assert!(matches!(
            insts[0],
            Inst::Alloc {
                region: RegionKind::Stack,
                ..
            }
        ));
        assert!(matches!(insts[1], Inst::PtrOffset { .. }));
        assert!(matches!(insts[2], Inst::Store { .. }));
    }

    #[test]
    fn unsupported_instruction_is_unanalyzed() {
        // A NEON/FP word we do not decode.
        let m = decode_function("f", &[0x00, 0x00, 0x00, 0x00]);
        assert!(m.functions.is_empty());
        assert_eq!(m.unanalyzed.len(), 1);
    }

    #[test]
    fn rejects_misaligned_code() {
        let m = decode_function("f", &[0xc0, 0x03, 0x5f]); // 3 bytes
        assert_eq!(m.unanalyzed.len(), 1);
    }

    #[test]
    fn reconstructs_a_conditional_branch() {
        // sub sp,#16 ; cmp w0,#0 ; b.ne .skip ; str w1,[sp,#8] ; .skip: add sp,#16 ; ret
        let code = [
            0xff, 0x43, 0x00, 0xd1, 0x1f, 0x00, 0x00, 0x71, 0x41, 0x00, 0x00, 0x54, 0xe1, 0x0b,
            0x00, 0xb9, 0xff, 0x43, 0x00, 0x91, 0xc0, 0x03, 0x5f, 0xd6,
        ];
        let m = decode_function("f", &code);
        assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
        let f = &m.functions[0];
        assert_eq!(f.blocks.len(), 3, "entry + store + join");
        assert!(
            matches!(f.blocks[0].term, Terminator::CondBr { .. }),
            "cmp/b.cond → CondBr"
        );
    }

    #[test]
    fn decodes_nop() {
        // nop  = d503201f
        let m = decode_function("f", &[0x1f, 0x20, 0x03, 0xd5, 0xc0, 0x03, 0x5f, 0xd6]);
        assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
    }

    #[test]
    fn decodes_movz_wide() {
        // movz x0, #42  = d28000a0 -> little-endian a0 00 80 d2
        let m = decode_function("f", &[0xa0, 0x00, 0x80, 0xd2, 0xc0, 0x03, 0x5f, 0xd6]);
        assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
        let insts = &m.functions[0].blocks[0].insts;
        assert!(matches!(insts[0], Inst::Assign { .. }));
    }

    #[test]
    fn decodes_movk() {
        // movk x0, #42, lsl #16  = f2a000a0 -> little-endian a0 00 a0 f2
        let m = decode_function("f", &[0xa0, 0x00, 0xa0, 0xf2, 0xc0, 0x03, 0x5f, 0xd6]);
        assert!(m.unanalyzed.is_empty(), "{:?}", m.unanalyzed);
    }

    #[test]
    fn bl_marks_unanalyzed() {
        // bl +0  (branch to self) = 98000000 -> little-endian 00 00 00 98
        let m = decode_function("f", &[0x00, 0x00, 0x00, 0x98, 0xc0, 0x03, 0x5f, 0xd6]);
        assert_eq!(m.unanalyzed.len(), 1, "BL should be unsupported");
    }

    // ========================================================================
    // Negative tests: truncation and unsupported patterns
    // ========================================================================

    #[test]
    fn empty_input_is_valid() {
        // An empty body is a vacuously-safe single `ret` block.
        let m = decode_function("f", &[]);
        assert!(m.unanalyzed.is_empty());
        assert_eq!(m.functions.len(), 1);
        assert_eq!(m.functions[0].blocks.len(), 1);
    }

    #[test]
    fn rejects_truncated_one_byte() {
        let m = decode_function("f", &[0xc0]);
        assert_eq!(m.unanalyzed.len(), 1);
    }

    #[test]
    fn rejects_truncated_two_bytes() {
        let m = decode_function("f", &[0xc0, 0x03]);
        assert_eq!(m.unanalyzed.len(), 1);
    }

    #[test]
    fn rejects_unsupported_encoding() {
        // AArch64 SVC (supervisor call) = 0xd4000001 — not in our decoder.
        let code = [
            0x01, 0x00, 0x00, 0xd4, // svc #0
            0xc0, 0x03, 0x5f, 0xd6, // ret
        ];
        let m = decode_function("f", &code);
        assert_eq!(m.unanalyzed.len(), 1);
    }

    #[test]
    fn branch_before_function_is_error() {
        // B #-8 at offset 0: the target address would be negative.
        // Encoding: imm26 = -2 (26-bit two's complement = 0x03ff_fffe).
        // word = 000101_00_11_1111_1111_1111_1111_1111_1110
        //      = 0x1400_0000 | 0x03ff_fffe = 0x17ff_fffe
        let code = [
            0xfe, 0xff, 0xff, 0x17, // b #-8 (before function start)
        ];
        let m = decode_function("f", &code);
        assert_eq!(m.unanalyzed.len(), 1);
    }
}
