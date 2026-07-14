use super::*;

/// Parse a VEX prefix at `*p`, advancing `p` past it. `is_two_byte` selects the
/// C5 (2-byte) form; otherwise the C4 (3-byte) form.
///
/// Real x86-64 VEX layout (all "~"-marked fields are stored inverted):
/// - 2-byte VEX (`C5 b`): one payload byte `b = [~R vvvv L pp]`; the map is
///   implicitly `0F` (mmmmm=1) and `W`/`X`/`B` are 0 (unextended).
/// - 3-byte VEX (`C4 b1 b2`): `b1 = [~R ~X ~B mmmmm(5)]`, `b2 = [W ~vvvv L pp]`.
///
/// The `~R/~X/~B` bits are complements (0 → the corresponding register field is
/// extended, i.e. r8/xmm8+), and `~vvvv` is the 1's-complement of the third
/// operand's register number. Test vectors are taken from a real assembler
/// (`llvm-mc -triple=x86_64 --show-encoding`).
pub(crate) fn parse_vex(
    code: &[u8],
    p: &mut usize,
    is_two_byte: bool,
) -> csolver_core::Result<VexInfo> {
    // Advance past the C4/C5 lead byte.
    *p += 1;
    if is_two_byte {
        // C5: single payload byte [~R vvvv L pp]. Map is implicitly 0F; W=0.
        let b = *code
            .get(*p)
            .ok_or_else(|| CoreError::parse("x86: truncated 2-byte VEX prefix (C5)"))?;
        *p += 1;
        Ok(VexInfo {
            vvvv: (!(b >> 3)) & 0xf,
            l: (b & 0x04) != 0,
            pp: b & 0x03,
            mmmmm: 1,
            w: false,
            rex_r: (b & 0x80) == 0, // ~R: 0 → extended
            rex_x: false,
            rex_b: false,
        })
    } else {
        // C4: b1 = [~R ~X ~B mmmmm(5)], b2 = [W ~vvvv L pp].
        let b1 = *code
            .get(*p)
            .ok_or_else(|| CoreError::parse("x86: truncated 3-byte VEX prefix (C4 byte 1)"))?;
        *p += 1;
        let b2 = *code
            .get(*p)
            .ok_or_else(|| CoreError::parse("x86: truncated 3-byte VEX prefix (C4 byte 2)"))?;
        *p += 1;
        let mmmmm = b1 & 0x1f;
        if mmmmm == 0 || mmmmm > 3 {
            return Err(CoreError::unsupported(format!(
                "x86: unsupported VEX.mmmmm {mmmmm}"
            )));
        }
        Ok(VexInfo {
            vvvv: (!(b2 >> 3)) & 0xf,
            l: (b2 & 0x04) != 0,
            pp: b2 & 0x03,
            mmmmm,
            w: (b2 & 0x80) != 0,
            rex_r: (b1 & 0x80) == 0, // ~R: 0 → extended
            rex_x: (b1 & 0x40) == 0, // ~X
            rex_b: (b1 & 0x20) == 0, // ~B
        })
    }
}

/// Build an XMM register operand at `width` (typically DQ for 128-bit).
pub(crate) fn xmm_op(r: XmmReg, width: Width) -> X86Operand {
    X86Operand::Xmm(r, width)
}

/// Read an XMM-or-memory operand from ModRM, advancing `p`. Uses `pp_map` to
/// determine the mnemonic prefix (none/66/F3/F2 selects packed/scalar).
pub(crate) fn read_xmm_rm_operand(
    code: &[u8],
    p: &mut usize,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    width: Width,
) -> csolver_core::Result<(X86Operand, TypedModRm)> {
    let m = read_modrm(code, *p, rex_r, rex_b)?;
    *p += 1;
    if m.mode == 0b11 {
        let r = XmmReg::from_idx(m.rm).ok_or_else(|| {
            CoreError::parse(format!("x86: invalid XMM register {} in SSE operand", m.rm))
        })?;
        Ok((X86Operand::Xmm(r, width), m))
    } else {
        let mem = read_mem(code, p, &m, rex_x, rex_b)?;
        Ok((X86Operand::Mem(mem, width), m))
    }
}

/// Decode a legacy-SSE or VEX.128-encoded instruction from the 0F opcode map.
/// `pp` encodes the mandatory prefix: 0=none (packed single), 1=66 (packed double),
/// 2=F3 (scalar single), 3=F2 (scalar double).
/// `op` is the second opcode byte (the byte after 0F).
pub(crate) fn decode_sse_0f_op(
    op: u8,
    code: &[u8],
    p: &mut usize,
    pp: u8,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
) -> csolver_core::Result<(Instruction, usize)> {
    let decode_reg_mem =
        |code: &[u8], p: &mut usize| -> csolver_core::Result<(X86Operand, TypedModRm)> {
            read_xmm_rm_operand(code, p, rex_r, rex_x, rex_b, Width::DQ)
        };
    match op {
        // 0F 10: MOVUPS (pp=0), MOVSS (pp=2), MOVSD (pp=3), MOVUPD (pp=1)
        0x10 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid dst XMM register in MOV*"))?;
            let inst = match pp {
                0 => Instruction::Movups(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Movupd(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Movss(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Movsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 10")),
            };
            Ok((inst, *p))
        }
        // 0F 11: MOVUPS store (pp=0), MOVSS store (pp=2), MOVSD store (pp=3), MOVUPD store (pp=1)
        0x11 => {
            let (dst, m) = decode_reg_mem(code, p)?;
            let src = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid src XMM register in MOV*"))?;
            let inst = match pp {
                0 => Instruction::Movups(dst, xmm_op(src, Width::DQ)),
                1 => Instruction::Movupd(dst, xmm_op(src, Width::DQ)),
                2 => Instruction::Movss(dst, xmm_op(src, Width::DQ)),
                3 => Instruction::Movsd(dst, xmm_op(src, Width::DQ)),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 11")),
            };
            Ok((inst, *p))
        }
        // 0F 28: MOVAPS (pp=0), MOVAPD (pp=1)
        0x28 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid dst XMM register in MOVAP*"))?;
            match pp {
                0 => Ok((Instruction::Movaps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Movapd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 28")),
            }
        }
        // 0F 29: MOVAPS store (pp=0), MOVAPD store (pp=1)
        0x29 => {
            let (dst, m) = decode_reg_mem(code, p)?;
            let src = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid src XMM register in MOVAP*"))?;
            match pp {
                0 => Ok((Instruction::Movaps(dst, xmm_op(src, Width::DQ)), *p)),
                1 => Ok((Instruction::Movapd(dst, xmm_op(src, Width::DQ)), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 29")),
            }
        }
        // 0F 2E: UCOMISS (pp=0), UCOMISD (pp=1)
        0x2e => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in UCOMIS*"))?;
            match pp {
                0 => Ok((Instruction::Ucomiss(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Ucomisd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 2E")),
            }
        }
        // 0F 2F: COMISS (pp=0), COMISD (pp=1)
        0x2f => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in COMIS*"))?;
            match pp {
                0 => Ok((Instruction::Comiss(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Comisd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 2F")),
            }
        }
        // 0F 51: SQRTPS (pp=0), SQRTSS (pp=2), SQRTPD (pp=1), SQRTSD (pp=3)
        0x51 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in SQRT*"))?;
            let inst = match pp {
                0 => Instruction::Sqrtps(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Sqrtss(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Sqrtpd(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Sqrtsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 51")),
            };
            Ok((inst, *p))
        }
        // 0F 54: ANDPS (pp=0), ANDPD (pp=1)
        0x54 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in AND*"))?;
            match pp {
                0 => Ok((Instruction::Andps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Andpd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 54")),
            }
        }
        // 0F 55: ANDNPS (pp=0), ANDNPD (pp=1)
        0x55 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in ANDN*"))?;
            match pp {
                0 => Ok((Instruction::Andnps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Andnpd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 55")),
            }
        }
        // 0F 56: ORPS (pp=0), ORPD (pp=1)
        0x56 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in OR*"))?;
            match pp {
                0 => Ok((Instruction::Orps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Orpd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 56")),
            }
        }
        // 0F 57: XORPS (pp=0), XORPD (pp=1)
        0x57 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in XOR*"))?;
            match pp {
                0 => Ok((Instruction::Xorps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Xorpd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 57")),
            }
        }
        // 0F 58: ADDPS (pp=0), ADDSS (pp=2), ADDPD (pp=1), ADDSD (pp=3)
        0x58 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in ADD*"))?;
            let inst = match pp {
                0 => Instruction::Addps(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Addss(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Addpd(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Addsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 58")),
            };
            Ok((inst, *p))
        }
        // 0F 59: MULPS (pp=0), MULSS (pp=2), MULPD (pp=1), MULSD (pp=3)
        0x59 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in MUL*"))?;
            let inst = match pp {
                0 => Instruction::Mulps(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Mulss(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Mulpd(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Mulsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 59")),
            };
            Ok((inst, *p))
        }
        // 0F 5B: CVTDQ2PS (pp=0), CVTTPS2DQ (pp=2), CVTPS2DQ (pp=1)
        0x5b => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in CVT*"))?;
            match pp {
                0 => Ok((Instruction::Cvtdq2ps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Cvtps2dq(xmm_op(dst, Width::DQ), src), *p)),
                2 => Ok((Instruction::Cvttps2dq(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 5B")),
            }
        }
        // 0F 5C: SUBPS (pp=0), SUBSS (pp=2), SUBPD (pp=1), SUBSD (pp=3)
        0x5c => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in SUB*"))?;
            let inst = match pp {
                0 => Instruction::Subps(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Subss(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Subpd(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Subsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 5C")),
            };
            Ok((inst, *p))
        }
        // 0F 5D: MINPS (pp=0), MINSS (pp=2), MINPD (pp=1), MINSD (pp=3)
        0x5d => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in MIN*"))?;
            let inst = match pp {
                0 => Instruction::Minps(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Minss(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Minpd(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Minsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 5D")),
            };
            Ok((inst, *p))
        }
        // 0F 5E: DIVPS (pp=0), DIVSS (pp=2), DIVPD (pp=1), DIVSD (pp=3)
        0x5e => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in DIV*"))?;
            let inst = match pp {
                0 => Instruction::Divps(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Divss(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Divpd(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Divsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 5E")),
            };
            Ok((inst, *p))
        }
        // 0F 5F: MAXPS (pp=0), MAXSS (pp=2), MAXPD (pp=1), MAXSD (pp=3)
        0x5f => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in MAX*"))?;
            let inst = match pp {
                0 => Instruction::Maxps(xmm_op(dst, Width::DQ), src),
                2 => Instruction::Maxss(xmm_op(dst, Width::DQ), src),
                1 => Instruction::Maxpd(xmm_op(dst, Width::DQ), src),
                3 => Instruction::Maxsd(xmm_op(dst, Width::DQ), src),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 5F")),
            };
            Ok((inst, *p))
        }
        // 0F 14: UNPCKLPS (pp=0), UNPCKLPD (pp=1)
        0x14 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in UNPCKL*"))?;
            match pp {
                0 => Ok((Instruction::Unpcklps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Unpcklpd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 14")),
            }
        }
        // 0F 15: UNPCKHPS (pp=0), UNPCKHPD (pp=1)
        0x15 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in UNPCKH*"))?;
            match pp {
                0 => Ok((Instruction::Unpckhps(xmm_op(dst, Width::DQ), src), *p)),
                1 => Ok((Instruction::Unpckhpd(xmm_op(dst, Width::DQ), src), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F 15")),
            }
        }
        // 0F C2: CMPPS (pp=0), CMPSS (pp=2), CMPPD (pp=1), CMPSD (pp=3) — all take imm8
        0xc2 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in CMP*"))?;
            let imm = code
                .get(*p)
                .copied()
                .ok_or_else(|| CoreError::parse("x86: truncated CMP immediate"))?;
            *p += 1;
            let inst = match pp {
                0 => Instruction::Cmpps(xmm_op(dst, Width::DQ), src, imm),
                2 => Instruction::Cmpss(xmm_op(dst, Width::DQ), src, imm),
                1 => Instruction::Cmppd(xmm_op(dst, Width::DQ), src, imm),
                3 => Instruction::Cmpsd(xmm_op(dst, Width::DQ), src, imm),
                _ => return Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F C2")),
            };
            Ok((inst, *p))
        }
        // 0F C6: SHUFPS (pp=0), SHUFPD (pp=1) — take imm8
        0xc6 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in SHUF*"))?;
            let imm = code
                .get(*p)
                .copied()
                .ok_or_else(|| CoreError::parse("x86: truncated SHUF immediate"))?;
            *p += 1;
            match pp {
                0 => Ok((Instruction::Shufps(xmm_op(dst, Width::DQ), src, imm), *p)),
                1 => Ok((Instruction::Shufpd(xmm_op(dst, Width::DQ), src, imm), *p)),
                _ => Err(CoreError::unsupported("x86: unsupported VEX.pp for 0F C6")),
            }
        }
        // 0F D4: PADDQ dst, src (66, SSE2)
        0xd4 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PADDQ"))?;
            Ok((Instruction::Paddq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F DB: PAND dst, src (66, SSE2)
        0xdb if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PAND"))?;
            Ok((Instruction::Pand(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F EB: POR dst, src (66, SSE2)
        0xeb if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in POR"))?;
            Ok((Instruction::Por(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F EF: PXOR dst, src (66, SSE2)
        0xef if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PXOR"))?;
            Ok((Instruction::Pxor(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F FB: PSUBQ dst, src (66, SSE2)
        0xfb if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PSUBQ"))?;
            Ok((Instruction::Psubq(xmm_op(dst, Width::DQ), src), *p))
        }
        _ => Err(CoreError::unsupported(format!(
            "x86: unsupported VEX.128 opcode 0f {:02x}",
            op
        ))),
    }
}
