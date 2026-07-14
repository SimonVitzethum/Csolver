use super::*;

/// VEX.128 wrapper: reads the opcode byte and dispatches to `decode_sse_0f_op`.
pub(crate) fn decode_vex_0f(
    code: &[u8],
    p: &mut usize,
    vex: VexInfo,
) -> csolver_core::Result<(Instruction, usize)> {
    let op = *code
        .get(*p)
        .ok_or_else(|| CoreError::parse(format!("x86: truncated VEX opcode at offset {}", *p)))?;
    *p += 1;
    decode_sse_0f_op(op, code, p, vex.pp, vex.rex_r, vex.rex_x, vex.rex_b)
}

/// Decode VEX.128-encoded instructions from the 0F38 opcode map (VEX.mmmmm=2).
/// Most instructions require pp=1 (66 prefix). SSSE3 and SSE4.1 instructions.
pub(crate) fn decode_vex_0f38(
    code: &[u8],
    p: &mut usize,
    vex: VexInfo,
) -> csolver_core::Result<(Instruction, usize)> {
    let op = *code.get(*p).ok_or_else(|| {
        CoreError::parse(format!("x86: truncated VEX 0F38 opcode at offset {}", *p))
    })?;
    *p += 1;
    let pp = vex.pp;
    let (rex_r, rex_x, rex_b) = (vex.rex_r, vex.rex_x, vex.rex_b);
    let decode_reg_mem =
        |code: &[u8], p: &mut usize| -> csolver_core::Result<(X86Operand, TypedModRm)> {
            read_xmm_rm_operand(code, p, rex_r, rex_x, rex_b, Width::DQ)
        };
    // Most 0F38 instructions require 66 prefix (pp=1).
    match op {
        // 0F38 00: PSHUFB dst, src (SSSE3)
        0x00 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PSHUFB"))?;
            Ok((Instruction::Pshufb(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 01: PHADDW dst, src (SSSE3)
        0x01 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PHADDW"))?;
            Ok((Instruction::Phaddw(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 02: PHADDD dst, src (SSSE3)
        0x02 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PHADDD"))?;
            Ok((Instruction::Phaddd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 03: PHADDSW dst, src (SSSE3)
        0x03 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PHADDSW"))?;
            Ok((Instruction::Phaddsw(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 1C: PABSB dst, src (SSSE3)
        0x1c if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PABSB"))?;
            Ok((Instruction::Pabsb(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 1D: PABSW dst, src (SSSE3)
        0x1d if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PABSW"))?;
            Ok((Instruction::Pabsw(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 1E: PABSD dst, src (SSSE3)
        0x1e if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PABSD"))?;
            Ok((Instruction::Pabsd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 20: PMOVSXBW dst, src (SSE4.1)
        0x20 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVSXBW"))?;
            Ok((Instruction::Pmovsxbw(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 21: PMOVSXBD dst, src (SSE4.1)
        0x21 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVSXBD"))?;
            Ok((Instruction::Pmovsxbd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 22: PMOVSXBQ dst, src (SSE4.1)
        0x22 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVSXBQ"))?;
            Ok((Instruction::Pmovsxbq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 23: PMOVSXWD dst, src (SSE4.1)
        0x23 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVSXWD"))?;
            Ok((Instruction::Pmovsxwd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 24: PMOVSXWQ dst, src (SSE4.1)
        0x24 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVSXWQ"))?;
            Ok((Instruction::Pmovsxwq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 25: PMOVSXDQ dst, src (SSE4.1)
        0x25 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVSXDQ"))?;
            Ok((Instruction::Pmovsxdq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 28: PMULDQ dst, src (SSE4.1)
        0x28 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMULDQ"))?;
            Ok((Instruction::Pmuldq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 29: PCMPEQQ dst, src (SSE4.2)
        0x29 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PCMPEQQ"))?;
            Ok((Instruction::Pcmpeqq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 30: PMOVZXBW dst, src (SSE4.1)
        0x30 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVZXBW"))?;
            Ok((Instruction::Pmovzxbw(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 31: PMOVZXBD dst, src (SSE4.1)
        0x31 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVZXBD"))?;
            Ok((Instruction::Pmovzxbd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 32: PMOVZXBQ dst, src (SSE4.1)
        0x32 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVZXBQ"))?;
            Ok((Instruction::Pmovzxbq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 33: PMOVZXWD dst, src (SSE4.1)
        0x33 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVZXWD"))?;
            Ok((Instruction::Pmovzxwd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 34: PMOVZXWQ dst, src (SSE4.1)
        0x34 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVZXWQ"))?;
            Ok((Instruction::Pmovzxwq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 35: PMOVZXDQ dst, src (SSE4.1)
        0x35 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMOVZXDQ"))?;
            Ok((Instruction::Pmovzxdq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 37: PCMPGTQ dst, src (SSE4.2)
        0x37 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PCMPGTQ"))?;
            Ok((Instruction::Pcmpgtq(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 38: PMINSB dst, src (SSE4.1)
        0x38 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMINSB"))?;
            Ok((Instruction::Pminsb(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 39: PMINSD dst, src (SSE4.1)
        0x39 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMINSD"))?;
            Ok((Instruction::Pminsd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 3A: PMINUW dst, src (SSE4.1)
        0x3a if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMINUW"))?;
            Ok((Instruction::Pminuw(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 3B: PMINUD dst, src (SSE4.1)
        0x3b if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMINUD"))?;
            Ok((Instruction::Pminud(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 3C: PMAXSB dst, src (SSE4.1)
        0x3c if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMAXSB"))?;
            Ok((Instruction::Pmaxsb(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 3D: PMAXSD dst, src (SSE4.1)
        0x3d if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMAXSD"))?;
            Ok((Instruction::Pmaxsd(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 3E: PMAXUW dst, src (SSE4.1)
        0x3e if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMAXUW"))?;
            Ok((Instruction::Pmaxuw(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 3F: PMAXUD dst, src (SSE4.1)
        0x3f if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMAXUD"))?;
            Ok((Instruction::Pmaxud(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 40: PMULLD dst, src (SSE4.1)
        0x40 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PMULLD"))?;
            Ok((Instruction::Pmulld(xmm_op(dst, Width::DQ), src), *p))
        }
        // 0F38 41: PHMINPOSUW dst, src (SSE4.1)
        0x41 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PHMINPOSUW"))?;
            Ok((Instruction::Phminposuw(xmm_op(dst, Width::DQ), src), *p))
        }
        _ => Err(CoreError::unsupported(format!(
            "x86: unsupported VEX.128 0F38 opcode {:02x} pp={}",
            op, pp
        ))),
    }
}

/// Decode VEX.128-encoded instructions from the 0F3A opcode map (VEX.mmmmm=3).
/// All require pp=1 (66 prefix). SSE4.1 and SSSE3 instructions with an imm8.
pub(crate) fn decode_vex_0f3a(
    code: &[u8],
    p: &mut usize,
    vex: VexInfo,
) -> csolver_core::Result<(Instruction, usize)> {
    let op = *code.get(*p).ok_or_else(|| {
        CoreError::parse(format!("x86: truncated VEX 0F3A opcode at offset {}", *p))
    })?;
    *p += 1;
    let pp = vex.pp;
    let rex_w = vex.w;
    let (rex_r, rex_x, rex_b) = (vex.rex_r, vex.rex_x, vex.rex_b);
    let decode_reg_mem =
        |code: &[u8], p: &mut usize| -> csolver_core::Result<(X86Operand, TypedModRm)> {
            read_xmm_rm_operand(code, p, rex_r, rex_x, rex_b, Width::DQ)
        };
    let read_imm8 = |code: &[u8], p: &mut usize| -> csolver_core::Result<u8> {
        let imm = code
            .get(*p)
            .copied()
            .ok_or_else(|| CoreError::parse("x86: truncated 0F3A immediate"))?;
        *p += 1;
        Ok(imm)
    };
    match op {
        // 0F3A 08: ROUNDPS dst, src, imm (SSE4.1)
        0x08 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in ROUNDPS"))?;
            let imm = read_imm8(code, p)?;
            Ok((Instruction::Roundps(xmm_op(dst, Width::DQ), src, imm), *p))
        }
        // 0F3A 09: ROUNDPD dst, src, imm (SSE4.1)
        0x09 if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in ROUNDPD"))?;
            let imm = read_imm8(code, p)?;
            Ok((Instruction::Roundpd(xmm_op(dst, Width::DQ), src, imm), *p))
        }
        // 0F3A 0A: ROUNDSS dst, src, imm (SSE4.1)
        0x0a if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in ROUNDSS"))?;
            let imm = read_imm8(code, p)?;
            Ok((Instruction::Roundss(xmm_op(dst, Width::DQ), src, imm), *p))
        }
        // 0F3A 0B: ROUNDSD dst, src, imm (SSE4.1)
        0x0b if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in ROUNDSD"))?;
            let imm = read_imm8(code, p)?;
            Ok((Instruction::Roundsd(xmm_op(dst, Width::DQ), src, imm), *p))
        }
        // 0F3A 0F: PALIGNR dst, src, imm (SSSE3)
        0x0f if pp == 1 => {
            let (src, m) = decode_reg_mem(code, p)?;
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PALIGNR"))?;
            let imm = read_imm8(code, p)?;
            Ok((Instruction::Palignr(xmm_op(dst, Width::DQ), src, imm), *p))
        }
        // 0F3A 14: PEXTRB dst, src, imm (SSE4.1)
        0x14 if pp == 1 => {
            let m = read_modrm(code, *p, rex_r, false)?;
            *p += 1;
            let dst = if m.mode == 0b11 {
                // Register form: extract into GPR
                let reg = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid GPR in PEXTRB"))?;
                X86Operand::Reg(reg, Width::B)
            } else {
                let mem = read_mem(code, p, &m, false, rex_x)?;
                X86Operand::Mem(mem, Width::B)
            };
            let src = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PEXTRB"))?;
            let imm = read_imm8(code, p)?;
            Ok((Instruction::Pextrb(dst, xmm_op(src, Width::DQ), imm), *p))
        }
        // 0F3A 16: PEXTRD dst, src, imm (SSE4.1) / PEXTRQ dst, src, imm (REX.W)
        0x16 if pp == 1 => {
            let m = read_modrm(code, *p, rex_r, false)?;
            *p += 1;
            let is_q = rex_w;
            let width = if is_q { Width::Q } else { Width::D };
            let dst = if m.mode == 0b11 {
                let reg = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid GPR in PEXTR*"))?;
                X86Operand::Reg(reg, width)
            } else {
                let mem = read_mem(code, p, &m, false, rex_x)?;
                X86Operand::Mem(mem, width)
            };
            let src = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PEXTR*"))?;
            let imm = read_imm8(code, p)?;
            if is_q {
                Ok((Instruction::Pextrq(dst, xmm_op(src, Width::DQ), imm), *p))
            } else {
                Ok((Instruction::Pextrd(dst, xmm_op(src, Width::DQ), imm), *p))
            }
        }
        // 0F3A 20: PINSRB dst, src, imm (SSE4.1)
        0x20 if pp == 1 => {
            let m = read_modrm(code, *p, rex_r, false)?;
            *p += 1;
            let src = if m.mode == 0b11 {
                let reg = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid GPR in PINSRB"))?;
                X86Operand::Reg(reg, Width::B)
            } else {
                let mem = read_mem(code, p, &m, false, rex_x)?;
                X86Operand::Mem(mem, Width::B)
            };
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PINSRB"))?;
            let imm = read_imm8(code, p)?;
            Ok((Instruction::Pinsrb(xmm_op(dst, Width::DQ), src, imm), *p))
        }
        // 0F3A 22: PINSRD dst, src, imm (SSE4.1) / PINSRQ dst, src, imm (REX.W)
        0x22 if pp == 1 => {
            let m = read_modrm(code, *p, rex_r, false)?;
            *p += 1;
            let is_q = rex_w;
            let width = if is_q { Width::Q } else { Width::D };
            let src = if m.mode == 0b11 {
                let reg = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid GPR in PINSR*"))?;
                X86Operand::Reg(reg, width)
            } else {
                let mem = read_mem(code, p, &m, false, rex_x)?;
                X86Operand::Mem(mem, width)
            };
            let dst = XmmReg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid XMM register in PINSR*"))?;
            let imm = read_imm8(code, p)?;
            if is_q {
                Ok((Instruction::Pinsrq(xmm_op(dst, Width::DQ), src, imm), *p))
            } else {
                Ok((Instruction::Pinsrd(xmm_op(dst, Width::DQ), src, imm), *p))
            }
        }
        _ => Err(CoreError::unsupported(format!(
            "x86: unsupported VEX.128 0F3A opcode {:02x} pp={}",
            op, pp
        ))),
    }
}

// ============================================================================
// Low-level decode helpers for typed representation
// ============================================================================
