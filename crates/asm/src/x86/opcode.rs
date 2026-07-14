use super::*;

/// Decode the typed instruction after prefixes have been parsed.
#[allow(clippy::too_many_arguments)]
pub(crate) fn decode_typed_opcode(
    op: u8,
    code: &[u8],
    mut p: usize,
    rex_w: bool,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    _op_size: bool,
    width: Width,
    sse_pp: u8,
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
            let src = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid src register in ALU"))?;
            // The destination is a register (mod 11) or a memory operand (`<alu> [mem], r`).
            let dst = if m.mode == 0b11 {
                let d = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid dst register in ALU"))?;
                reg_op(d)
            } else {
                X86Operand::Mem(read_mem(code, &mut p, &m, rex_x, rex_b)?, width)
            };
            let inst = match op {
                0x31 => {
                    if m.mode == 0b11 && m.rm == m.reg {
                        // xor r, r → zero idiom
                        Instruction::Mov(dst, X86Operand::Imm(0))
                    } else {
                        Instruction::Xor(dst, reg_op(src))
                    }
                }
                0x01 => Instruction::Add(dst, reg_op(src)),
                0x29 => Instruction::Sub(dst, reg_op(src)),
                0x21 => Instruction::And(dst, reg_op(src)),
                0x09 => Instruction::Or(dst, reg_op(src)),
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
                Ok((
                    Instruction::Mov(X86Operand::Mem(mem, width), reg_op(src)),
                    p,
                ))
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
                Ok((
                    Instruction::Mov(reg_op(dst), X86Operand::Mem(mem, width)),
                    p,
                ))
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

        // Group 1 (0x80): ALU r/m8, imm8 (unsigned imm8).
        0x80 => {
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, Width::B)?;
            let imm = read_imm_u8(code, &mut p)?;
            let group_op = group1_op_from_modrm_reg(code, p - 2, rex_r, rex_b)?;
            let inst = match group_op {
                Group1Op::Add => Instruction::Add(operand, X86Operand::Imm(imm as u64)),
                Group1Op::Sub => Instruction::Sub(operand, X86Operand::Imm(imm as u64)),
                Group1Op::Cmp => Instruction::Cmp(operand, X86Operand::Imm(imm as u64)),
                Group1Op::And => Instruction::And(operand, X86Operand::Imm(imm as u64)),
                Group1Op::Or => Instruction::Or(operand, X86Operand::Imm(imm as u64)),
                Group1Op::Xor => Instruction::Xor(operand, X86Operand::Imm(imm as u64)),
                _ => {
                    return Err(CoreError::unsupported(
                        "x86: unsupported group-1 operation with imm8 (0x80)",
                    ))
                }
            };
            Ok((inst, p))
        }
        // Group 1 (0x81): ALU r/m, imm32 (sign-extended to operand width).
        0x81 => {
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, width)?;
            let imm = read_imm_i32(code, &mut p)? as u64;
            let group_op = group1_op_from_modrm_reg(code, p - 5, rex_r, rex_b)?;
            let inst = match group_op {
                Group1Op::Add => Instruction::Add(operand, X86Operand::Imm(imm)),
                Group1Op::Sub => Instruction::Sub(operand, X86Operand::Imm(imm)),
                Group1Op::Cmp => Instruction::Cmp(operand, X86Operand::Imm(imm)),
                Group1Op::And => Instruction::And(operand, X86Operand::Imm(imm)),
                Group1Op::Or => Instruction::Or(operand, X86Operand::Imm(imm)),
                Group1Op::Xor => Instruction::Xor(operand, X86Operand::Imm(imm)),
                _ => {
                    return Err(CoreError::unsupported(
                        "x86: unsupported group-1 operation with imm32",
                    ))
                }
            };
            Ok((inst, p))
        }
        // Group 1 (0x82/0x83): ALU r/m, imm8 (sign-extended to width).
        // 0x82 is an alias for 0x83 in 64-bit mode (but should not be emitted by
        // modern assemblers; we decode it identically).
        0x82 | 0x83 => {
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, width)?;
            let imm = read_imm_u8(code, &mut p)?;
            // Sign-extend imm8 to operand width.
            let imm = (imm as i8 as i64) as u64;
            let group_op = group1_op_from_modrm_reg(code, p - 2, rex_r, rex_b)?;
            let inst = match group_op {
                Group1Op::Add => Instruction::Add(operand, X86Operand::Imm(imm)),
                Group1Op::Sub => Instruction::Sub(operand, X86Operand::Imm(imm)),
                Group1Op::Cmp => Instruction::Cmp(operand, X86Operand::Imm(imm)),
                Group1Op::And => Instruction::And(operand, X86Operand::Imm(imm)),
                Group1Op::Or => Instruction::Or(operand, X86Operand::Imm(imm)),
                Group1Op::Xor => Instruction::Xor(operand, X86Operand::Imm(imm as u64)),
                _ => {
                    return Err(CoreError::unsupported(
                        "x86: unsupported group-1 operation with imm8",
                    ))
                }
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

        // push reg (0x50..0x57) — push register onto stack.
        0x50..=0x57 => {
            let r = Reg::from_idx((op - 0x50) | if rex_b { 8 } else { 0 })
                .ok_or_else(|| CoreError::parse("x86: invalid register in push"))?;
            Ok((Instruction::Push(reg_op(r)), p))
        }

        // pop reg (0x58..0x5f) — pop register from stack.
        0x58..=0x5f => {
            let r = Reg::from_idx((op - 0x58) | if rex_b { 8 } else { 0 })
                .ok_or_else(|| CoreError::parse("x86: invalid register in pop"))?;
            Ok((Instruction::Pop(reg_op(r)), p))
        }

        // push imm32 (0x68) — sign-extended to 64 bits.
        0x68 => {
            let imm = read_imm_i32(code, &mut p)? as u64;
            Ok((Instruction::Push(X86Operand::Imm(imm)), p))
        }

        // push imm8 (0x6a) — sign-extended imm8.
        0x6a => {
            let v = read_imm_i8(code, &mut p)?;
            Ok((Instruction::Push(X86Operand::Imm(v as u64)), p))
        }

        // xchg r/m, r  (0x87) — register form only.
        0x87 => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: xchg with a memory operand"));
            }
            let a = Reg::from_idx(m.rm)
                .ok_or_else(|| CoreError::parse("x86: invalid register in xchg"))?;
            let b = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid register in xchg"))?;
            Ok((Instruction::Xchg(reg_op(a), reg_op(b)), p))
        }

        // xchg eax/rax, reg (0x91..0x97)
        0x91..=0x97 => {
            let r = Reg::from_idx((op - 0x91) | if rex_b { 8 } else { 0 })
                .ok_or_else(|| CoreError::parse("x86: invalid register in xchg"))?;
            Ok((Instruction::Xchg(reg_op(Reg::RAX), reg_op(r)), p))
        }

        // cdqe (0x98) — sign-extend eax to rax (cwde in 16-bit, cdqe in 32/64).
        0x98 => Ok((Instruction::Cdqe, p)),

        // cqo (0x99) — sign-extend rax to rdx:rax (cwd/cdq/cqo depending on width).
        0x99 => Ok((Instruction::Cqo, p)),

        // movsxd (0x63) — sign-extend dword src to qword dst (REX.W implied for 64-bit dst).
        0x63 => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            let dst = Reg::from_idx(m.reg)
                .ok_or_else(|| CoreError::parse("x86: invalid register in movsxd"))?;
            if m.mode == 0b11 {
                let src = Reg::from_idx(m.rm)
                    .ok_or_else(|| CoreError::parse("x86: invalid register in movsxd"))?;
                Ok((
                    Instruction::Movsxd(
                        X86Operand::Reg(dst, Width::Q),
                        X86Operand::Reg(src, Width::D),
                    ),
                    p,
                ))
            } else {
                let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                Ok((
                    Instruction::Movsxd(
                        X86Operand::Reg(dst, Width::Q),
                        X86Operand::Mem(mem, Width::D),
                    ),
                    p,
                ))
            }
        }

        // String operations (0xa4..0xaf) — movs, cmps, stos, lods, scas.
        0xa4 => Ok((Instruction::Movs(Width::B), p)),
        0xa5 => Ok((Instruction::Movs(width), p)),
        0xa6 => Ok((Instruction::Cmps(Width::B), p)),
        0xa7 => Ok((Instruction::Cmps(width), p)),
        0xaa => Ok((Instruction::Stos(Width::B), p)),
        0xab => Ok((Instruction::Stos(width), p)),
        0xac => Ok((Instruction::Lods(Width::B), p)),
        0xad => Ok((Instruction::Lods(width), p)),
        0xae => Ok((Instruction::Scas(Width::B), p)),
        0xaf => Ok((Instruction::Scas(width), p)),

        // int3 (0xcc)
        0xcc => Ok((Instruction::Int3, p)),

        // lahf (0x9f) — load flags into AH.
        0x9f => Ok((Instruction::Lahf, p)),
        // sahf (0x9e) — store AH into flags.
        0x9e => Ok((Instruction::Sahf, p)),
        // pushf (0x9c) — push flags.
        0x9c => Ok((Instruction::Pushf, p)),
        // popf (0x9d) — pop flags.
        0x9d => Ok((Instruction::Popf, p)),

        // clc (0xf8) — clear carry flag.
        0xf8 => Ok((Instruction::Clc, p)),
        // stc (0xf9) — set carry flag.
        0xf9 => Ok((Instruction::Stc, p)),
        // cmc (0xf5) — complement carry flag.
        0xf5 => Ok((Instruction::Cmc, p)),
        // cld (0xfc) — clear direction flag.
        0xfc => Ok((Instruction::Cld, p)),
        // std (0xfd) — set direction flag.
        0xfd => Ok((Instruction::Std, p)),

        // call rel32 (0xe8)
        0xe8 => {
            let rel = read_imm_i32(code, &mut p)?;
            Ok((Instruction::Call(X86Operand::Rel(rel as i64)), p))
        }

        // Group 4 (0xfe): inc/dec r/m (register form only).
        0xfe => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: inc/dec with a memory operand"));
            }
            let dst = Reg::from_idx(m.rm)
                .ok_or_else(|| CoreError::parse("x86: invalid register in inc/dec"))?;
            let operand = X86Operand::Reg(dst, Width::B);
            match m.reg & 7 {
                0 => Ok((Instruction::Inc(operand), p)),
                1 => Ok((Instruction::Dec(operand), p)),
                _ => Err(CoreError::unsupported(format!(
                    "x86: unsupported group-4 /digit {}",
                    m.reg & 7
                ))),
            }
        }

        // Group 5 (0xff): inc/dec/call/jmp r/m (register form only).
        0xff => {
            let m = read_modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: group-5 with a memory operand"));
            }
            let dst = Reg::from_idx(m.rm)
                .ok_or_else(|| CoreError::parse("x86: invalid register in group-5"))?;
            let operand = reg_op(dst);
            match m.reg & 7 {
                0 => Ok((Instruction::Inc(operand), p)),
                1 => Ok((Instruction::Dec(operand), p)),
                2 => Ok((Instruction::Call(operand), p)),
                4 => Ok((Instruction::Jmp(operand), p)),
                _ => Err(CoreError::unsupported(format!(
                    "x86: unsupported group-5 /digit {}",
                    m.reg & 7
                ))),
            }
        }

        // MOV r/m8, imm8 (0xc6).
        0xc6 => {
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, Width::B)?;
            let imm = read_imm_u8(code, &mut p)?;
            Ok((Instruction::Mov(operand, X86Operand::Imm(imm as u64)), p))
        }
        // MOV r/m, imm32 (0xc7) — imm32 sign-extended when width > 32 (REX.W).
        0xc7 => {
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, width)?;
            let (imm_raw, _) = read_imm64(code, p, 4)?;
            p += 4;
            let imm = if width.bits() > 32 {
                imm_raw as u32 as i32 as i64 as u128 as u64
            } else {
                imm_raw
            };
            Ok((Instruction::Mov(operand, X86Operand::Imm(imm)), p))
        }

        // Group 2 — rotate/shift by imm8 (0xc0 byte, 0xc1 word/d/q).
        // Intel /digit encoding: 0=ROL, 1=ROR, 2=RCL, 3=RCR, 4=SHL, 5=SHR, 6=reserved, 7=SAR.
        0xc0 | 0xc1 => {
            let shift_width = if op == 0xc0 { Width::B } else { width };
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, shift_width)?;
            let imm = read_imm_u8(code, &mut p)?;
            let m = read_modrm(code, p - 2, rex_r, rex_b)?;
            match m.reg & 7 {
                0 => Ok((Instruction::Rol(operand, imm), p)),
                1 => Ok((Instruction::Ror(operand, imm), p)),
                2 => Ok((Instruction::Rcl(operand, imm), p)),
                3 => Ok((Instruction::Rcr(operand, imm), p)),
                4 => Ok((Instruction::Shl(operand, imm), p)),
                5 => Ok((Instruction::Shr(operand, imm), p)),
                7 => Ok((Instruction::Sar(operand, imm), p)),
                _ => Err(CoreError::unsupported(format!(
                    "x86: unsupported group-2 /digit {}",
                    m.reg & 7
                ))),
            }
        }

        // Group 2 — rotate/shift by 1 (0xd0 byte, 0xd1 word/d/q).
        // /digit encoding: same as Group 2 imm8 above.
        0xd0 | 0xd1 => {
            let shift_width = if op == 0xd0 { Width::B } else { width };
            let operand = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, shift_width)?;
            let m = read_modrm(code, p - 1, rex_r, rex_b)?;
            match m.reg & 7 {
                0 => Ok((Instruction::Rol(operand, 1), p)),
                1 => Ok((Instruction::Ror(operand, 1), p)),
                2 => Ok((Instruction::Rcl(operand, 1), p)),
                3 => Ok((Instruction::Rcr(operand, 1), p)),
                4 => Ok((Instruction::Shl(operand, 1), p)),
                5 => Ok((Instruction::Shr(operand, 1), p)),
                7 => Ok((Instruction::Sar(operand, 1), p)),
                _ => Err(CoreError::unsupported(format!(
                    "x86: unsupported group-2 shift-1 /digit {}",
                    m.reg & 7
                ))),
            }
        }

        // Group 3 (0xf6 byte, 0xf7 word/d/q): test/not/neg/mul/imul/div/idiv.
        // Only register form is supported (mode != 0b11 → unsupported).
        0xf6 | 0xf7 => {
            let is_byte = op == 0xf6;
            let group_width = if is_byte { Width::B } else { width };
            // read_rm_operand consumes the ModRM and advances p past it.
            if code.get(p).is_none() {
                return Err(CoreError::parse("x86: truncated ModR/M in group-3"));
            }
            // Peek at ModRM mode before consuming it — if not register form, reject.
            let peek_mod = code[p] >> 6;
            if peek_mod != 0b11 {
                return Err(CoreError::unsupported("x86: group-3 with a memory operand"));
            }
            let o1 = read_rm_operand(code, &mut p, rex_r, rex_x, rex_b, group_width)?;
            // Read the /digit field from the ModRM byte (at p-1 after read_rm_operand).
            let modrm_byte = *code
                .get(p - 1)
                .ok_or_else(|| CoreError::parse("x86: truncated ModR/M in group-3"))?;
            let reg_field = ((modrm_byte >> 3) & 7) | if rex_r { 8 } else { 0 };
            match reg_field & 7 {
                0 => {
                    // test r/m, imm — not /0
                    let imm_len = if is_byte {
                        1
                    } else {
                        if rex_w {
                            8
                        } else {
                            4
                        }
                    };
                    let (imm, _) = read_imm64(code, p, imm_len)?;
                    p += imm_len;
                    Ok((Instruction::Test(o1, X86Operand::Imm(imm)), p))
                }
                2 => Ok((Instruction::Not(o1), p)),
                3 => Ok((Instruction::Neg(o1), p)),
                4 => Ok((Instruction::Mul(o1), p)),
                5 => Ok((Instruction::Imul(o1), p)),
                6 => Ok((Instruction::Div(o1), p)),
                7 => Ok((Instruction::Idiv(o1), p)),
                _ => Err(CoreError::unsupported(format!(
                    "x86: unsupported group-3 /digit {}",
                    reg_field & 7
                ))),
            }
        }

        // Two-byte opcode escape (0x0F).
        0x0f => {
            let op2 = *code.get(p).ok_or_else(|| {
                CoreError::parse(format!("x86: truncated 0F opcode at offset {p}"))
            })?;
            p += 1;
            match op2 {
                // syscall (0F 05)
                0x05 => Ok((Instruction::Syscall, p)),
                // cmovcc (0F 40..4F) — conditional move.
                0x40..=0x4f => {
                    let cc = Condition::from_cc(op2 - 0x40)
                        .ok_or_else(|| CoreError::parse("x86: invalid condition code in cmovcc"))?;
                    let m = read_modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    let dst = Reg::from_idx(m.reg)
                        .ok_or_else(|| CoreError::parse("x86: invalid register in cmovcc"))?;
                    if m.mode == 0b11 {
                        let src = Reg::from_idx(m.rm)
                            .ok_or_else(|| CoreError::parse("x86: invalid register in cmovcc"))?;
                        Ok((Instruction::Cmovcc(cc, reg_op(dst), reg_op(src)), p))
                    } else {
                        let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                        Ok((
                            Instruction::Cmovcc(cc, reg_op(dst), X86Operand::Mem(mem, width)),
                            p,
                        ))
                    }
                }
                // jcc rel32 (0F 80..8F)
                0x80..=0x8f => {
                    let rel = read_imm_i32(code, &mut p)?;
                    let cc = Condition::from_cc(op2 - 0x80)
                        .ok_or_else(|| CoreError::parse("x86: invalid condition code"))?;
                    Ok((Instruction::Jcc(cc, rel as i64), p))
                }
                // setcc (0F 90..9F) — set byte on condition.
                0x90..=0x9f => {
                    let cc = Condition::from_cc(op2 - 0x90)
                        .ok_or_else(|| CoreError::parse("x86: invalid condition code in setcc"))?;
                    let m = read_modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    if m.mode == 0b11 {
                        let dst = Reg::from_idx(m.rm)
                            .ok_or_else(|| CoreError::parse("x86: invalid register in setcc"))?;
                        Ok((Instruction::Setcc(cc, X86Operand::Reg(dst, Width::B)), p))
                    } else {
                        let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                        Ok((Instruction::Setcc(cc, X86Operand::Mem(mem, Width::B)), p))
                    }
                }
                // multi-byte NOP (0F 1f /0)
                0x1f => {
                    // Accept any ModRM-encoded multi-byte NOP.
                    let m = read_modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    // Consume any SIB + displacement that ModRM indicates.
                    if m.mode != 0b11 {
                        let _ = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                    }
                    Ok((Instruction::Nop, p))
                }
                // bt r/m, r (0F A3) — bit test.
                0xa3 => {
                    let m = read_modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    let bit_index = Reg::from_idx(m.reg)
                        .ok_or_else(|| CoreError::parse("x86: invalid register in bt"))?;
                    if m.mode == 0b11 {
                        let base = Reg::from_idx(m.rm)
                            .ok_or_else(|| CoreError::parse("x86: invalid register in bt"))?;
                        Ok((Instruction::Bt(reg_op(base), reg_op(bit_index)), p))
                    } else {
                        let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                        Ok((
                            Instruction::Bt(X86Operand::Mem(mem, width), reg_op(bit_index)),
                            p,
                        ))
                    }
                }
                // bts r/m, r (0F AB) — bit test and set.
                0xab => {
                    let m = read_modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    let bit_index = Reg::from_idx(m.reg)
                        .ok_or_else(|| CoreError::parse("x86: invalid register in bts"))?;
                    if m.mode == 0b11 {
                        let base = Reg::from_idx(m.rm)
                            .ok_or_else(|| CoreError::parse("x86: invalid register in bts"))?;
                        Ok((Instruction::Bts(reg_op(base), reg_op(bit_index)), p))
                    } else {
                        let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                        Ok((
                            Instruction::Bts(X86Operand::Mem(mem, width), reg_op(bit_index)),
                            p,
                        ))
                    }
                }
                // btr r/m, r (0F B3) — bit test and reset.
                0xb3 => {
                    let m = read_modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    let bit_index = Reg::from_idx(m.reg)
                        .ok_or_else(|| CoreError::parse("x86: invalid register in btr"))?;
                    if m.mode == 0b11 {
                        let base = Reg::from_idx(m.rm)
                            .ok_or_else(|| CoreError::parse("x86: invalid register in btr"))?;
                        Ok((Instruction::Btr(reg_op(base), reg_op(bit_index)), p))
                    } else {
                        let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                        Ok((
                            Instruction::Btr(X86Operand::Mem(mem, width), reg_op(bit_index)),
                            p,
                        ))
                    }
                }
                // btc r/m, r (0F BB) — bit test and complement.
                0xbb => {
                    let m = read_modrm(code, p, rex_r, rex_b)?;
                    p += 1;
                    let bit_index = Reg::from_idx(m.reg)
                        .ok_or_else(|| CoreError::parse("x86: invalid register in btc"))?;
                    if m.mode == 0b11 {
                        let base = Reg::from_idx(m.rm)
                            .ok_or_else(|| CoreError::parse("x86: invalid register in btc"))?;
                        Ok((Instruction::Btc(reg_op(base), reg_op(bit_index)), p))
                    } else {
                        let mem = read_mem(code, &mut p, &m, rex_x, rex_b)?;
                        Ok((
                            Instruction::Btc(X86Operand::Mem(mem, width), reg_op(bit_index)),
                            p,
                        ))
                    }
                }
                // bsf (0F BC) — bit scan forward; bsr (0F BD) — bit scan reverse.
                0xbc => decode_bsf_bsr(code, &mut p, rex_r, rex_x, rex_b, width, false),
                0xbd => decode_bsf_bsr(code, &mut p, rex_r, rex_x, rex_b, width, true),
                // movzx (0F B6 / 0F B7)
                0xb6 => decode_movzx(code, &mut p, rex_r, rex_x, rex_b, width, false),
                0xb7 => decode_movzx(code, &mut p, rex_r, rex_x, rex_b, width, true),
                // movsx (0F BE / 0F BF)
                0xbe => decode_movsx(code, &mut p, rex_r, rex_x, rex_b, width, false),
                0xbf => decode_movsx(code, &mut p, rex_r, rex_x, rex_b, width, true),
                // 0F SSE opcodes (legacy prefix encoded in sse_pp).
                // These are handled by the shared SSE decoder that both VEX and legacy paths use.
                0x10 | 0x11 | 0x14 | 0x15 | 0x28 | 0x29 | 0x2e | 0x2f | 0x51 | 0x54 | 0x55
                | 0x56 | 0x57 | 0x58 | 0x59 | 0x5b | 0x5c | 0x5d | 0x5e | 0x5f | 0xc2 | 0xc6
                | 0xd4 | 0xdb | 0xeb | 0xef | 0xfb => {
                    decode_sse_0f_op(op2, code, &mut p, sse_pp, rex_r, rex_x, rex_b)
                }
                _ => Err(CoreError::unsupported(format!(
                    "x86: unsupported two-byte opcode 0f {op2:#04x}"
                ))),
            }
        }

        other => Err(CoreError::unsupported(format!(
            "x86: unsupported opcode {other:#04x}"
        ))),
    }
}

// ============================================================================
// VEX prefix parsing / SSE decode helpers
// ============================================================================
