use super::*;

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

/// Parsed VEX prefix information (used for SSE/AVX instructions).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) struct VexInfo {
    /// The third-operand register index (0..15), already decoded from the
    /// complemented VEX.vvvv field.
    pub(crate) vvvv: u8,
    /// VEX.L — 256-bit operation (YMM).
    pub(crate) l: bool,
    /// VEX.pp — implied legacy prefix (0=none, 1=66, 2=F3, 3=F2).
    pub(crate) pp: u8,
    /// VEX.mmmmm — opcode map (1=0F, 2=0F38, 3=0F3A).
    pub(crate) mmmmm: u8,
    /// Equivalent REX.W from VEX.W.
    pub(crate) w: bool,
    /// Equivalent REX.R (ModRM.reg extension): true → reg is r8/xmm8+.
    pub(crate) rex_r: bool,
    /// Equivalent REX.X (SIB.index extension). Always false for 2-byte VEX.
    pub(crate) rex_x: bool,
    /// Equivalent REX.B (ModRM.rm / SIB.base extension). Always false for 2-byte VEX.
    pub(crate) rex_b: bool,
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

    // --- Parse legacy prefixes (REX, 66, F2, F3, segments) ---
    let (rex_w, rex_r, rex_x, rex_b, op_size, addr_size, sse_pp) = parse_prefixes(code, &mut p)?;

    // The width of most integer operations: 64 with REX.W, else 32.
    let width = Width::from_rex_w(rex_w);

    // --- Check for VEX prefix (C4 / C5 in 64-bit mode) ---
    if let Some(&b) = code.get(p) {
        if b == 0xc5 || b == 0xc4 {
            let vex = parse_vex(code, &mut p, b == 0xc5)?;
            // The effective REX bits and the third-operand register are already
            // decoded in `vex` (see `parse_vex`).
            let (v_rex_w, v_rex_r, v_rex_x, v_rex_b) = (vex.w, vex.rex_r, vex.rex_x, vex.rex_b);

            // Determine the opcode lead bytes based on VEX.mmmmm.
            const MAP_0F: u8 = 1;
            const MAP_0F38: u8 = 2;
            const MAP_0F3A: u8 = 3;
            let (inst, next) = match vex.mmmmm {
                MAP_0F => decode_vex_0f(code, &mut p, vex)?,
                MAP_0F38 => decode_vex_0f38(code, &mut p, vex)?,
                MAP_0F3A => decode_vex_0f3a(code, &mut p, vex)?,
                _ => {
                    return Err(CoreError::unsupported(format!(
                        "x86: unsupported VEX map {}",
                        vex.mmmmm
                    )))
                }
            };

            return Ok(DecodedInstruction {
                offset,
                length: next - offset,
                prefixes: Prefixes {
                    rex: false,
                    rex_w: v_rex_w,
                    rex_r: v_rex_r,
                    rex_x: v_rex_x,
                    rex_b: v_rex_b,
                    operand_size: op_size,
                    address_size: addr_size,
                },
                instruction: inst,
            });
        }
    }

    // --- Opcode byte (non-VEX path) ---
    let op = *code
        .get(p)
        .ok_or_else(|| CoreError::parse(format!("x86: truncated opcode at offset {p}")))?;
    p += 1;

    // --- Decode by opcode ---
    let (inst, next) = decode_typed_opcode(
        op, code, p, rex_w, rex_r, rex_x, rex_b, op_size, width, sse_pp,
    )?;

    Ok(DecodedInstruction {
        offset,
        length: next - offset,
        prefixes: Prefixes {
            rex: rex_w || rex_r || rex_x || rex_b,
            rex_w,
            rex_r,
            rex_x,
            rex_b,
            operand_size: op_size,
            address_size: addr_size,
        },
        instruction: inst,
    })
}

/// Parse x86-64 legacy and REX prefixes, advancing `p` past them.
/// Returns (rex_w, rex_r, rex_x, rex_b, op_size, addr_size, sse_pp)
/// where sse_pp encodes the SSE/VEX mandatory prefix: 0=None, 1=0x66, 2=0xF3, 3=0xF2.
pub(crate) fn parse_prefixes(
    code: &[u8],
    p: &mut usize,
) -> csolver_core::Result<(bool, bool, bool, bool, bool, bool, u8)> {
    let mut rex_w = false;
    let mut rex_r = false;
    let mut rex_x = false;
    let mut rex_b = false;
    let mut op_size = false;
    let mut addr_size = false;
    let mut sse_pp: u8 = 0;

    loop {
        match code.get(*p).copied() {
            // REX prefix (0x40..0x4F) — only one REX prefix is valid.
            Some(b) if (0x40..=0x4f).contains(&b) => {
                rex_w = b & 8 != 0;
                rex_r = b & 4 != 0;
                rex_x = b & 2 != 0;
                rex_b = b & 1 != 0;
                *p += 1;
            }
            Some(0x66) => {
                op_size = true;
                sse_pp = 1;
                *p += 1;
            }
            Some(0x67) => {
                addr_size = true;
                *p += 1;
            }
            Some(0xF0) => {
                // LOCK: a 1-byte prefix making the following read-modify-write atomic. It does
                // not change the instruction's length or operands, so consume it and decode the
                // rest normally (the MSIR path additionally emits a full barrier — see decode_one).
                *p += 1;
            }
            Some(0xF2) => {
                sse_pp = 3; // REPNE → SSE prefix F2
                *p += 1;
            }
            Some(0xF3) => {
                sse_pp = 2; // REP/REPE → SSE prefix F3
                *p += 1;
            }
            Some(0x26 | 0x2E | 0x36 | 0x3E | 0x64 | 0x65) => {
                *p += 1;
            }
            _ => break,
        }
    }

    Ok((rex_w, rex_r, rex_x, rex_b, op_size, addr_size, sse_pp))
}

/// A raw ModRM byte with REX-extended reg and rm fields.
pub(crate) struct TypedModRm {
    pub(crate) mode: u8,
    pub(crate) reg: u8, // low 3 bits from ModRM.reg, extended by REX.R
    pub(crate) rm: u8,  // low 3 bits from ModRM.rm, extended by REX.B
}

/// Read a ModRM byte at `at`, applying REX.R and REX.B extensions.
pub(crate) fn read_modrm(
    code: &[u8],
    at: usize,
    rex_r: bool,
    rex_b: bool,
) -> csolver_core::Result<TypedModRm> {
    let b = *code
        .get(at)
        .ok_or_else(|| CoreError::parse(format!("x86: truncated ModR/M at offset {at}")))?;
    Ok(TypedModRm {
        mode: b >> 6,
        reg: ((b >> 3) & 7) | if rex_r { 8 } else { 0 },
        rm: (b & 7) | if rex_b { 8 } else { 0 },
    })
}

/// Read a memory operand from ModRM (mode != 11), including SIB and displacement,
/// advancing `p` past the consumed bytes.
pub(crate) fn read_mem(
    code: &[u8],
    p: &mut usize,
    m: &TypedModRm,
    rex_x: bool,
    rex_b: bool,
) -> csolver_core::Result<Mem> {
    let rm_low = m.rm & 7;
    let mut base = m.rm;
    let mut index = None;

    if rm_low == 4 {
        // SIB byte follows.
        let sib = *code
            .get(*p)
            .ok_or_else(|| CoreError::parse(format!("x86: truncated SIB at offset {}", *p)))?;
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
            return Ok(Mem {
                base: None,
                index,
                disp: disp as i64,
            });
        }
        base = base_field;
    } else if rm_low == 5 && m.mode == 0b00 {
        // RIP-relative addressing: disp32 with no base register.
        // In 64-bit mode, [rip + disp32] is encoded as ModRM.rm=5, mod=00.
        let disp = read_imm_i32(code, p)?;
        return Ok(Mem {
            base: None,
            index,
            disp: disp as i64,
        });
    }

    let base_reg = Reg::from_idx(base).ok_or_else(|| {
        CoreError::parse(format!(
            "x86: invalid base register {base} in memory operand at offset {}",
            *p
        ))
    })?;

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
pub(crate) fn read_rm_operand(
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
pub(crate) enum Group1Op {
    Add = 0,
    Or = 1,
    Adc = 2,
    Sbb = 3,
    And = 4,
    Sub = 5,
    Xor = 6,
    Cmp = 7,
}

pub(crate) fn group1_op_from_modrm_reg(
    code: &[u8],
    at: usize,
    rex_r: bool,
    _rex_b: bool,
) -> csolver_core::Result<Group1Op> {
    let b = *code.get(at).ok_or_else(|| {
        CoreError::parse(format!("x86: truncated ModR/M in group-1 at offset {at}"))
    })?;
    let reg = ((b >> 3) & 7) | if rex_r { 8 } else { 0 };
    match reg & 7 {
        0 => Ok(Group1Op::Add),
        1 => Ok(Group1Op::Or),
        2 => Ok(Group1Op::Adc),
        3 => Ok(Group1Op::Sbb),
        4 => Ok(Group1Op::And),
        5 => Ok(Group1Op::Sub),
        6 => Ok(Group1Op::Xor),
        7 => Ok(Group1Op::Cmp),
        _ => Err(CoreError::parse(format!(
            "x86: invalid group-1 /digit {reg} at offset {at}"
        ))),
    }
}

/// Decode `movzx` (0F B6: byte->word/d/q, 0F B7: word->d/q).
pub(crate) fn decode_movzx(
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
        let src = Reg::from_idx(m.rm).ok_or_else(|| {
            CoreError::parse(format!("x86: invalid src register {} in movzx", m.rm))
        })?;
        Ok((
            Instruction::Movzx(
                X86Operand::Reg(dst, dst_width),
                X86Operand::Reg(src, src_width),
            ),
            *p,
        ))
    } else {
        let mem = read_mem(code, p, &m, rex_x, rex_b)?;
        Ok((
            Instruction::Movzx(
                X86Operand::Reg(dst, dst_width),
                X86Operand::Mem(mem, src_width),
            ),
            *p,
        ))
    }
}

/// Decode `movsx` (0F BE: byte->word/d/q, 0F BF: word->d/q).
pub(crate) fn decode_movsx(
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
        let src = Reg::from_idx(m.rm).ok_or_else(|| {
            CoreError::parse(format!("x86: invalid src register {} in movsx", m.rm))
        })?;
        Ok((
            Instruction::Movsx(
                X86Operand::Reg(dst, dst_width),
                X86Operand::Reg(src, src_width),
            ),
            *p,
        ))
    } else {
        let mem = read_mem(code, p, &m, rex_x, rex_b)?;
        Ok((
            Instruction::Movsx(
                X86Operand::Reg(dst, dst_width),
                X86Operand::Mem(mem, src_width),
            ),
            *p,
        ))
    }
}

/// Decode `bsf` (0F BC) / `bsr` (0F BD) — bit scan forward/reverse.
/// Format: bsf/bsr dst, src — reg field = dst, r/m field = src (reg or mem).
pub(crate) fn decode_bsf_bsr(
    code: &[u8],
    p: &mut usize,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    width: Width,
    reverse: bool,
) -> csolver_core::Result<(Instruction, usize)> {
    let m = read_modrm(code, *p, rex_r, rex_b)?;
    *p += 1;
    let dst = Reg::from_idx(m.reg).ok_or_else(|| {
        CoreError::parse(format!("x86: invalid dst register {} in bsf/bsr", m.reg))
    })?;
    let dst_op = X86Operand::Reg(dst, width);
    let inst = if m.mode == 0b11 {
        let src = Reg::from_idx(m.rm).ok_or_else(|| {
            CoreError::parse(format!("x86: invalid src register {} in bsf/bsr", m.rm))
        })?;
        let src_op = X86Operand::Reg(src, width);
        if reverse {
            Instruction::Bsr(dst_op, src_op)
        } else {
            Instruction::Bsf(dst_op, src_op)
        }
    } else {
        let mem = read_mem(code, p, &m, rex_x, rex_b)?;
        if reverse {
            Instruction::Bsr(dst_op, X86Operand::Mem(mem, width))
        } else {
            Instruction::Bsf(dst_op, X86Operand::Mem(mem, width))
        }
    };
    Ok((inst, *p))
}

/// Read an unsigned 8-bit immediate, advancing `p`.
pub(crate) fn read_imm_u8(code: &[u8], p: &mut usize) -> csolver_core::Result<u8> {
    let b = *code
        .get(*p)
        .ok_or_else(|| CoreError::parse(format!("x86: truncated imm8 at offset {}", *p)))?;
    *p += 1;
    Ok(b)
}

/// Read a signed 8-bit immediate (sign-extended to i64), advancing `p`.
pub(crate) fn read_imm_i8(code: &[u8], p: &mut usize) -> csolver_core::Result<i64> {
    let b = *code
        .get(*p)
        .ok_or_else(|| CoreError::parse(format!("x86: truncated imm8 at offset {}", *p)))?;
    *p += 1;
    Ok((b as i8) as i64)
}

/// Read a signed 32-bit immediate (sign-extended to i64), advancing `p`.
pub(crate) fn read_imm_i32(code: &[u8], p: &mut usize) -> csolver_core::Result<i64> {
    let bytes = code
        .get(*p..*p + 4)
        .ok_or_else(|| CoreError::parse(format!("x86: truncated imm32 at offset {}", *p)))?;
    let v = i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    *p += 4;
    Ok(v as i64)
}

/// Read a little-endian unsigned immediate of `len` bytes (4 or 8),
/// advancing `p`.
pub(crate) fn read_imm64(code: &[u8], p: usize, len: usize) -> csolver_core::Result<(u64, usize)> {
    let bytes = code
        .get(p..p + len)
        .ok_or_else(|| CoreError::parse(format!("x86: truncated immediate at offset {p}")))?;
    let mut v: u64 = 0;
    for (i, &byte) in bytes.iter().enumerate() {
        v |= (byte as u64) << (8 * i);
    }
    Ok((v, len))
}
