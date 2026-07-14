use super::*;

/// Decode one instruction starting at `pos`. `flags` carries the last
/// `cmp`/`test` operands so a following `jcc` can form its condition.
pub(crate) fn decode_one(
    code: &[u8],
    pos: usize,
    flags: &mut Option<(Operand, Operand)>,
    resolve: RelocResolver,
    resolve_call: CallResolver,
) -> csolver_core::Result<Decoded> {
    let mut p = pos;
    // LOCK prefix (`f0`): the following instruction is an atomic read-modify-write. Its memory
    // access — and the in-bounds / permission obligations on it — are exactly those of the
    // un-prefixed form, so decode the rest normally and prepend a **full barrier** (LOCK is a
    // full memory fence). This models `lock add [mem], r` / `lock xchg` / `lock cmpxchg` as the
    // RMW they are instead of declining the whole instruction.
    if code.get(p) == Some(&0xf0) {
        let mut inner = decode_one(code, p + 1, flags, resolve, resolve_call)?;
        inner.insts.insert(0, Inst::Barrier { kind: 0, access: None });
        return Ok(inner);
    }
    // CET / alignment **no-ops**, special-cased before any prefix handling so no
    // general legacy prefix is ever *guessed* at (that would risk mis-decoding).
    // `endbr64`/`endbr32` (`f3 0f 1e fa|fb`) open almost every function in a
    // CET/IBT-built kernel; a multi-byte `nop` (`66? 0f 1f /M`) pads inside functions.
    // Both are pure no-ops regardless of operand size, so consuming them is sound.
    if code.get(p) == Some(&0xf3)
        && code.get(p + 1) == Some(&0x0f)
        && code.get(p + 2) == Some(&0x1e)
        && matches!(code.get(p + 3), Some(&(0xfa | 0xfb)))
    {
        return Ok(Decoded { insts: vec![], next: p + 4, ctrl: Ctrl::Fall });
    }
    if code.get(p) == Some(&0x66) && code.get(p + 1) == Some(&0x0f) && code.get(p + 2) == Some(&0x1f) {
        let m = modrm(code, p + 3, false, false)?;
        let next = if m.mode == 0b11 {
            p + 4
        } else {
            mem_operand(code, p + 4, &m, false, false, resolve)?.next
        };
        return Ok(Decoded { insts: vec![], next, ctrl: Ctrl::Fall });
    }
    // Segment override prefix `fs`/`gs` (`0x64`/`0x65`): the memory operand addresses a
    // *separate* thread-local address space — the stack canary (`%fs:0x28`), thread-local
    // storage, or a per-CPU base (`%gs:…`) — not the tracked flat memory. Decode the rest of
    // the instruction, then **neutralise its segment access**: a load yields an opaque value,
    // a store is dropped. Sound: segment memory never aliases a tracked region, and its
    // values (a canary, a per-CPU pointer) do not establish the safety of any tracked access.
    // Without this the whole (canary-guarded) function would drop on the unknown prefix.
    if matches!(code.get(p), Some(0x64 | 0x65)) {
        let inner = decode_one(code, p + 1, flags, resolve, resolve_call)?;
        let insts = inner.insts.into_iter().filter_map(neutralize_segment_access).collect();
        return Ok(Decoded { insts, next: inner.next, ctrl: inner.ctrl });
    }
    // Optional REX prefix (0x40..0x4F): W=wide(64), R=reg ext, X=index ext,
    // B=rm/base ext.
    let (rex_w, rex_r, rex_x, rex_b) = match code.get(p) {
        Some(&b) if (0x40..=0x4f).contains(&b) => {
            p += 1;
            (b & 8 != 0, b & 4 != 0, b & 2 != 0, b & 1 != 0)
        }
        _ => (false, false, false, false),
    };
    let op = *code.get(p).ok_or_else(|| CoreError::parse(format!("x86: truncated opcode at offset {p}")))?;
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
            let bin = match op {
                0x31 => BinOp::Xor,
                0x01 => BinOp::Add,
                0x29 => BinOp::Sub,
                0x21 => BinOp::And,
                0x09 => BinOp::Or,
                _ => unreachable!(),
            };
            let src = reg(m.reg);
            if m.mode == 0b11 {
                let dst = reg(m.rm);
                // `xor r, r` is the idiom for zeroing — model it as `r = 0`.
                let value = if op == 0x31 && m.rm == m.reg {
                    RValue::Use(Operand::int(width, 0))
                } else {
                    RValue::Bin { op: bin, lhs: Operand::Reg(dst), rhs: Operand::Reg(src), flags: Default::default() }
                };
                done(vec![Inst::Assign { dst, ty, value }], p)
            } else {
                // `<alu> [mem], r` — a read-modify-write on memory: load, combine with the
                // register, store back. The load and store carry the ordinary in-bounds /
                // permission obligations, so an OOB through the memory operand is now checked
                // (previously this form was declined and the access went unmodelled).
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                let loaded = RegId(3000 + pos as u32);
                insts.push(Inst::Load { dst: loaded, ty: ty.clone(), ptr: Operand::Reg(ptr), align: 1, volatile: false });
                insts.push(Inst::Assign {
                    dst: loaded,
                    ty: ty.clone(),
                    value: RValue::Bin { op: bin, lhs: Operand::Reg(loaded), rhs: Operand::Reg(src), flags: Default::default() },
                });
                insts.push(Inst::Store { ty, ptr: Operand::Reg(ptr), value: Operand::Reg(loaded), align: 1, volatile: false });
                done(insts, mem.next)
            }
        }
        // <alu> r, r/m — reg destination, r/m source (reg or memory): add/or/and/sub/xor.
        0x03 | 0x0b | 0x23 | 0x2b | 0x33 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            let bin = match op {
                0x03 => BinOp::Add,
                0x0b => BinOp::Or,
                0x23 => BinOp::And,
                0x2b => BinOp::Sub,
                0x33 => BinOp::Xor,
                _ => unreachable!(),
            };
            let dst = reg(m.reg);
            if m.mode == 0b11 {
                // `xor r, r` is the zeroing idiom.
                let value = if op == 0x33 && m.rm == m.reg {
                    RValue::Use(Operand::int(width, 0))
                } else {
                    RValue::Bin { op: bin, lhs: Operand::Reg(dst), rhs: Operand::Reg(reg(m.rm)) , flags: Default::default() }
                };
                done(vec![Inst::Assign { dst, ty, value }], p)
            } else {
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                let loaded = RegId(3000 + pos as u32);
                insts.push(Inst::Load { dst: loaded, ty: ty.clone(), ptr: Operand::Reg(ptr), align: 1 , volatile: false});
                insts.push(Inst::Assign {
                    dst,
                    ty,
                    value: RValue::Bin { op: bin, lhs: Operand::Reg(dst), rhs: Operand::Reg(loaded) , flags: Default::default() },
                });
                done(insts, mem.next)
            }
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
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                insts.push(Inst::Store { ty, ptr: Operand::Reg(ptr), value: Operand::Reg(reg(m.reg)), align: 1 , volatile: false});
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
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                insts.push(Inst::Load { dst: reg(m.reg), ty, ptr: Operand::Reg(ptr), align: 1 , volatile: false});
                done(insts, mem.next)
            }
        }
        // lea r, [mem] — compute the effective address into r (no memory access).
        0x8d => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                return Err(CoreError::unsupported("x86: lea requires a memory operand"));
            }
            let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
            let (mut insts, ptr) = mem.lower(pos);
            insts.push(Inst::Assign { dst: reg(m.reg), ty, value: RValue::Use(Operand::Reg(ptr)) });
            done(insts, mem.next)
        }
        // group 1: <op> r/m, imm8 — register target (mod 11) only.
        // x86 sign-extends the 8-bit immediate to the operand width.
        0x83 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                // `<op> [mem], imm8` — the imm8 follows the SIB/displacement, so parse the memory
                // operand first, then the immediate at `mem.next`. add/or/and/sub/xor are a
                // read-modify-write on memory; cmp (/7) is a read-only load feeding the flags.
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let imm_raw = read_imm(code, mem.next, 1)?;
                let imm = (imm_raw as u8 as i8 as i128) as u128;
                let next = mem.next + 1;
                let (mut insts, ptr) = mem.lower(pos);
                let loaded = RegId(3000 + pos as u32);
                insts.push(Inst::Load { dst: loaded, ty: ty.clone(), ptr: Operand::Reg(ptr), align: 1, volatile: false });
                let bin = match m.reg & 7 {
                    0 => BinOp::Add,
                    1 => BinOp::Or,
                    4 => BinOp::And,
                    5 => BinOp::Sub,
                    6 => BinOp::Xor,
                    7 => {
                        // cmp [mem], imm8 — read-only; record the operands for a following `jcc`.
                        *flags = Some((Operand::Reg(loaded), Operand::int(width, imm)));
                        return done(insts, next);
                    }
                    d => return Err(CoreError::unsupported(format!("x86: unsupported group-1 /digit {d} with a memory operand"))),
                };
                insts.push(Inst::Assign {
                    dst: loaded,
                    ty: ty.clone(),
                    value: RValue::Bin { op: bin, lhs: Operand::Reg(loaded), rhs: Operand::int(width, imm), flags: Default::default() },
                });
                insts.push(Inst::Store { ty, ptr: Operand::Reg(ptr), value: Operand::Reg(loaded), align: 1, volatile: false });
                return done(insts, next);
            }
            let imm_raw = read_imm(code, p, 1)?; // imm8, value 0..255
            p += 1;
            // Sign-extend imm8 to the operand width.
            let imm = (imm_raw as u8 as i8 as i128) as u128;
            let uns = |v: u128| v & ((1u128 << width) - 1); // mask to width
            let target = reg(m.rm);
            // The /digit (ModRM reg field, sans any REX.R) selects the operation.
            match m.reg & 7 {
                // `sub rsp, N` allocates the stack frame: model rsp as a pointer
                // to a fresh N-byte stack region, so `[rsp+disp]` is checked
                // against the frame. N is always positive in practice.
                5 if m.rm == 4 => done(
                    vec![Inst::Alloc {
                        dst: target,
                        region: RegionKind::Stack,
                        elem: Type::int(8),
                        count: Operand::int(64, uns(imm)),
                        align: 16,
                    }],
                    p,
                ),
                // `add rsp, N` tears the frame down; nothing accesses it after, so
                // it is a no-op for the analysis.
                0 if m.rm == 4 => done(vec![], p),
                0 => done(vec![add_imm(target, ty, BinOp::Add, uns(imm), width)], p),
                5 => done(vec![add_imm(target, ty, BinOp::Sub, uns(imm), width)], p),
                7 => {
                    // cmp r, imm — record the operands for a following `jcc`.
                    *flags = Some((Operand::Reg(target), Operand::int(width, uns(imm))));
                    done(vec![], p)
                }
                _ => Err(CoreError::unsupported("x86: unsupported group-1 operation")),
              }
          }
          // cmp r/m, r — record operands for a following `jcc` (reg/reg form).
        0x39 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                *flags = Some((Operand::Reg(reg(m.rm)), Operand::Reg(reg(m.reg))));
                done(vec![], p)
            } else {
                // cmp [mem], r — reads memory (the load carries the access obligations), sets flags.
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                let loaded = RegId(3000 + pos as u32);
                insts.push(Inst::Load { dst: loaded, ty, ptr: Operand::Reg(ptr), align: 1, volatile: false });
                *flags = Some((Operand::Reg(loaded), Operand::Reg(reg(m.reg))));
                done(insts, mem.next)
            }
        }
        // cmp r, r/m (reg source or memory source).
        0x3b => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                *flags = Some((Operand::Reg(reg(m.reg)), Operand::Reg(reg(m.rm))));
                done(vec![], p)
            } else {
                // cmp r, [mem] — model the memory read, then compare.
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                let loaded = RegId(3000 + pos as u32);
                insts.push(Inst::Load { dst: loaded, ty, ptr: Operand::Reg(ptr), align: 1, volatile: false });
                *flags = Some((Operand::Reg(reg(m.reg)), Operand::Reg(loaded)));
                done(insts, mem.next)
            }
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
            if m.mode != 0b11 {
                // test [mem], r — model the memory read (the AND-flags are not tracked, as for
                // the reg-reg non-self case), so the access carries its obligations.
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                let loaded = RegId(3000 + pos as u32);
                insts.push(Inst::Load { dst: loaded, ty, ptr: Operand::Reg(ptr), align: 1, volatile: false });
                *flags = None;
                done(insts, mem.next)
            } else {
                *flags = if m.rm == m.reg {
                    Some((Operand::Reg(reg(m.rm)), Operand::int(width, 0)))
                } else {
                    None
                };
                done(vec![], p)
            }
        }
        // jmp rel8 / rel32.
        0xeb => {
            let rel = read_imm(code, p, 1)? as u8 as i8 as i64;
            let np = p + 1;
            Ok(Decoded { insts: vec![], next: np, ctrl: Ctrl::Jmp(branch_target(np, rel)?) })
        }
        // call rel32: an OPAQUE call that returns and falls through — havocs caller-saved
        // registers + rax, so analysis continues past it instead of dropping the whole
        // function (real functions almost always contain calls). The target offset is
        // recorded for stripped-binary function discovery (see `call_targets`).
        0xe8 => {
            let _rel = read_imm(code, p, 4)? as u32 as i32 as i64;
            // A direct call whose target the relocation names becomes a **named** call carrying
            // the SysV argument registers as its args — so a post-pass can match it against an
            // API contract (allocator / free / user-copy) and model its memory effect, exactly
            // as the LLVM front-end does. An unnamed (unrelocated) call stays opaque.
            let inst = match resolve_call(p) {
                Some(name) => named_call(name),
                None => opaque_call(),
            };
            Ok(Decoded { insts: vec![inst], next: p + 4, ctrl: Ctrl::Fall })
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
        // movsxd r64, r/m32 — sign-extend dword to qword.
        0x63 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                done(
                    vec![Inst::Assign {
                dst: reg(m.reg),
                ty: ty.clone(),
                value: RValue::Cast {
                    op: CastOp::SExt,
                    operand: Operand::Reg(reg(m.rm)),
                    to: ty,
                },
            }],
            p,
        )
    } else {
        let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
        let (mut insts, ptr) = mem.lower(pos);
        let tmp = temp_reg(pos);
        insts.push(Inst::Load { dst: tmp, ty: Type::int(32), ptr: Operand::Reg(ptr), align: 1 , volatile: false});
        insts.push(Inst::Assign {
            dst: reg(m.reg),
            ty: ty.clone(),
            value: RValue::Cast { op: CastOp::SExt, operand: Operand::Reg(tmp), to: ty },
                });
                done(insts, mem.next)
            }
        }
        // push reg (0x50..0x57).
        0x50..=0x57 => {
            let r = reg(op - 0x50 + if rex_b { 8 } else { 0 });
            let size = if rex_w { 8 } else { 4 };
            done(
                vec![
                    Inst::Alloc {
                        dst: reg(4),
                        region: RegionKind::Stack,
                        elem: Type::int(8),
                        count: Operand::int(64, size as u128),
                        align: if size == 8 { 8 } else { 4 },
                    },
                    Inst::Store {
                        ty: Type::int(size as u32 * 8),
                        ptr: Operand::Reg(reg(4)),
                        value: Operand::Reg(r),
                        align: if size == 8 { 8 } else { 4 }, volatile: false,
                    },
                ],
                p,
            )
        }
        // pop reg (0x58..0x5f).
        0x58..=0x5f => {
            let r = reg(op - 0x58 + if rex_b { 8 } else { 0 });
            let size = if rex_w { 8 } else { 4 };
            done(
                vec![Inst::Load {
                    dst: r,
                    ty: Type::int(size as u32 * 8),
                    ptr: Operand::Reg(reg(4)),
                    align: if size == 8 { 8 } else { 4 }, volatile: false,
                }],
                p,
            )
        }
        // push imm32 (0x68) — sign-extended to 64 bits.
        0x68 => {
            let imm = read_imm(code, p, 4)? as u32 as i32 as i64 as u128;
            done(
                vec![
                    Inst::Alloc {
                        dst: reg(4),
                        region: RegionKind::Stack,
                        elem: Type::int(8),
                        count: Operand::int(64, 8),
                        align: 8,
                    },
                    Inst::Store {
                        ty: Type::int(64),
                        ptr: Operand::Reg(reg(4)),
                        value: Operand::int(64, imm),
                        align: 8, volatile: false
                    },
                ],
                p + 4,
            )
        }
        // push imm8 (0x6a).
        0x6a => {
            let imm = read_imm(code, p, 1)? as u8 as i8 as i64 as u128;
            done(
                vec![
                    Inst::Alloc {
                        dst: reg(4),
                        region: RegionKind::Stack,
                        elem: Type::int(8),
                        count: Operand::int(64, 8),
                        align: 8,
                    },
                    Inst::Store {
                        ty: Type::int(64),
                        ptr: Operand::Reg(reg(4)),
                        value: Operand::int(64, imm),
                        align: 8, volatile: false
                    },
                ],
                p + 1,
            )
        }
        // xchg rax, reg (0x91..0x97).
        0x91..=0x97 => {
            let rax = reg(0);
            let r = reg(op - 0x91 + if rex_b { 8 } else { 0 });
            let t = temp_reg(pos);
            done(
                vec![
                    Inst::Assign { dst: t, ty: ty.clone(), value: RValue::Use(Operand::Reg(rax)) },
                    Inst::Assign { dst: rax, ty: ty.clone(), value: RValue::Use(Operand::Reg(r)) },
                    Inst::Assign { dst: r, ty, value: RValue::Use(Operand::Reg(t)) },
                ],
                p,
            )
        }
        // xchg r/m, r (0x87): register swap, or an atomic swap with memory.
        0x87 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            let ra = reg(m.reg);
            if m.mode == 0b11 {
                let rb = reg(m.rm);
                let t = temp_reg(pos);
                done(
                    vec![
                        Inst::Assign { dst: t, ty: ty.clone(), value: RValue::Use(Operand::Reg(ra)) },
                        Inst::Assign { dst: ra, ty: ty.clone(), value: RValue::Use(Operand::Reg(rb)) },
                        Inst::Assign { dst: rb, ty, value: RValue::Use(Operand::Reg(t)) },
                    ],
                    p,
                )
            } else {
                // xchg [mem], r — implicitly LOCKed (a full barrier): `t = [mem]; [mem] = r; r = t`.
                // The load and store carry the memory-access obligations.
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                let t = RegId(3000 + pos as u32);
                insts.push(Inst::Barrier { kind: 0, access: None });
                insts.push(Inst::Load { dst: t, ty: ty.clone(), ptr: Operand::Reg(ptr), align: 1, volatile: false });
                insts.push(Inst::Store { ty: ty.clone(), ptr: Operand::Reg(ptr), value: Operand::Reg(ra), align: 1, volatile: false });
                insts.push(Inst::Assign { dst: ra, ty, value: RValue::Use(Operand::Reg(t)) });
                done(insts, mem.next)
            }
        }
        // cdqe (0x98 with REX.W) — sign-extend eax to rax.
        0x98 => {
            if rex_w {
                done(
                    vec![Inst::Assign {
                        dst: reg(0),
                        ty: Type::int(64),
                        value: RValue::Cast {
                            op: CastOp::SExt,
                            operand: Operand::Reg(reg(0)),
                            to: Type::int(64),
                        },
                    }],
                    p,
                )
            } else {
                // cwde — sign-extend ax to eax; in 64-bit mode, zero-extend to rax.
                done(
                    vec![Inst::Assign {
                        dst: reg(0),
                        ty: Type::int(32),
                        value: RValue::Cast {
                            op: CastOp::SExt,
                            operand: Operand::Reg(reg(0)),
                            to: Type::int(32),
                        },
                    }],
                    p,
                )
            }
        }
        // cqo/cdq/cwd (0x99) — sign-extend accumulator to rdx:rax.
        // REX.W → cqo  (sign-extend 64-bit rax → rdx:rax)
        // no REX → cdq  (sign-extend 32-bit eax → edx:eax)
        // 0x66   → cwd  (sign-extend 16-bit ax  → dx:ax)
        0x99 => {
            let shift_bits: u32 = if rex_w { 63 } else if width == 16 { 15 } else { 31 };
            let dst = reg(2);
            done(
                vec![Inst::Assign {
                    dst,
                    ty: Type::int(width),
                    value: RValue::Bin {
                        op: BinOp::AShr,
                        lhs: Operand::Reg(reg(0)),
                        rhs: Operand::int(width, shift_bits as u128),
                    flags: Default::default(),
                    },
                }],
                p,
            )
        }
        // mov r/m, imm32 (0xc7) — immediate dword to register or memory.
        // With REX.W the 32-bit immediate is sign-extended to 64 bits.
        0xc7 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            let imm_raw = read_imm(code, p, 4)?;
            p += 4;
            let imm = if width > 32 { imm_raw as u32 as i32 as i64 as u128 } else { imm_raw };
            if m.mode == 0b11 {
                done(
                    vec![Inst::Assign {
                        dst: reg(m.rm),
                        ty,
                        value: RValue::Use(Operand::int(width, imm)),
                    }],
                    p,
                )
            } else {
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                insts.push(Inst::Store { ty, ptr: Operand::Reg(ptr), value: Operand::int(width, imm), align: 1 , volatile: false});
                done(insts, mem.next)
            }
        }
        // mov r/m8, imm8 (0xc6).
        0xc6 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            let imm = read_imm(code, p, 1)?;
            p += 1;
            if m.mode == 0b11 {
                done(
                    vec![Inst::Assign {
                        dst: reg(m.rm),
                        ty: Type::int(8),
                        value: RValue::Use(Operand::int(8, imm)),
                    }],
                    p,
                )
            } else {
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                insts.push(Inst::Store { ty: Type::int(8), ptr: Operand::Reg(ptr), value: Operand::int(8, imm), align: 1 , volatile: false});
                done(insts, mem.next)
            }
        }
        // Group 2 shift r/m, imm8 (0xc1) and shift r/m, 1 (0xd1).
        0xc1 | 0xd1 => {
            let shift_by_1 = op == 0xd1;
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: shift with a memory operand"));
            }
            let count = if shift_by_1 { 1u128 } else {
                let c = read_imm(code, p, 1)?;
                p += 1;
                c
            };
            let target = reg(m.rm);
            let bin_op = match m.reg & 7 {
                4 => BinOp::Shl,
                5 => BinOp::LShr,
                7 => BinOp::AShr,
                _ => return Err(CoreError::unsupported(format!("x86: unsupported group-2 operation /digit {}", m.reg & 7))),
            };
            done(
                vec![Inst::Assign {
                    dst: target,
                    ty,
                    value: RValue::Bin {
                        op: bin_op,
                        lhs: Operand::Reg(target),
                        rhs: Operand::int(width, count),
                    flags: Default::default(),
                    },
                }],
                p,
            )
        }
        // Group 3 r/m (0xf6, 0xf7, reg-reg only): test/not/neg/mul/imul/div/idiv.
        // We decode only not and neg; the rest are returned as unsupported.
        0xf6 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: group-3 with a memory operand"));
            }
            let target = reg(m.rm);
            let w = 8;
            match m.reg & 7 {
                2 => {
                    // not r/m8 = xor r/m8, 0xFF
                    done(
                        vec![Inst::Assign {
                            dst: target,
                            ty: Type::int(w),
                            value: RValue::Bin {
                                op: BinOp::Xor,
                                lhs: Operand::Reg(target),
                                rhs: Operand::int(w, (1u128 << w) - 1),
                            flags: Default::default(),
                            },
                        }],
                        p,
                    )
                }
                3 => {
                    // neg r/m8 = 0 - r/m8
                    done(
                        vec![Inst::Assign {
                            dst: target,
                            ty: Type::int(w),
                            value: RValue::Bin {
                                op: BinOp::Sub,
                                lhs: Operand::int(w, 0),
                                rhs: Operand::Reg(target),
                            flags: Default::default(),
                            },
                        }],
                        p,
                    )
                }
                _ => Err(CoreError::unsupported(format!("x86: unsupported group-3 /digit {} with 8-bit", m.reg & 7))),
            }
        }
        0xf7 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: group-3 with a memory operand"));
            }
            let target = reg(m.rm);
            match m.reg & 7 {
                2 => {
                    // not r/m = xor r/m, all-ones
                    done(
                        vec![Inst::Assign {
                            dst: target,
                            ty,
                            value: RValue::Bin {
                                op: BinOp::Xor,
                                lhs: Operand::Reg(target),
                                rhs: Operand::int(width, (1u128 << width) - 1),
                            flags: Default::default(),
                            },
                        }],
                        p,
                    )
                }
                3 => {
                    // neg r/m = 0 - r/m
                    done(
                        vec![Inst::Assign {
                            dst: target,
                            ty,
                            value: RValue::Bin {
                                op: BinOp::Sub,
                                lhs: Operand::int(width, 0),
                                rhs: Operand::Reg(target),
                            flags: Default::default(),
                            },
                        }],
                        p,
                    )
                }
                _ => Err(CoreError::unsupported(format!("x86: unsupported group-3 /digit {}", m.reg & 7))),
            }
        }
        // Group 4 inc/dec r/m8 (0xfe): register or an 8-bit memory read-modify-write.
        0xfe => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            let bin_op = match m.reg & 7 {
                0 => BinOp::Add,
                1 => BinOp::Sub,
                _ => return Err(CoreError::unsupported(format!("x86: unsupported group-4 /digit {}", m.reg & 7))),
            };
            let inc = |lhs| RValue::Bin { op: bin_op, lhs, rhs: Operand::int(8, 1), flags: Default::default() };
            if m.mode == 0b11 {
                let target = reg(m.rm);
                done(vec![Inst::Assign { dst: target, ty: Type::int(8), value: inc(Operand::Reg(target)) }], p)
            } else {
                // inc/dec byte [mem] — load, ±1, store back (the access carries its obligations).
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                let loaded = RegId(3000 + pos as u32);
                insts.push(Inst::Load { dst: loaded, ty: Type::int(8), ptr: Operand::Reg(ptr), align: 1, volatile: false });
                insts.push(Inst::Assign { dst: loaded, ty: Type::int(8), value: inc(Operand::Reg(loaded)) });
                insts.push(Inst::Store { ty: Type::int(8), ptr: Operand::Reg(ptr), value: Operand::Reg(loaded), align: 1, volatile: false });
                done(insts, mem.next)
            }
        }
        // Group 5 (0xff): inc/dec/call/jmp — register, or a memory operand.
        0xff => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                let loaded = RegId(3000 + pos as u32);
                return match m.reg & 7 {
                    // inc/dec [mem] — a read-modify-write.
                    d @ (0 | 1) => {
                        let bin = if d == 0 { BinOp::Add } else { BinOp::Sub };
                        insts.push(Inst::Load { dst: loaded, ty: ty.clone(), ptr: Operand::Reg(ptr), align: 1, volatile: false });
                        insts.push(Inst::Assign {
                            dst: loaded,
                            ty: ty.clone(),
                            value: RValue::Bin { op: bin, lhs: Operand::Reg(loaded), rhs: Operand::int(width, 1), flags: Default::default() },
                        });
                        insts.push(Inst::Store { ty, ptr: Operand::Reg(ptr), value: Operand::Reg(loaded), align: 1, volatile: false });
                        done(insts, mem.next)
                    }
                    // call [mem] — load the target pointer (the read is checked), then an opaque
                    // call that falls through (havocs caller-saved + rax), as for the reg form.
                    2 => {
                        insts.push(Inst::Load { dst: loaded, ty, ptr: Operand::Reg(ptr), align: 1, volatile: false });
                        insts.push(opaque_call());
                        Ok(Decoded { insts, next: mem.next, ctrl: Ctrl::Fall })
                    }
                    // jmp [mem] — load the target (checked), then stop (tail/switch; conservative).
                    4 => {
                        insts.push(Inst::Load { dst: loaded, ty, ptr: Operand::Reg(ptr), align: 1, volatile: false });
                        Ok(Decoded { insts, next: mem.next, ctrl: Ctrl::Ret })
                    }
                    d => Err(CoreError::unsupported(format!("x86: unsupported group-5 /digit {d} with a memory operand"))),
                };
            }
            let target = reg(m.rm);
            match m.reg & 7 {
                0 => done(
                    vec![Inst::Assign {
                        dst: target,
                        ty,
                        value: RValue::Bin { op: BinOp::Add, lhs: Operand::Reg(target), rhs: Operand::int(width, 1) , flags: Default::default() },
                    }],
                    p,
                ),
                1 => done(
                    vec![Inst::Assign {
                        dst: target,
                        ty,
                        value: RValue::Bin { op: BinOp::Sub, lhs: Operand::Reg(target), rhs: Operand::int(width, 1) , flags: Default::default() },
                    }],
                    p,
                ),
                2 => Ok(Decoded { insts: vec![opaque_call()], next: p, ctrl: Ctrl::Fall }), // call r/m: opaque call, fall through
                4 => Ok(Decoded { insts: vec![], next: p, ctrl: Ctrl::Ret }), // jmp reg (tail/switch) → stop (conservative)
                _ => Err(CoreError::unsupported(format!("x86: unsupported group-5 /digit {}", m.reg & 7))),
            }
        }
        // Two-byte opcodes.
        0x0f => decode_two_byte(code, p, pos, rex_r, rex_x, rex_b, ty, flags, resolve),
        other => Err(CoreError::unsupported(format!("x86: unsupported opcode {other:#04x}"))),
    }
}

/// The **two-byte (`0F`-prefixed) opcode** arm of [`decode_one`], split out to keep that
/// function tractable. `p` points at the byte *after* `0F`; the other parameters are the
/// prefix/type context [`decode_one`] already computed. Behaviour-identical to the inline arm.
#[allow(clippy::too_many_arguments)]
fn decode_two_byte(
    code: &[u8],
    mut p: usize,
    pos: usize,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    ty: Type,
    flags: &mut Option<(Operand, Operand)>,
    resolve: RelocResolver,
) -> csolver_core::Result<Decoded> {
    let done = |insts: Vec<Inst>, next: usize| Ok(Decoded { insts, next, ctrl: Ctrl::Fall });
    let op2 = *code.get(p).ok_or_else(|| CoreError::parse(format!("x86: truncated 0F opcode at offset {p}")))?;
    p += 1;
    match op2 {
        // multi-byte nop (`0f 1f /M`) — consume the ModR/M operand, emit nothing.
        0x1f => {
            let m = modrm(code, p, rex_r, rex_b)?;
            let next = if m.mode == 0b11 {
                p + 1
            } else {
                mem_operand(code, p + 1, &m, rex_x, rex_b, resolve)?.next
            };
            Ok(Decoded { insts: vec![], next, ctrl: Ctrl::Fall })
        }
        // cmovcc r, r/m (`0f 40..4f`) — conditional move. Reg-reg only; the moved
        // value depends on flags we do not model precisely, so the destination
        // becomes an unknown (sound over-approximation) rather than dropping the
        // whole function. The memory-operand form loads the source (the read is checked)
        // and still leaves the destination unknown (the move is flag-conditional).
        0x40..=0x4f => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            let undef = RValue::Use(Operand::Const(csolver_ir::Const::Undef));
            if m.mode == 0b11 {
                done(vec![Inst::Assign { dst: reg(m.reg), ty, value: undef }], p)
            } else {
                // cmovcc r, [mem] — the load happens unconditionally (its access is checked);
                // the destination stays unknown since the move depends on flags we do not model.
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                let loaded = RegId(3000 + pos as u32);
                insts.push(Inst::Load { dst: loaded, ty: ty.clone(), ptr: Operand::Reg(ptr), align: 1, volatile: false });
                insts.push(Inst::Assign { dst: reg(m.reg), ty, value: undef });
                done(insts, mem.next)
            }
        }
        // jcc rel32.
        0x80..=0x8f => {
            let rel = read_imm(code, p, 4)? as u32 as i32 as i64;
            let np = p + 4;
            jcc(pos, np, branch_target(np, rel)?, op2 - 0x80, flags)
        }
        // setcc r/m8 (reg-reg only).
        0x90..=0x9f => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode != 0b11 {
                return Err(CoreError::unsupported("x86: setcc with a memory operand"));
            }
            let cond_creg = temp_reg(pos);
            let (cmp_op, lhs, rhs) = match (cc_cmpop(op2 - 0x90), flags) {
                (Some(op), Some((a, b))) => (op, a.clone(), b.clone()),
                _ => (CmpOp::Ne, Operand::Reg(RegId(2000 + pos as u32)), Operand::int(64, 0)),
            };
            let dst_target = reg(m.rm);
            done(
                vec![
                    Inst::Assign { dst: cond_creg, ty: Type::Bool, value: RValue::Cmp { op: cmp_op, lhs, rhs } },
                    Inst::Assign {
                        dst: dst_target,
                        ty: Type::int(8),
                        value: RValue::Cast {
                            op: CastOp::ZExt,
                            operand: Operand::Reg(cond_creg),
                            to: Type::int(8),
                        },
                    },
                ],
                p,
            )
        }
        // movzx r, r/m8 (0f b6).
        0xb6 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                done(
                    vec![Inst::Assign {
                        dst: reg(m.reg),
                        ty: ty.clone(),
                        value: RValue::Cast {
                            op: CastOp::ZExt,
                            operand: Operand::Reg(reg(m.rm)),
                            to: ty,
                        },
                    }],
                    p,
                )
            } else {
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                let tmp = temp_reg(pos);
                insts.push(Inst::Load { dst: tmp, ty: Type::int(8), ptr: Operand::Reg(ptr), align: 1 , volatile: false});
                insts.push(Inst::Assign {
                    dst: reg(m.reg),
                    ty: ty.clone(),
                    value: RValue::Cast { op: CastOp::ZExt, operand: Operand::Reg(tmp), to: ty },
                });
                done(insts, mem.next)
            }
        }
        // movzx r, r/m16 (0f b7).
        0xb7 => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                done(
                    vec![Inst::Assign {
                        dst: reg(m.reg),
                        ty: ty.clone(),
                        value: RValue::Cast {
                            op: CastOp::ZExt,
                            operand: Operand::Reg(reg(m.rm)),
                            to: ty,
                        },
                    }],
                    p,
                )
            } else {
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                let tmp = temp_reg(pos);
                insts.push(Inst::Load { dst: tmp, ty: Type::int(16), ptr: Operand::Reg(ptr), align: 1 , volatile: false});
                insts.push(Inst::Assign {
                    dst: reg(m.reg),
                    ty: ty.clone(),
                    value: RValue::Cast { op: CastOp::ZExt, operand: Operand::Reg(tmp), to: ty },
                });
                done(insts, mem.next)
            }
        }
        // movsx r, r/m8 (0f be).
        0xbe => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                done(
                    vec![Inst::Assign {
                        dst: reg(m.reg),
                        ty: ty.clone(),
                        value: RValue::Cast {
                            op: CastOp::SExt,
                            operand: Operand::Reg(reg(m.rm)),
                            to: ty,
                        },
                    }],
                    p,
                )
            } else {
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                let tmp = temp_reg(pos);
                insts.push(Inst::Load { dst: tmp, ty: Type::int(8), ptr: Operand::Reg(ptr), align: 1 , volatile: false});
                insts.push(Inst::Assign {
                    dst: reg(m.reg),
                    ty: ty.clone(),
                    value: RValue::Cast { op: CastOp::SExt, operand: Operand::Reg(tmp), to: ty },
                });
                done(insts, mem.next)
            }
        }
        // movsx r, r/m16 (0f bf).
        0xbf => {
            let m = modrm(code, p, rex_r, rex_b)?;
            p += 1;
            if m.mode == 0b11 {
                done(
                    vec![Inst::Assign {
                        dst: reg(m.reg),
                        ty: ty.clone(),
                        value: RValue::Cast {
                            op: CastOp::SExt,
                            operand: Operand::Reg(reg(m.rm)),
                            to: ty,
                        },
                    }],
                    p,
                )
            } else {
                let mem = mem_operand(code, p, &m, rex_x, rex_b, resolve)?;
                let (mut insts, ptr) = mem.lower(pos);
                let tmp = temp_reg(pos);
                insts.push(Inst::Load { dst: tmp, ty: Type::int(16), ptr: Operand::Reg(ptr), align: 1 , volatile: false});
                insts.push(Inst::Assign {
                    dst: reg(m.reg),
                    ty: ty.clone(),
                    value: RValue::Cast { op: CastOp::SExt, operand: Operand::Reg(tmp), to: ty },
                });
                done(insts, mem.next)
            }
        }
        _ => Err(CoreError::unsupported(format!("x86: unsupported opcode 0f {op2:#04x}"))),
    }
}

/// The precise byte→MSIR decoder does not model this opcode. Fall back to the rich
/// typed instruction decoder (`decode_instruction`, VEX/cmov/bt/… — ~160 tests) purely
/// for the instruction **length**, so a single unmodeled instruction does not drop the
/// *whole* function to `unanalyzed`. A **non-control-flow** instruction is skipped
/// *soundly*: an opaque call invalidates the memory model (read-your-writes cannot then
/// trust a value this instruction may have overwritten) and every GP register is havoc'd
/// to a fresh opaque value (a pointer it may have written is UNKNOWN, never trusted), so
/// the surrounding instructions keep their obligations while nothing this one did is
/// assumed safe. A control-flow instruction (Call/Jmp/Jcc/Ret/Syscall/Int3) must NOT be
/// skipped — a wrong CFG could be unsound — so it re-raises the original error (drop).
/// An opaque call: havocs the heap and binds rax (reg 0) to an unknown result. Used for
/// `call rel32`/`call r/m` so analysis continues past a call instead of dropping.
/// Neutralise one instruction of a **segment-prefixed** (`fs`/`gs`) access: a `Load` of
/// thread-local/per-CPU memory becomes an opaque value bound to the same register (we know
/// nothing about a canary / per-CPU base), and a `Store` to it is dropped (segment memory is
/// untracked and never aliases a tracked region). Every other instruction (the register
/// arithmetic the segment operand fed) passes through unchanged. Returns `None` to drop.
fn neutralize_segment_access(inst: Inst) -> Option<Inst> {
    match inst {
        Inst::Load { dst, ty, .. } => Some(Inst::Assign {
            dst,
            ty,
            value: RValue::Use(Operand::Const(csolver_ir::Const::Undef)),
        }),
        Inst::Store { .. } => None,
        other => Some(other),
    }
}

fn opaque_call() -> Inst {
    Inst::Call {
        dst: Some(reg(0)),
        callee: Callee::Symbol("<x86 call>".into()),
        args: vec![],
        ret_ty: Type::int(64),
        ret_ref: None,
    }
}

/// A **named** direct call: the resolved callee symbol, with the SysV integer argument
/// registers (`rdi, rsi, …`) as its arguments and `rax` as its result. Carries enough to
/// (a) match an API contract at a post-pass (the callee name + the size/pointer args) and
/// (b) resolve to an in-module callee summary. For a callee with neither, the executor
/// treats an unknown symbol exactly as the opaque call did (havoc), so this is never less
/// sound — only more informative.
fn named_call(name: String) -> Inst {
    Inst::Call {
        dst: Some(reg(0)),
        callee: Callee::Symbol(name),
        args: crate::x86::arg_operands(),
        ret_ty: Type::int(64),
        ret_ref: None,
    }
}

pub(super) fn bridge_unmodeled(code: &[u8], pos: usize, err: CoreError) -> csolver_core::Result<Decoded> {
    match decode_instruction(code, pos) {
        Ok(d) if d.length > 0 && !is_control_flow(&d.instruction) && !touches_memory(&d.instruction) => {
            let mut insts = vec![Inst::Call {
                dst: None,
                callee: csolver_ir::Callee::Symbol("<x86 unmodeled>".into()),
                args: vec![],
                ret_ty: Type::Unit,
                ret_ref: None,
            }];
            // Havoc every general-purpose register (0..=15): the instruction may have
            // written any of them (including rsp/rbp), so none may keep a stale value.
            for r in 0..16u8 {
                insts.push(Inst::Assign {
                    dst: reg(r),
                    ty: Type::int(64),
                    value: RValue::Use(Operand::Const(csolver_ir::Const::Undef)),
                });
            }
            Ok(Decoded { insts, next: pos + d.length, ctrl: Ctrl::Fall })
        }
        _ => Err(err),
    }
}

/// Whether a typed instruction **reads or writes memory** — either an explicit
/// `X86Operand::Mem` in any operand, or an implicit memory access (the stack for
/// `push`/`pop`/`pushf`/`popf`, `[rsi]`/`[rdi]` for the string ops). Such an
/// instruction must NOT be havoc-bridged: `bridge_unmodeled` only havocs registers,
/// so skipping a memory-touching instruction would silently drop its access — and a
/// dropped unchecked load/store through an invalid pointer could yield a **false PASS**.
/// So a memory-touching unmodeled instruction declines the bridge (the function drops to
/// UNKNOWN — sound). `lea` is NOT a memory access (it computes an address). Exhaustive by
/// design: a new `Instruction` variant breaks the build, forcing an explicit safe/unsafe
/// classification rather than defaulting into the havoc path.
fn touches_memory(i: &Instruction) -> bool {
    use Instruction as I;
    let m = |o: &X86Operand| matches!(o, X86Operand::Mem(..));
    match i {
        // Implicit memory: the stack and the string operations.
        I::Push(_) | I::Pop(_) | I::Pushf | I::Popf
        | I::Movs(_) | I::Stos(_) | I::Lods(_) | I::Scas(_) | I::Cmps(_) => true,
        // `lea` computes an effective address; it performs no memory access.
        I::Lea(..) => false,
        // Two-operand instructions: memory iff either operand is a memory operand.
        I::Mov(a, b) | I::Movzx(a, b) | I::Movsx(a, b) | I::Movsxd(a, b) | I::Add(a, b)
        | I::Sub(a, b) | I::Xor(a, b) | I::And(a, b) | I::Or(a, b) | I::Cmp(a, b) | I::Test(a, b)
        | I::Xchg(a, b) | I::Bsf(a, b) | I::Bsr(a, b) | I::Bt(a, b) | I::Bts(a, b) | I::Btr(a, b)
        | I::Btc(a, b) | I::Movaps(a, b) | I::Movapd(a, b) | I::Movups(a, b) | I::Movupd(a, b)
        | I::Movdqa(a, b) | I::Movdqu(a, b) | I::Movss(a, b) | I::Movsd(a, b) | I::Movq(a, b)
        | I::Movd(a, b) | I::Addps(a, b) | I::Addss(a, b) | I::Addpd(a, b) | I::Addsd(a, b)
        | I::Subps(a, b) | I::Subss(a, b) | I::Subpd(a, b) | I::Subsd(a, b) | I::Mulps(a, b)
        | I::Mulss(a, b) | I::Mulpd(a, b) | I::Mulsd(a, b) | I::Divps(a, b) | I::Divss(a, b)
        | I::Divpd(a, b) | I::Divsd(a, b) | I::Andps(a, b) | I::Andpd(a, b) | I::Orps(a, b)
        | I::Orpd(a, b) | I::Xorps(a, b) | I::Xorpd(a, b) | I::Andnps(a, b) | I::Andnpd(a, b)
        | I::Sqrtps(a, b) | I::Sqrtss(a, b) | I::Sqrtpd(a, b) | I::Sqrtsd(a, b) | I::Unpcklps(a, b)
        | I::Unpckhps(a, b) | I::Unpcklpd(a, b) | I::Unpckhpd(a, b) | I::Cvtps2dq(a, b)
        | I::Cvtdq2ps(a, b) | I::Cvttps2dq(a, b) | I::Cvtsi2ss(a, b) | I::Cvtsi2sd(a, b)
        | I::Cvtss2si(a, b) | I::Cvtsd2si(a, b) | I::Cvttss2si(a, b) | I::Cvttsd2si(a, b)
        | I::Maxps(a, b) | I::Minps(a, b) | I::Maxpd(a, b) | I::Minpd(a, b) | I::Maxss(a, b)
        | I::Minss(a, b) | I::Maxsd(a, b) | I::Minsd(a, b) | I::Comiss(a, b) | I::Comisd(a, b)
        | I::Ucomiss(a, b) | I::Ucomisd(a, b) | I::Pxor(a, b) | I::Paddq(a, b) | I::Psubq(a, b)
        | I::Pand(a, b) | I::Por(a, b) | I::Pshufb(a, b) | I::Phaddw(a, b) | I::Phaddd(a, b)
        | I::Phaddsw(a, b) | I::Pabsb(a, b) | I::Pabsw(a, b) | I::Pabsd(a, b) | I::Pmovsxbw(a, b)
        | I::Pmovsxbd(a, b) | I::Pmovsxbq(a, b) | I::Pmovsxwd(a, b) | I::Pmovsxwq(a, b)
        | I::Pmovsxdq(a, b) | I::Pmovzxbw(a, b) | I::Pmovzxbd(a, b) | I::Pmovzxbq(a, b)
        | I::Pmovzxwd(a, b) | I::Pmovzxwq(a, b) | I::Pmovzxdq(a, b) | I::Pmuldq(a, b)
        | I::Pmulld(a, b) | I::Pcmpeqq(a, b) | I::Pcmpgtq(a, b) | I::Pminsb(a, b) | I::Pminsd(a, b)
        | I::Pminuw(a, b) | I::Pminud(a, b) | I::Pmaxsb(a, b) | I::Pmaxsd(a, b) | I::Pmaxuw(a, b)
        | I::Pmaxud(a, b) | I::Phminposuw(a, b) => m(a) || m(b),
        // Three-operand (imm8) forms.
        I::Cmpps(a, b, _) | I::Cmppd(a, b, _) | I::Cmpss(a, b, _) | I::Cmpsd(a, b, _)
        | I::Shufps(a, b, _) | I::Shufpd(a, b, _) | I::Roundps(a, b, _) | I::Roundpd(a, b, _)
        | I::Roundss(a, b, _) | I::Roundsd(a, b, _) | I::Palignr(a, b, _) | I::Pinsrb(a, b, _)
        | I::Pinsrd(a, b, _) | I::Pinsrq(a, b, _) | I::Pextrb(a, b, _) | I::Pextrd(a, b, _)
        | I::Pextrq(a, b, _) => m(a) || m(b),
        I::Cmovcc(_, a, b) => m(a) || m(b),
        // One-operand data-processing.
        I::Neg(a) | I::Not(a) | I::Inc(a) | I::Dec(a) | I::Mul(a) | I::Imul(a) | I::Div(a)
        | I::Idiv(a) | I::Call(a) | I::Jmp(a) | I::Setcc(_, a) => m(a),
        I::Shl(a, _) | I::Shr(a, _) | I::Sar(a, _) | I::Rol(a, _) | I::Ror(a, _) | I::Rcl(a, _)
        | I::Rcr(a, _) => m(a),
        // No memory: no-operand / flag / register-implicit instructions.
        I::Nop | I::Ret | I::Syscall | I::Cdqe | I::Cqo | I::Int3 | I::Jcc(..) | I::Stc | I::Clc
        | I::Cmc | I::Std | I::Cld | I::Lahf | I::Sahf => false,
    }
}

/// Whether a typed instruction changes control flow — those must be decoded precisely
/// or dropped, never skipped as a data-processing havoc.
fn is_control_flow(i: &Instruction) -> bool {
    matches!(
        i,
        Instruction::Call(_)
            | Instruction::Jmp(_)
            | Instruction::Jcc(..)
            | Instruction::Ret
            | Instruction::Syscall
            | Instruction::Int3
    )
}
