use super::*;

impl Condition {
    pub(crate) fn from_cc(cc: u8) -> Option<Condition> {
        match cc {
            0x0 => Some(Condition::O),
            0x1 => Some(Condition::NO),
            0x2 => Some(Condition::B),
            0x3 => Some(Condition::AE),
            0x4 => Some(Condition::E),
            0x5 => Some(Condition::NE),
            0x6 => Some(Condition::BE),
            0x7 => Some(Condition::A),
            0x8 => Some(Condition::S),
            0x9 => Some(Condition::NS),
            0xa => Some(Condition::P),
            0xb => Some(Condition::NP),
            0xc => Some(Condition::L),
            0xd => Some(Condition::GE),
            0xe => Some(Condition::LE),
            0xf => Some(Condition::G),
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
    /// `nop` (0x90, 0x0f 0x1f ...).
    Nop,
    /// `mov dst, src` — register, memory, and immediate moves.
    Mov(X86Operand, X86Operand),
    /// `movzx dst, src` — move with zero-extension.
    Movzx(X86Operand, X86Operand),
    /// `movsx dst, src` — move with sign-extension.
    Movsx(X86Operand, X86Operand),
    /// `lea dst, mem` — load effective address.
    Lea(Reg, Width, Mem),
    /// `add dst, src`.
    Add(X86Operand, X86Operand),
    /// `sub dst, src`.
    Sub(X86Operand, X86Operand),
    /// `xor dst, src`.
    Xor(X86Operand, X86Operand),
    /// `and dst, src`.
    And(X86Operand, X86Operand),
    /// `or dst, src`.
    Or(X86Operand, X86Operand),
    /// `cmp a, b`.
    Cmp(X86Operand, X86Operand),
    /// `test a, b`.
    Test(X86Operand, X86Operand),
    /// `push src`.
    Push(X86Operand),
    /// `pop dst`.
    Pop(X86Operand),
    /// `call target`.
    Call(X86Operand),
    /// `jmp target`.
    Jmp(X86Operand),
    /// `jcc target`.
    Jcc(Condition, i64),
    /// `ret`.
    Ret,
    /// `syscall`.
    Syscall,
    /// `cdqe` (0x98) — sign-extend eax to rax; `cdqe` if REX.W else `cdqe` (32→64).
    Cdqe,
    /// `cqo` (0x99) — sign-extend rax to rdx:rax.
    Cqo,
    /// `int3` (0xcc).
    Int3,
    /// `xchg a, b`.
    Xchg(X86Operand, X86Operand),
    /// `neg dst` (0xf6/0xf7 /3).
    Neg(X86Operand),
    /// `not dst` (0xf6/0xf7 /2).
    Not(X86Operand),
    /// `inc dst` (0xfe/0xff /0).
    Inc(X86Operand),
    /// `dec dst` (0xfe/0xff /1).
    Dec(X86Operand),
    /// `mul src` — unsigned multiply (0xf6/0xf7 /4).
    Mul(X86Operand),
    /// `imul src` — signed multiply (0xf6/0xf7 /5).
    Imul(X86Operand),
    /// `div src` — unsigned divide (0xf6/0xf7 /6).
    Div(X86Operand),
    /// `idiv src` — signed divide (0xf6/0xf7 /7).
    Idiv(X86Operand),
    /// `shl dst, count` — left shift by imm8 or 1.
    Shl(X86Operand, u8),
    /// `shr dst, count` — logical right shift.
    Shr(X86Operand, u8),
    /// `sar dst, count` — arithmetic right shift.
    Sar(X86Operand, u8),
    /// `cmovcc dst, src` — conditional move (0f 0x40..0x4f).
    Cmovcc(Condition, X86Operand, X86Operand),
    /// `setcc dst` — set byte on condition (0f 0x90..0x9f).
    Setcc(Condition, X86Operand),
    /// `rol dst, count` — rotate left (Group 2 /0).
    Rol(X86Operand, u8),
    /// `ror dst, count` — rotate right (Group 2 /1).
    Ror(X86Operand, u8),
    /// `rcl dst, count` — rotate through carry left (Group 2 /2).
    Rcl(X86Operand, u8),
    /// `rcr dst, count` — rotate through carry right (Group 2 /3).
    Rcr(X86Operand, u8),
    /// `movsxd dst, src` — move with sign-extension dword→qword (0x63).
    Movsxd(X86Operand, X86Operand),
    /// `bsf dst, src` — bit scan forward (0f bc).
    Bsf(X86Operand, X86Operand),
    /// `bsr dst, src` — bit scan reverse (0f bd).
    Bsr(X86Operand, X86Operand),
    /// `bt src, pos` — bit test (0f a3).
    Bt(X86Operand, X86Operand),
    /// `bts dst, pos` — bit test and set (0f ab).
    Bts(X86Operand, X86Operand),
    /// `btr dst, pos` — bit test and reset (0f b3).
    Btr(X86Operand, X86Operand),
    /// `btc dst, pos` — bit test and complement (0f bb).
    Btc(X86Operand, X86Operand),
    /// `stc` — set carry flag (0xf9).
    Stc,
    /// `clc` — clear carry flag (0xf8).
    Clc,
    /// `cmc` — complement carry flag (0xf5).
    Cmc,
    /// `std` — set direction flag (0xfd).
    Std,
    /// `cld` — clear direction flag (0xfc).
    Cld,
    /// `lahf` — load flags into AH (0x9f).
    Lahf,
    /// `sahf` — store AH into flags (0x9e).
    Sahf,
    /// `pushf` — push flags (0x9c).
    Pushf,
    /// `popf` — pop flags (0x9d).
    Popf,
    /// `movs` — string move [rdi]←[rsi] (0xa4/0xa5).
    Movs(Width),
    /// `stos` — string store [rdi]←rAX (0xaa/0xab).
    Stos(Width),
    /// `lods` — string load rAX←[rsi] (0xac/0xad).
    Lods(Width),
    /// `scas` — string scan cmp rAX, [rdi] (0xae/0xaf).
    Scas(Width),
    /// `cmps` — string compare [rdi]←[rsi] (0xa6/0xa7).
    Cmps(Width),
    // ====================================================================
    // SSE / AVX instructions
    // ====================================================================
    /// `movaps dst, src` — move aligned packed singles (0F 28 /r, VEX.128 equivalent).
    Movaps(X86Operand, X86Operand),
    /// `movapd dst, src` — move aligned packed doubles (66 0F 28 /r).
    Movapd(X86Operand, X86Operand),
    /// `movups dst, src` — move unaligned packed singles (0F 10 /r).
    Movups(X86Operand, X86Operand),
    /// `movupd dst, src` — move unaligned packed doubles (66 0F 10 /r).
    Movupd(X86Operand, X86Operand),
    /// `movdqa dst, src` — move aligned packed integers (66 0F 6F /r).
    Movdqa(X86Operand, X86Operand),
    /// `movdqu dst, src` — move unaligned packed integers (F3 0F 6F /r).
    Movdqu(X86Operand, X86Operand),
    /// `movss dst, src` — move scalar single (F3 0F 10 /r).
    Movss(X86Operand, X86Operand),
    /// `movsd dst, src` — move scalar double (F2 0F 10 /r).
    Movsd(X86Operand, X86Operand),
    /// `movq dst, src` — move quadword between XMM and GPR/mem (66 0F 6E/D6, F3 0F 7E).
    Movq(X86Operand, X86Operand),
    /// `movd dst, src` — move doubleword between XMM and GPR/mem (66 0F 6E/D6).
    Movd(X86Operand, X86Operand),
    /// `addps dst, src` — packed single add (0F 58 /r).
    Addps(X86Operand, X86Operand),
    /// `addss dst, src` — scalar single add (F3 0F 58 /r).
    Addss(X86Operand, X86Operand),
    /// `addpd dst, src` — packed double add (66 0F 58 /r).
    Addpd(X86Operand, X86Operand),
    /// `addsd dst, src` — scalar double add (F2 0F 58 /r).
    Addsd(X86Operand, X86Operand),
    /// `subps dst, src` — packed single subtract (0F 5C /r).
    Subps(X86Operand, X86Operand),
    /// `subss dst, src` — scalar single subtract (F3 0F 5C /r).
    Subss(X86Operand, X86Operand),
    /// `subpd dst, src` — packed double subtract (66 0F 5C /r).
    Subpd(X86Operand, X86Operand),
    /// `subsd dst, src` — scalar double subtract (F2 0F 5C /r).
    Subsd(X86Operand, X86Operand),
    /// `mulps dst, src` — packed single multiply (0F 59 /r).
    Mulps(X86Operand, X86Operand),
    /// `mulss dst, src` — scalar single multiply (F3 0F 59 /r).
    Mulss(X86Operand, X86Operand),
    /// `mulpd dst, src` — packed double multiply (66 0F 59 /r).
    Mulpd(X86Operand, X86Operand),
    /// `mulsd dst, src` — scalar double multiply (F2 0F 59 /r).
    Mulsd(X86Operand, X86Operand),
    /// `divps dst, src` — packed single divide (0F 5E /r).
    Divps(X86Operand, X86Operand),
    /// `divss dst, src` — scalar single divide (F3 0F 5E /r).
    Divss(X86Operand, X86Operand),
    /// `divpd dst, src` — packed double divide (66 0F 5E /r).
    Divpd(X86Operand, X86Operand),
    /// `divsd dst, src` — scalar double divide (F2 0F 5E /r).
    Divsd(X86Operand, X86Operand),
    /// `andps dst, src` — packed single bitwise and (0F 54 /r).
    Andps(X86Operand, X86Operand),
    /// `andpd dst, src` — packed double bitwise and (66 0F 54 /r).
    Andpd(X86Operand, X86Operand),
    /// `orps dst, src` — packed single bitwise or (0F 56 /r).
    Orps(X86Operand, X86Operand),
    /// `orpd dst, src` — packed double bitwise or (66 0F 56 /r).
    Orpd(X86Operand, X86Operand),
    /// `xorps dst, src` — packed single bitwise xor (0F 57 /r).
    Xorps(X86Operand, X86Operand),
    /// `xorpd dst, src` — packed double bitwise xor (66 0F 57 /r).
    Xorpd(X86Operand, X86Operand),
    /// `andnps dst, src` — packed single bitwise and-not (0F 55 /r).
    Andnps(X86Operand, X86Operand),
    /// `andnpd dst, src` — packed double bitwise and-not (66 0F 55 /r).
    Andnpd(X86Operand, X86Operand),
    /// `sqrtps dst, src` — packed single sqrt (0F 51 /r).
    Sqrtps(X86Operand, X86Operand),
    /// `sqrtss dst, src` — scalar single sqrt (F3 0F 51 /r).
    Sqrtss(X86Operand, X86Operand),
    /// `sqrtpd dst, src` — packed double sqrt (66 0F 51 /r).
    Sqrtpd(X86Operand, X86Operand),
    /// `sqrtsd dst, src` — scalar double sqrt (F2 0F 51 /r).
    Sqrtsd(X86Operand, X86Operand),
    /// `cmpps dst, src, imm` — packed single compare (0F C2 /r ib).
    Cmpps(X86Operand, X86Operand, u8),
    /// `cmppd dst, src, imm` — packed double compare (66 0F C2 /r ib).
    Cmppd(X86Operand, X86Operand, u8),
    /// `cmpss dst, src, imm` — scalar single compare (F3 0F C2 /r ib).
    Cmpss(X86Operand, X86Operand, u8),
    /// `cmpsd dst, src, imm` — scalar double compare (F2 0F C2 /r ib).
    Cmpsd(X86Operand, X86Operand, u8),
    /// `shufps dst, src, imm` — packed single shuffle (0F C6 /r ib).
    Shufps(X86Operand, X86Operand, u8),
    /// `shufpd dst, src, imm` — packed double shuffle (66 0F C6 /r ib).
    Shufpd(X86Operand, X86Operand, u8),
    /// `unpcklps dst, src` — unpack low singles (0F 14 /r).
    Unpcklps(X86Operand, X86Operand),
    /// `unpckhps dst, src` — unpack high singles (0F 15 /r).
    Unpckhps(X86Operand, X86Operand),
    /// `unpcklpd dst, src` — unpack low doubles (66 0F 14 /r).
    Unpcklpd(X86Operand, X86Operand),
    /// `unpckhpd dst, src` — unpack high doubles (66 0F 15 /r).
    Unpckhpd(X86Operand, X86Operand),
    /// `cvtps2dq dst, src` — convert packed singles to dwords (66 0F 5B /r).
    Cvtps2dq(X86Operand, X86Operand),
    /// `cvtdq2ps dst, src` — convert packed dwords to singles (0F 5B /r).
    Cvtdq2ps(X86Operand, X86Operand),
    /// `cvttps2dq dst, src` — truncate packed singles to dwords (F3 0F 5B /r).
    Cvttps2dq(X86Operand, X86Operand),
    /// `cvtsi2ss dst, src` — convert dword/qword (GPR) to scalar single (F3 0F 2A /r).
    Cvtsi2ss(X86Operand, X86Operand),
    /// `cvtsi2sd dst, src` — convert dword/qword (GPR) to scalar double (F2 0F 2A /r).
    Cvtsi2sd(X86Operand, X86Operand),
    /// `cvtss2si dst, src` — convert scalar single to dword/qword (F3 0F 2D /r).
    Cvtss2si(X86Operand, X86Operand),
    /// `cvtsd2si dst, src` — convert scalar double to dword/qword (F2 0F 2D /r).
    Cvtsd2si(X86Operand, X86Operand),
    /// `cvttss2si dst, src` — truncate scalar single to dword/qword (F3 0F 2C /r).
    Cvttss2si(X86Operand, X86Operand),
    /// `cvttsd2si dst, src` — truncate scalar double to dword/qword (F2 0F 2C /r).
    Cvttsd2si(X86Operand, X86Operand),
    /// `maxps dst, src` — packed single maximum (0F 5F /r).
    Maxps(X86Operand, X86Operand),
    /// `minps dst, src` — packed single minimum (0F 5D /r).
    Minps(X86Operand, X86Operand),
    /// `maxpd dst, src` — packed double maximum (66 0F 5F /r).
    Maxpd(X86Operand, X86Operand),
    /// `minpd dst, src` — packed double minimum (66 0F 5D /r).
    Minpd(X86Operand, X86Operand),
    /// `maxss dst, src` — scalar single maximum (F3 0F 5F /r).
    Maxss(X86Operand, X86Operand),
    /// `minss dst, src` — scalar single minimum (F3 0F 5D /r).
    Minss(X86Operand, X86Operand),
    /// `maxsd dst, src` — scalar double maximum (F2 0F 5F /r).
    Maxsd(X86Operand, X86Operand),
    /// `minsd dst, src` — scalar double minimum (F2 0F 5D /r).
    Minsd(X86Operand, X86Operand),
    /// `comiss dst, src` — compare scalar single ordered (0F 2F /r).
    Comiss(X86Operand, X86Operand),
    /// `comisd dst, src` — compare scalar double ordered (66 0F 2F /r).
    Comisd(X86Operand, X86Operand),
    /// `ucomiss dst, src` — compare scalar single unordered (0F 2E /r).
    Ucomiss(X86Operand, X86Operand),
    /// `ucomisd dst, src` — compare scalar double unordered (66 0F 2E /r).
    Ucomisd(X86Operand, X86Operand),
    /// `pxor dst, src` — packed integer xor (66 0F EF /r).
    Pxor(X86Operand, X86Operand),
    /// `paddq dst, src` — packed quadword add (66 0F D4 /r).
    Paddq(X86Operand, X86Operand),
    /// `psubq dst, src` — packed quadword subtract (66 0F FB /r).
    Psubq(X86Operand, X86Operand),
    /// `pand dst, src` — packed integer and (66 0F DB /r).
    Pand(X86Operand, X86Operand),
    /// `por dst, src` — packed integer or (66 0F EB /r).
    Por(X86Operand, X86Operand),
    // --- SSSE3 (0F38 map, VEX.mmmmm=2) ---
    /// `pshufb dst, src` — packed shuffle bytes (66 0F 38 00 /r).
    Pshufb(X86Operand, X86Operand),
    /// `phaddw dst, src` — packed horizontal add words (66 0F 38 01 /r).
    Phaddw(X86Operand, X86Operand),
    /// `phaddd dst, src` — packed horizontal add dwords (66 0F 38 02 /r).
    Phaddd(X86Operand, X86Operand),
    /// `phaddsw dst, src` — packed horizontal add words saturated (66 0F 38 03 /r).
    Phaddsw(X86Operand, X86Operand),
    /// `pabsb dst, src` — packed absolute value bytes (66 0F 38 1C /r).
    Pabsb(X86Operand, X86Operand),
    /// `pabsw dst, src` — packed absolute value words (66 0F 38 1D /r).
    Pabsw(X86Operand, X86Operand),
    /// `pabsd dst, src` — packed absolute value dwords (66 0F 38 1E /r).
    Pabsd(X86Operand, X86Operand),
    // --- SSE4.1 (0F38 map, 66 prefix required) ---
    /// `pmovsxbw dst, src` — sign extend bytes to words (66 0F 38 20 /r).
    Pmovsxbw(X86Operand, X86Operand),
    /// `pmovsxbd dst, src` — sign extend bytes to dwords (66 0F 38 21 /r).
    Pmovsxbd(X86Operand, X86Operand),
    /// `pmovsxbq dst, src` — sign extend bytes to qwords (66 0F 38 22 /r).
    Pmovsxbq(X86Operand, X86Operand),
    /// `pmovsxwd dst, src` — sign extend words to dwords (66 0F 38 23 /r).
    Pmovsxwd(X86Operand, X86Operand),
    /// `pmovsxwq dst, src` — sign extend words to qwords (66 0F 38 24 /r).
    Pmovsxwq(X86Operand, X86Operand),
    /// `pmovsxdq dst, src` — sign extend dwords to qwords (66 0F 38 25 /r).
    Pmovsxdq(X86Operand, X86Operand),
    /// `pmovzxbw dst, src` — zero extend bytes to words (66 0F 38 30 /r).
    Pmovzxbw(X86Operand, X86Operand),
    /// `pmovzxbd dst, src` — zero extend bytes to dwords (66 0F 38 31 /r).
    Pmovzxbd(X86Operand, X86Operand),
    /// `pmovzxbq dst, src` — zero extend bytes to qwords (66 0F 38 32 /r).
    Pmovzxbq(X86Operand, X86Operand),
    /// `pmovzxwd dst, src` — zero extend words to dwords (66 0F 38 33 /r).
    Pmovzxwd(X86Operand, X86Operand),
    /// `pmovzxwq dst, src` — zero extend words to qwords (66 0F 38 34 /r).
    Pmovzxwq(X86Operand, X86Operand),
    /// `pmovzxdq dst, src` — zero extend dwords to qwords (66 0F 38 35 /r).
    Pmovzxdq(X86Operand, X86Operand),
    /// `pmuldq dst, src` — packed multiply qwords (66 0F 38 28 /r).
    Pmuldq(X86Operand, X86Operand),
    /// `pmulld dst, src` — packed multiply low dwords (66 0F 38 40 /r).
    Pmulld(X86Operand, X86Operand),
    /// `pcmpeqq dst, src` — packed compare qword equal (66 0F 38 29 /r).
    Pcmpeqq(X86Operand, X86Operand),
    /// `pcmpgtq dst, src` — packed compare qword greater (66 0F 38 37 /r).
    Pcmpgtq(X86Operand, X86Operand),
    /// `pminsb dst, src` — packed min signed bytes (66 0F 38 38 /r).
    Pminsb(X86Operand, X86Operand),
    /// `pminsd dst, src` — packed min signed dwords (66 0F 38 39 /r).
    Pminsd(X86Operand, X86Operand),
    /// `pminuw dst, src` — packed min unsigned words (66 0F 38 3A /r).
    Pminuw(X86Operand, X86Operand),
    /// `pminud dst, src` — packed min unsigned dwords (66 0F 38 3B /r).
    Pminud(X86Operand, X86Operand),
    /// `pmaxsb dst, src` — packed max signed bytes (66 0F 38 3C /r).
    Pmaxsb(X86Operand, X86Operand),
    /// `pmaxsd dst, src` — packed max signed dwords (66 0F 38 3D /r).
    Pmaxsd(X86Operand, X86Operand),
    /// `pmaxuw dst, src` — packed max unsigned words (66 0F 38 3E /r).
    Pmaxuw(X86Operand, X86Operand),
    /// `pmaxud dst, src` — packed max unsigned dwords (66 0F 38 3F /r).
    Pmaxud(X86Operand, X86Operand),
    /// `phminposuw dst, src` — packed horizontal min unsigned word (66 0F 38 41 /r).
    Phminposuw(X86Operand, X86Operand),
    // --- SSE4.1 (0F3A map, VEX.mmmmm=3) ---
    /// `roundps dst, src, imm` — round packed single (66 0F 3A 08 /r ib).
    Roundps(X86Operand, X86Operand, u8),
    /// `roundpd dst, src, imm` — round packed double (66 0F 3A 09 /r ib).
    Roundpd(X86Operand, X86Operand, u8),
    /// `roundss dst, src, imm` — round scalar single (66 0F 3A 0A /r ib).
    Roundss(X86Operand, X86Operand, u8),
    /// `roundsd dst, src, imm` — round scalar double (66 0F 3A 0B /r ib).
    Roundsd(X86Operand, X86Operand, u8),
    /// `palignr dst, src, imm` — packed align right (66 0F 3A 0F /r ib).
    Palignr(X86Operand, X86Operand, u8),
    /// `pinsrb dst, src, imm` — insert byte (66 0F 3A 20 /r ib).
    Pinsrb(X86Operand, X86Operand, u8),
    /// `pinsrd dst, src, imm` — insert dword (66 0F 3A 22 /r ib).
    Pinsrd(X86Operand, X86Operand, u8),
    /// `pinsrq dst, src, imm` — insert qword (66 0F 3A 22 /r ib, REX.W).
    Pinsrq(X86Operand, X86Operand, u8),
    /// `pextrb dst, src, imm` — extract byte (66 0F 3A 14 /r ib).
    Pextrb(X86Operand, X86Operand, u8),
    /// `pextrd dst, src, imm` — extract dword (66 0F 3A 16 /r ib).
    Pextrd(X86Operand, X86Operand, u8),
    /// `pextrq dst, src, imm` — extract qword (66 0F 3A 16 /r ib, REX.W).
    Pextrq(X86Operand, X86Operand, u8),
}
