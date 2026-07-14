//! Textual x86-64 assembly (`.s`) → MSIR — **AT&T and Intel** syntax.
//!
//! A focused frontend for compiler-emitted (`clang/gcc -S`, either
//! `-masm=att` or `-masm=intel`) and hand-written assembly. The two syntaxes
//! differ only in their *operand grammar* (`%rax`/`$imm`/`disp(%b,%i,s)` vs.
//! `rax`/`imm`/`[b + i*s + disp]`) and operand order (AT&T is `src, dst`; Intel
//! is `dst, src`). Each grammar parses one instruction's operands into a uniform
//! [`TextOp`] list in **AT&T order** (source first, destination last) plus the
//! access width; the *instruction semantics* below are then shared.
//!
//! Both reuse the architecture-independent CFG assembly ([`crate::blocks`]) and
//! the x86 register/condition helpers. An unrecognised mnemonic or operand fails
//! the enclosing function to `unanalyzed` (sound: never a guess), exactly like
//! the byte decoder.
//!
//! ## Pointer extraction
//! Every memory operand — `disp(%base,%index,scale)`, `[base + index*scale +
//! disp]`, or a RIP-relative `sym(%rip)` / `[rip + sym]` — lowers to a
//! `PtrOffset` chain (a real MSIR pointer, symbol-based for RIP-relative) and a
//! `Load`/`Store`, so machine-level pointer accesses carry the same in-bounds /
//! liveness obligations as source-level ones.

use crate::blocks::{build_blocks, Ctrl, DecodedInsn};
use crate::x86::{cc_cmpop, reg, temp_reg, MemOperand};
use csolver_core::{Error, RegionKind, Result};
use csolver_ir::{
    BinOp, Callee, Const, FuncId, Function, Inst, Module, Operand, RValue, RegId, Type,
};

/// One parsed textual operand, in a syntax-independent form. Widths are in bits.
pub(crate) enum TextOp {
    /// A register (x86 encoding number). Its width is folded into the
    /// instruction width by the grammar, so it need not be carried per operand.
    Reg(u8),
    /// An immediate (already sign-resolved to `i64`).
    Imm(i64),
    /// A memory reference `[base + index*scale + disp]` (or a symbol base).
    Mem(MemOperand),
    /// A branch/label target (a symbol or `.L…` name).
    Label(String),
}

/// Decode a whole `.s` translation unit into a module using `syntax`'s operand
/// grammar (one function per non-local `NAME:` label that carries instructions).
pub(crate) fn decode(source: &str, intel: bool) -> Module {
    let mut m = Module::new("asm");
    for (name, body) in split_functions(source) {
        match decode_function_lines(&body, intel) {
            Ok(f) => m.functions.push(Function {
                id: FuncId(m.functions.len() as u32),
                name,
                ..f
            }),
            Err(e) => m.unanalyzed.push((name, e.to_string())),
        }
    }
    m
}

/// AT&T-syntax entry point (`clang/gcc -S` default on Linux).
pub fn decode_att(source: &str) -> Module {
    decode(source, false)
}

/// Intel-syntax entry point (`clang -masm=intel` / MASM-style output).
pub fn decode_intel(source: &str) -> Module {
    decode(source, true)
}

/// Split the source into `(function name, its instruction/label lines)`. A
/// function starts at a **non-local** label (`foo:`, not `.L…:`) and runs until
/// the next such label, a `.size`, or `.cfi_endproc`. Shared by both syntaxes
/// (compiler output uses the same directive/label conventions either way).
fn split_functions(source: &str) -> Vec<(String, Vec<String>)> {
    let mut out: Vec<(String, Vec<String>)> = Vec::new();
    let mut cur: Option<(String, Vec<String>)> = None;
    for raw in source.lines() {
        let line = strip_comment(raw).trim();
        if line.is_empty() {
            continue;
        }
        if let Some(label) = line.strip_suffix(':') {
            if !label.starts_with(".L") && is_symbol(label) {
                if let Some(f) = cur.take() {
                    out.push(f);
                }
                cur = Some((label.to_string(), Vec::new()));
                continue;
            }
            if let Some((_, body)) = cur.as_mut() {
                body.push(line.to_string());
            }
            continue;
        }
        if line.starts_with(".size") || line.starts_with(".cfi_endproc") {
            if let Some(f) = cur.take() {
                out.push(f);
            }
            continue;
        }
        if line.starts_with('.') {
            continue; // any other directive (.text/.globl/.type/.p2align/.cfi_*/.intel_syntax/…)
        }
        if let Some((_, body)) = cur.as_mut() {
            body.push(line.to_string());
        }
    }
    if let Some(f) = cur.take() {
        out.push(f);
    }
    out
}

/// Decode one function's lines (instructions + local labels) into a `Function`.
fn decode_function_lines(lines: &[String], intel: bool) -> Result<Function> {
    // Pass 1: assign each instruction a sequential offset and record label → offset.
    let mut labels: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    let mut insns: Vec<&str> = Vec::new();
    for line in lines {
        if let Some(l) = line.strip_suffix(':') {
            labels.insert(l.to_string(), insns.len());
        } else {
            insns.push(line);
        }
    }
    // Pass 2: lower each instruction. `flags` carries the last cmp/test operands;
    // `fp` records that the frame-pointer idiom (`mov rbp, rsp`) is pending, so the
    // following `sub rsp, N` builds a precise frame (see `lower_alu_or_frame`).
    let mut decoded: Vec<DecodedInsn> = Vec::new();
    let mut flags: Option<(Operand, Operand)> = None;
    let mut fp = false;
    for (i, ins) in insns.iter().enumerate() {
        decoded.push(lower_insn(ins, i, &labels, &mut flags, &mut fp, intel)?);
    }
    let (blocks, entry) = build_blocks(decoded)?;
    Ok(Function {
        id: FuncId(0),
        name: String::new(),
        params: crate::x86::arg_registers(),
        ret_ty: Type::Unit,
        blocks,
        entry,
    })
}

/// Lower one instruction at sequential offset `off`. Dispatches the operand
/// grammar on `intel`, then runs the shared instruction semantics.
#[allow(clippy::too_many_arguments)]
fn lower_insn(
    ins: &str,
    off: usize,
    labels: &std::collections::HashMap<String, usize>,
    flags: &mut Option<(Operand, Operand)>,
    fp: &mut bool,
    intel: bool,
) -> Result<DecodedInsn> {
    let next = off + 1;
    let fall = |insts: Vec<Inst>| DecodedInsn {
        offset: off,
        next,
        insts,
        ctrl: Ctrl::Fall,
    };
    let (mnem, rest) = match ins.split_once(char::is_whitespace) {
        Some((m, r)) => (m, r.trim()),
        None => (ins, ""),
    };
    // Parse the operands (in AT&T order: source first, destination last) and the
    // instruction's base mnemonic + access width.
    let (base, width, ops) = if intel {
        intel::parse(mnem, rest)?
    } else {
        att::parse(mnem, rest)?
    };

    match base.as_str() {
        "ret" | "retq" => Ok(DecodedInsn {
            offset: off,
            next,
            insts: vec![],
            ctrl: Ctrl::Ret,
        }),
        "endbr64" | "endbr32" | "hlt" | "ud2" => Ok(fall(vec![])),
        _ if base.starts_with("nop") => Ok(fall(vec![])),
        "jmp" => Ok(DecodedInsn {
            offset: off,
            next,
            insts: vec![],
            ctrl: Ctrl::Jmp(label(&ops, 0, labels)?),
        }),
        // jcc: `j<cc>` — the condition is the cc suffix.
        _ if base.starts_with('j') && base.len() >= 2 => {
            let cc = jcc_code(&base[1..])
                .ok_or_else(|| Error::unsupported(format!("asm: jcc `{base}`")))?;
            let t = label(&ops, 0, labels)?;
            let cond = temp_reg(off);
            let (op, lhs, rhs) = match (cc_cmpop(cc), flags.clone()) {
                (Some(op), Some((a, b))) => (op, a, b),
                _ => (
                    csolver_ir::CmpOp::Ne,
                    Operand::Reg(RegId(2000 + off as u32)),
                    Operand::int(64, 0),
                ),
            };
            Ok(DecodedInsn {
                offset: off,
                next,
                insts: vec![Inst::Assign {
                    dst: cond,
                    ty: Type::Bool,
                    value: RValue::Cmp { op, lhs, rhs },
                }],
                ctrl: Ctrl::Jcc(t, cond),
            })
        }
        // cmp/test set the flags for a following jcc. Internal AT&T order is
        // (src, dst); the comparison is `dst <op> src` (cc_cmpop's convention).
        "cmp" | "test" => {
            let a = operand_value(op_at(&ops, 1)?, off, width)?; // dst
            let b = operand_value(op_at(&ops, 0)?, off, width)?; // src
            *flags = Some((a.value, b.value));
            let mut insts = a.pre;
            insts.extend(b.pre);
            Ok(fall(insts))
        }
        "mov" | "movabs" => {
            // Frame-pointer establishment `mov rbp, rsp` (AT&T-internal order
            // src=rsp(4), dst=rbp(5)): mark the frame pending so the next
            // `sub rsp, N` builds the precise frame region binding both rsp and rbp.
            if matches!(
                (op_at(&ops, 0), op_at(&ops, 1)),
                (Ok(TextOp::Reg(4)), Ok(TextOp::Reg(5)))
            ) {
                *fp = true;
            }
            lower_mov(&ops, off, width).map(&fall)
        }
        // Sign/zero-extending moves — the value flows through (model as a move).
        "movslq" | "movsbl" | "movzbl" | "movzwl" | "movswl" | "movsbq" | "movzbq" | "movsxd"
        | "movsx" | "movzx" => lower_mov(&ops, off, width).map(&fall),
        "lea" => lower_lea(&ops, off).map(&fall),
        "add" | "sub" | "and" | "or" | "xor" => {
            lower_alu_or_frame(&base, &ops, off, width, fp).map(&fall)
        }
        "inc" | "dec" => {
            let d = reg_of(op_at(&ops, 0)?)?;
            let bin = if base == "inc" {
                BinOp::Add
            } else {
                BinOp::Sub
            };
            Ok(fall(vec![Inst::Assign {
                dst: d,
                ty: Type::int(width),
                value: RValue::Bin {
                    op: bin,
                    lhs: Operand::Reg(d),
                    rhs: Operand::int(width, 1),
                    flags: Default::default(),
                },
            }]))
        }
        _ if base.starts_with("cmov") => {
            // Conditional move: destination becomes unknown (flags not modelled precisely).
            let d = reg_of(op_at(&ops, 1)?)?;
            Ok(fall(vec![Inst::Assign {
                dst: d,
                ty: Type::int(width),
                value: RValue::Use(Operand::Const(Const::Undef)),
            }]))
        }
        // push/pop: a callee-saved register spill/restore. The saved value always
        // lands on valid stack, so **not** modelling the store/load is sound (we
        // never claim an access safe that isn't) and avoids poisoning the frame
        // pointer: a `push` region flowing into `mov rbp, rsp` would make every
        // `[rbp - k]` local provably out of that tiny region — a false bug. `push`
        // is therefore a no-op; `pop` havocs its destination (its value is unknown
        // after an unmodelled load). Precise stack checking still applies to the
        // `sub rsp, N` frame (rsp-relative accesses), the common optimized shape.
        "push" => Ok(fall(vec![])),
        "pop" => {
            let d = reg_of(op_at(&ops, 0)?)?;
            Ok(fall(vec![Inst::Assign {
                dst: d,
                ty: Type::int(64),
                value: RValue::Use(Operand::Const(Const::Undef)),
            }]))
        }
        // `leave` = `mov rsp, rbp; pop rbp` — havoc rbp; rsp is re-established by the
        // caller's frame (or the next prologue). Sound (the restore is always valid).
        "leave" => Ok(fall(vec![Inst::Assign {
            dst: reg(5),
            ty: Type::int(64),
            value: RValue::Use(Operand::Const(Const::Undef)),
        }])),
        // call: an opaque call that returns and falls through (havocs caller-saved
        // state and rax), so analysis continues past it — strictly more than the
        // byte decoder's conservative stop. A direct `call sym` names the symbol; a
        // register/`*`-indirect target is an indirect call.
        "call" => Ok(fall(vec![lower_call(op_at(&ops, 0)?)])),
        _ => Err(Error::unsupported(format!("asm: mnemonic `{mnem}`"))),
    }
}

/// Lower a `call` to an opaque `Inst::Call` binding rax: a direct symbol target,
/// or an indirect call through a register / `*`-dereferenced operand.
fn lower_call(op: &TextOp) -> Inst {
    let callee = match op {
        TextOp::Label(name) => Callee::Symbol(name.trim_start_matches('*').to_string()),
        TextOp::Reg(n) => Callee::Indirect(Operand::Reg(reg(*n))),
        _ => Callee::Symbol("<indirect>".to_string()),
    };
    Inst::Call {
        dst: Some(reg(0)),
        callee,
        args: Vec::new(),
        ret_ty: Type::int(64),
        ret_ref: None,
    }
}

/// A parsed operand's MSIR value plus any address-computing insts.
struct OpVal {
    value: Operand,
    pre: Vec<Inst>,
}

fn op_at(ops: &[TextOp], i: usize) -> Result<&TextOp> {
    ops.get(i)
        .ok_or_else(|| Error::unsupported(format!("asm: missing operand {i}")))
}

fn reg_of(op: &TextOp) -> Result<RegId> {
    match op {
        TextOp::Reg(n) => Ok(reg(*n)),
        _ => Err(Error::unsupported("asm: expected a register operand")),
    }
}

/// The value of an operand: a register, an immediate, or a load from memory
/// (emitting the address computation + load into temporaries).
fn operand_value(op: &TextOp, off: usize, width: u32) -> Result<OpVal> {
    match op {
        TextOp::Reg(n) => Ok(OpVal {
            value: Operand::Reg(reg(*n)),
            pre: vec![],
        }),
        TextOp::Imm(v) => Ok(OpVal {
            value: Operand::int(width, *v as u128),
            pre: vec![],
        }),
        TextOp::Mem(mem) => {
            let (mut pre, ptr) = mem.lower(off);
            let loaded = RegId(3000 + off as u32);
            pre.push(Inst::Load {
                dst: loaded,
                ty: Type::int(width),
                ptr: Operand::Reg(ptr),
                align: 1,
                volatile: false,
            });
            Ok(OpVal {
                value: Operand::Reg(loaded),
                pre,
            })
        }
        TextOp::Label(l) => Err(Error::unsupported(format!(
            "asm: unexpected label operand `{l}`"
        ))),
    }
}

fn lower_mov(ops: &[TextOp], off: usize, width: u32) -> Result<Vec<Inst>> {
    let ty = Type::int(width);
    let src = operand_value(op_at(ops, 0)?, off, width)?;
    match op_at(ops, 1)? {
        TextOp::Reg(d) => {
            let mut insts = src.pre;
            insts.push(Inst::Assign {
                dst: reg(*d),
                ty,
                value: RValue::Use(src.value),
            });
            Ok(insts)
        }
        TextOp::Mem(mem) => {
            let (mut insts, ptr) = mem.lower(off);
            insts.extend(src.pre);
            insts.push(Inst::Store {
                ty,
                ptr: Operand::Reg(ptr),
                value: src.value,
                align: 1,
                volatile: false,
            });
            Ok(insts)
        }
        _ => Err(Error::unsupported(
            "asm: mov destination must be a register or memory",
        )),
    }
}

fn lower_lea(ops: &[TextOp], off: usize) -> Result<Vec<Inst>> {
    let d = reg_of(op_at(ops, 1)?)?;
    let TextOp::Mem(mem) = op_at(ops, 0)? else {
        return Err(Error::unsupported("asm: lea needs a memory operand"));
    };
    let (mut insts, ptr) = mem.lower(off);
    insts.push(Inst::Assign {
        dst: d,
        ty: Type::int(64),
        value: RValue::Use(Operand::Reg(ptr)),
    });
    Ok(insts)
}

/// `add/sub/and/or/xor`, with the stack-frame prologue special case: `sub $N,
/// %rsp` (rsp = register 4) allocates the frame region so `[rsp+disp]` is
/// checked against it; `add $N, %rsp` tears it down (a no-op).
fn lower_alu_or_frame(
    base: &str,
    ops: &[TextOp],
    off: usize,
    width: u32,
    fp: &mut bool,
) -> Result<Vec<Inst>> {
    if matches!(base, "add" | "sub") {
        if let (TextOp::Imm(n), TextOp::Reg(4)) = (op_at(ops, 0)?, op_at(ops, 1)?) {
            if base == "sub" {
                // A frame with an established frame pointer (`mov rbp, rsp` seen):
                // build one frame region for both rsp and rbp (see `frame_insts`).
                if std::mem::take(fp) {
                    return Ok(frame_insts(*n as u128, off));
                }
                return Ok(vec![Inst::Alloc {
                    dst: reg(4),
                    region: RegionKind::Stack,
                    elem: Type::int(8),
                    count: Operand::int(64, *n as u128),
                    align: 16,
                }]);
            }
            return Ok(vec![]); // `add $N, %rsp` — frame teardown, a no-op.
        }
    }
    let bin = match base {
        "add" => BinOp::Add,
        "sub" => BinOp::Sub,
        "and" => BinOp::And,
        "or" => BinOp::Or,
        "xor" => BinOp::Xor,
        _ => unreachable!(),
    };
    let ty = Type::int(width);
    let d = reg_of(op_at(ops, 1)?)?;
    // `xor %r, %r` / `xor r, r` is the zeroing idiom.
    if matches!(bin, BinOp::Xor) {
        if let (TextOp::Reg(a), TextOp::Reg(b)) = (op_at(ops, 0)?, op_at(ops, 1)?) {
            if a == b {
                return Ok(vec![Inst::Assign {
                    dst: d,
                    ty,
                    value: RValue::Use(Operand::int(width, 0)),
                }]);
            }
        }
    }
    let src = operand_value(op_at(ops, 0)?, off, width)?;
    let mut insts = src.pre;
    insts.push(Inst::Assign {
        dst: d,
        ty,
        value: RValue::Bin {
            op: bin,
            lhs: Operand::Reg(d),
            rhs: src.value,
            flags: Default::default(),
        },
    });
    Ok(insts)
}

/// The precise frame model for the `push rbp; mov rbp, rsp; sub rsp, N` idiom.
///
/// Allocates **one** stack region for the whole frame whose size is *bounded
/// below* by `N + 16` (the callee-owned locals + saved-rbp + return-address
/// slots, always present) but *open above* (the caller's frame extent is
/// unknown), then binds `rsp` to the region base and `rbp` to `base + N`:
///
/// * a local `[rbp - k]` (`k ≤ N`) or `[rsp + j]` (`j < N`) is provably in
///   bounds → **PASS**;
/// * the saved-rbp / return-address slots `[rbp + 0..16)` are in bounds → PASS;
/// * a stack-passed argument `[rbp + 16 + …]` lands in the caller's frame, whose
///   size is unknown, so it is neither provably in nor out of bounds → **UNKNOWN**
///   (honest — not a false bug);
/// * an access below `rsp` (`[rsp - x]` / `[rbp - (N + x)]`) has a negative
///   offset → provably out of bounds → **FAIL** (a real stack underflow).
///
/// The open-above bound is `size = (N + 16) + (fresh & 0xFFFF_FFFF)`: masking a
/// never-written (unconstrained) register to 32 bits makes the addend lie in
/// `[0, 2^32)` — a non-negative, non-wrapping symbolic size of at least `N + 16`
/// and at most `~4 GiB`, so no real access is ever wrongly refuted.
fn frame_insts(n: u128, off: usize) -> Vec<Inst> {
    // A never-assigned register reads as a fresh, unconstrained symbol.
    let fresh = RegId(3600 + off as u32);
    let headroom = RegId(3601 + off as u32);
    let size = RegId(3602 + off as u32);
    vec![
        // headroom = fresh & 0xFFFF_FFFF   ∈ [0, 2^32)
        Inst::Assign {
            dst: headroom,
            ty: Type::int(64),
            value: RValue::Bin {
                op: BinOp::And,
                lhs: Operand::Reg(fresh),
                rhs: Operand::int(64, 0xFFFF_FFFF),
                flags: Default::default(),
            },
        },
        // size = (N + 16) + headroom   ∈ [N+16, N+16+2^32)
        Inst::Assign {
            dst: size,
            ty: Type::int(64),
            value: RValue::Bin {
                op: BinOp::Add,
                lhs: Operand::int(64, n + 16),
                rhs: Operand::Reg(headroom),
                flags: Default::default(),
            },
        },
        // rsp = base of the frame region (offset 0).
        Inst::Alloc {
            dst: reg(4),
            region: RegionKind::Stack,
            elem: Type::int(8),
            count: Operand::Reg(size),
            align: 16,
        },
        // rbp = base + N (the top of the local area; locals are at negative offsets).
        Inst::PtrOffset {
            dst: reg(5),
            base: Operand::Reg(reg(4)),
            index: Operand::int(64, n),
            elem: Type::int(8),
        },
    ]
}

fn label(
    ops: &[TextOp],
    i: usize,
    labels: &std::collections::HashMap<String, usize>,
) -> Result<usize> {
    match ops.get(i) {
        Some(TextOp::Label(t)) => labels
            .get(t)
            .copied()
            .ok_or_else(|| Error::unsupported(format!("asm: branch to unknown label `{t}`"))),
        _ => Err(Error::unsupported("asm: branch needs a label operand")),
    }
}

/// The x86 condition code for a `j<cc>` / `cmov<cc>` suffix.
pub(crate) fn jcc_code(cc: &str) -> Option<u8> {
    Some(match cc {
        "b" | "c" | "nae" => 0x2,
        "ae" | "nb" | "nc" => 0x3,
        "e" | "z" => 0x4,
        "ne" | "nz" => 0x5,
        "be" | "na" => 0x6,
        "a" | "nbe" => 0x7,
        "s" => 0x8,
        "ns" => 0x9,
        "l" | "nge" => 0xc,
        "ge" | "nl" => 0xd,
        "le" | "ng" => 0xe,
        "g" | "nle" => 0xf,
        _ => return None,
    })
}

pub(crate) fn strip_comment(line: &str) -> &str {
    match line.find(['#', ';']) {
        Some(i) => &line[..i],
        None => line,
    }
}

fn is_symbol(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '.' || c == '$' || c == '@')
}

/// AT&T register name → x86 register number (sub-registers alias their 64-bit
/// reg). Shared by both grammars (Intel names are the same without the `%`).
pub(crate) fn reg_number(name: &str) -> Option<u8> {
    Some(match name {
        "rax" | "eax" | "ax" | "al" => 0,
        "rcx" | "ecx" | "cx" | "cl" => 1,
        "rdx" | "edx" | "dx" | "dl" => 2,
        "rbx" | "ebx" | "bx" | "bl" => 3,
        "rsp" | "esp" | "sp" | "spl" => 4,
        "rbp" | "ebp" | "bp" | "bpl" => 5,
        "rsi" | "esi" | "si" | "sil" => 6,
        "rdi" | "edi" | "di" | "dil" => 7,
        "rip" => return None, // handled specially by the memory grammar
        _ => {
            let core = name.strip_prefix('r')?;
            let digits = core.trim_end_matches(['d', 'w', 'b']);
            let n: u8 = digits.parse().ok()?;
            if (8..=15).contains(&n) {
                n
            } else {
                return None;
            }
        }
    })
}

/// The bit width a register name denotes (`rax`=64, `eax`=32, `ax`=16, `al`=8;
/// `r8`=64, `r8d`=32, `r8w`=16, `r8b`=8). Used by the Intel grammar to size an
/// instruction that carries no explicit `ptr` keyword.
pub(crate) fn reg_width(name: &str) -> u32 {
    match name {
        "rax" | "rcx" | "rdx" | "rbx" | "rsp" | "rbp" | "rsi" | "rdi" => 64,
        "eax" | "ecx" | "edx" | "ebx" | "esp" | "ebp" | "esi" | "edi" => 32,
        "ax" | "cx" | "dx" | "bx" | "sp" | "bp" | "si" | "di" => 16,
        "al" | "cl" | "dl" | "bl" | "spl" | "bpl" | "sil" | "dil" => 8,
        _ => match name.strip_prefix('r').and_then(|c| c.chars().last()) {
            Some('d') => 32,
            Some('w') => 16,
            Some('b') => 8,
            _ => 64,
        },
    }
}

mod att;
mod intel;

#[cfg(test)]
#[path = "x86text_tests.rs"]
mod tests;
