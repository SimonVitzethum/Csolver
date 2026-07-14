//! Textual **AArch64** assembly (`.s`) → MSIR (`clang --target=aarch64 -S`).
//!
//! Mirrors the x86 text frontend: it reuses the architecture-independent CFG
//! assembly ([`crate::blocks`]) and lowers a common instruction subset, failing
//! the whole function to `unanalyzed` on anything unrecognised (sound — never a
//! guess). Registers `x0..x30`/`w0..w30`/`sp` map to MSIR `RegId`s by their
//! encoding number; the zero register (`xzr`/`wzr`) is a literal 0.
//!
//! ## Pointer extraction
//! Every `[base, #off]` / `[base, index, lsl #s]` / `[base]` access lowers to a
//! `PtrOffset` + `Load`/`Store`; `adrp`/`adr`(+`:lo12:` `add`) materialise a
//! symbol pointer, so a `ldr` off a global address is bounds-checked. `stp`/`ldp`
//! (pair — the standard prologue save/restore) become two accesses.

use crate::blocks::{build_blocks, Ctrl, DecodedInsn};
use csolver_core::{Error, RegionKind, Result};
use csolver_ir::{
    BinOp, Callee, CmpOp, Const, FuncId, Function, Inst, Module, Operand, RValue, RegId, Type,
};

/// The stack-pointer register number (also `sp`/register 31 in the memory and
/// add/sub-immediate forms).
const SP: u8 = 31;

fn reg(num: u8) -> RegId {
    RegId(num as u32)
}

fn temp_reg(pos: usize) -> RegId {
    RegId(1000 + pos as u32)
}

/// Decode a whole AArch64 `.s` translation unit into a module.
pub fn decode(source: &str) -> Module {
    let mut m = Module::new("asm");
    for (name, body) in split_functions(source) {
        match decode_function_lines(&body) {
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

/// The AArch64 PCS integer argument registers `x0..x7`, modelled as parameters.
fn arg_registers() -> Vec<(RegId, Type)> {
    (0u8..8).map(|r| (reg(r), Type::int(64))).collect()
}

/// Split into `(function name, lines)` — same label/directive conventions as x86.
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
            continue;
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

fn decode_function_lines(lines: &[String]) -> Result<Function> {
    let mut labels: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    let mut insns: Vec<&str> = Vec::new();
    for line in lines {
        if let Some(l) = line.strip_suffix(':') {
            labels.insert(l.to_string(), insns.len());
        } else {
            insns.push(line);
        }
    }
    let mut decoded: Vec<DecodedInsn> = Vec::new();
    let mut flags: Option<(Operand, Operand)> = None;
    for (i, ins) in insns.iter().enumerate() {
        decoded.push(lower_insn(ins, i, &labels, &mut flags)?);
    }
    let (blocks, entry) = build_blocks(decoded)?;
    Ok(Function {
        id: FuncId(0),
        name: String::new(),
        params: arg_registers(),
        ret_ty: Type::Unit,
        blocks,
        entry,
    })
}

fn lower_insn(
    ins: &str,
    off: usize,
    labels: &std::collections::HashMap<String, usize>,
    flags: &mut Option<(Operand, Operand)>,
) -> Result<DecodedInsn> {
    let next = off + 1;
    let fall = |insts: Vec<Inst>| DecodedInsn {
        offset: off,
        next,
        insts,
        ctrl: Ctrl::Fall,
    };
    let (mnem, rest) = match ins.split_once(char::is_whitespace) {
        Some((m, r)) => (m.trim(), r.trim()),
        None => (ins.trim(), ""),
    };
    let ops = split_operands(rest);
    let width = |r: &str| {
        if r.trim_start().starts_with('w') {
            32
        } else {
            64
        }
    };

    match mnem {
        "ret" => Ok(DecodedInsn {
            offset: off,
            next,
            insts: vec![],
            ctrl: Ctrl::Ret,
        }),
        "nop" => Ok(fall(vec![])),
        // A call (`bl sym`/`blr Xn`) returns and falls through: model it as an
        // opaque `Inst::Call` binding x0 (havocs caller-saved state), so analysis
        // continues past it. `svc`/`brk` trap — stop analysis (sound).
        "bl" | "blr" => Ok(fall(vec![lower_call(&ops)])),
        "svc" | "brk" => Ok(DecodedInsn {
            offset: off,
            next,
            insts: vec![],
            ctrl: Ctrl::Ret,
        }),
        "b" => Ok(DecodedInsn {
            offset: off,
            next,
            insts: vec![],
            ctrl: Ctrl::Jmp(label(&ops, 0, labels)?),
        }),
        // b.<cond> — the mnemonic carries the condition after the dot.
        _ if mnem.starts_with("b.") => {
            let cc = cc_name(&mnem[2..])
                .ok_or_else(|| Error::unsupported(format!("arm64: cond `{mnem}`")))?;
            branch(off, next, label(&ops, 0, labels)?, cc, flags.clone())
        }
        // cbz/cbnz Rn, label — compare-and-branch against zero.
        "cbz" | "cbnz" => {
            let rn = reg_of(&ops, 0)?;
            let t = label(&ops, 1, labels)?;
            let op = if mnem == "cbz" { CmpOp::Eq } else { CmpOp::Ne };
            branch_cmp(off, next, t, op, Operand::Reg(rn), Operand::int(64, 0))
        }
        "mov" => {
            let d = reg_of(&ops, 0)?;
            let src = value_operand(&ops, 1, width(ops[0]))?;
            Ok(fall(vec![Inst::Assign {
                dst: d,
                ty: Type::int(width(ops[0])),
                value: RValue::Use(src),
            }]))
        }
        "add" | "sub" => lower_addsub(mnem, &ops).map(fall),
        "and" | "orr" | "eor" | "lsl" | "lsr" | "asr" => {
            lower_alu(mnem, &ops, width(ops[0])).map(fall)
        }
        "cmp" | "cmn" => {
            let a = Operand::Reg(reg_of(&ops, 0)?);
            let b = value_operand(&ops, 1, width(ops[0]))?;
            *flags = Some((a, b));
            Ok(fall(vec![]))
        }
        // adrp/adr Rd, sym — materialise the symbol's address as a pointer.
        "adrp" | "adr" => {
            let d = reg_of(&ops, 0)?;
            let sym = ops.get(1).map(|s| s.trim().to_string()).unwrap_or_default();
            Ok(fall(vec![Inst::Assign {
                dst: d,
                ty: Type::ptr(Type::Unit),
                value: RValue::Use(Operand::Const(Const::Symbol(strip_reloc(&sym)))),
            }]))
        }
        "ldr" | "ldrb" | "ldrh" | "ldrsw" | "ldrsb" | "ldrsh" | "str" | "strb" | "strh" => {
            lower_load_store(mnem, &ops, off).map(fall)
        }
        "ldp" | "stp" => lower_pair(mnem, &ops, off).map(fall),
        _ => Err(Error::unsupported(format!("arm64: mnemonic `{mnem}`"))),
    }
}

/// A register operand → its encoding number (`x`/`w` prefix; `sp`=31; the zero
/// register is not a location and is rejected here — callers that accept it use
/// [`value_operand`]).
fn reg_of(ops: &[&str], i: usize) -> Result<RegId> {
    reg_number(ops.get(i).copied().unwrap_or(""))
        .map(reg)
        .ok_or_else(|| Error::unsupported(format!("arm64: expected a register at operand {i}")))
}

/// The **value** of operand `i`: a register, `#imm`, or the zero register as 0.
fn value_operand(ops: &[&str], i: usize, width: u32) -> Result<Operand> {
    let tok = ops.get(i).copied().unwrap_or("").trim();
    if tok == "xzr" || tok == "wzr" {
        return Ok(Operand::int(width, 0));
    }
    if let Some(imm) = parse_imm(tok) {
        return Ok(Operand::int(width, imm as u128));
    }
    reg_number(tok)
        .map(|n| Operand::Reg(reg(n)))
        .ok_or_else(|| Error::unsupported(format!("arm64: operand `{tok}`")))
}

fn lower_addsub(mnem: &str, ops: &[&str]) -> Result<Vec<Inst>> {
    let rd = reg_number(ops.first().copied().unwrap_or(""))
        .ok_or_else(|| Error::unsupported("arm64: add/sub dst"))?;
    let rn = reg_number(ops.get(1).copied().unwrap_or(""))
        .ok_or_else(|| Error::unsupported("arm64: add/sub src"))?;
    let width = if ops[0].trim_start().starts_with('w') {
        32
    } else {
        64
    };
    // `sub sp, sp, #N` allocates the frame; `add sp, sp, #N` tears it down.
    if rd == SP && rn == SP {
        if let Some(n) = ops.get(2).and_then(|o| parse_imm(o)) {
            return Ok(if mnem == "sub" {
                vec![Inst::Alloc {
                    dst: reg(SP),
                    region: RegionKind::Stack,
                    elem: Type::int(8),
                    count: Operand::int(64, n as u128),
                    align: 16,
                }]
            } else {
                vec![]
            });
        }
    }
    // `add Rd, Rn, :lo12:sym` completes an adrp — keep Rn's symbol pointer.
    if let Some(third) = ops.get(2) {
        if third.trim().starts_with(":lo12:") || third.trim().starts_with(":got_lo12:") {
            return Ok(vec![Inst::Assign {
                dst: reg(rd),
                ty: Type::ptr(Type::Unit),
                value: RValue::Use(Operand::Reg(reg(rn))),
            }]);
        }
    }
    let rhs = value_operand(ops, 2, width)?;
    let op = if mnem == "sub" {
        BinOp::Sub
    } else {
        BinOp::Add
    };
    Ok(vec![Inst::Assign {
        dst: reg(rd),
        ty: Type::int(width),
        value: RValue::Bin {
            op,
            lhs: Operand::Reg(reg(rn)),
            rhs,
            flags: Default::default(),
        },
    }])
}

fn lower_alu(mnem: &str, ops: &[&str], width: u32) -> Result<Vec<Inst>> {
    let rd = reg_of(ops, 0)?;
    let rn = Operand::Reg(reg_of(ops, 1)?);
    let rhs = value_operand(ops, 2, width)?;
    let op = match mnem {
        "and" => BinOp::And,
        "orr" => BinOp::Or,
        "eor" => BinOp::Xor,
        "lsl" => BinOp::Shl,
        "lsr" => BinOp::LShr,
        "asr" => BinOp::AShr,
        _ => unreachable!(),
    };
    Ok(vec![Inst::Assign {
        dst: rd,
        ty: Type::int(width),
        value: RValue::Bin {
            op,
            lhs: rn,
            rhs,
            flags: Default::default(),
        },
    }])
}

/// Lower a single load or store; the memory operand is the bracketed tail.
fn lower_load_store(mnem: &str, ops: &[&str], off: usize) -> Result<Vec<Inst>> {
    let rt = ops.first().copied().unwrap_or("");
    let (mut insts, ptr) = parse_mem(ops, 1, off)?;
    let width = access_width(mnem);
    let ty = Type::int(width);
    if mnem.starts_with("str") || mnem == "st" {
        let value = if rt.trim() == "xzr" || rt.trim() == "wzr" {
            Operand::int(width, 0)
        } else {
            Operand::Reg(reg(
                reg_number(rt).ok_or_else(|| Error::unsupported("arm64: str value reg"))?
            ))
        };
        insts.push(Inst::Store {
            ty,
            ptr: Operand::Reg(ptr),
            value,
            align: 1,
            volatile: false,
        });
    } else {
        let dst = match reg_number(rt) {
            Some(n) => reg(n),
            None => temp_reg(off + 900), // load into the zero register = discard
        };
        insts.push(Inst::Load {
            dst,
            ty,
            ptr: Operand::Reg(ptr),
            align: 1,
            volatile: false,
        });
    }
    Ok(insts)
}

/// Lower `ldp`/`stp Rt1, Rt2, [base, #off]` as two accesses at `#off` and
/// `#off + 8` (the standard prologue save/restore of a register pair).
fn lower_pair(mnem: &str, ops: &[&str], off: usize) -> Result<Vec<Inst>> {
    // The memory operand starts at operand index 2 (after the two registers).
    let (mut insts, base_ptr) = parse_mem(ops, 2, off)?;
    let emit = |slot: usize, rt: &str, insts: &mut Vec<Inst>| -> Result<()> {
        let ptr = if slot == 0 {
            base_ptr
        } else {
            let p = temp_reg(off + 800 + slot);
            insts.push(Inst::PtrOffset {
                dst: p,
                base: Operand::Reg(base_ptr),
                index: Operand::int(64, 8 * slot as u128),
                elem: Type::int(8),
            });
            p
        };
        if mnem == "stp" {
            let value = if rt.trim() == "xzr" || rt.trim() == "wzr" {
                Operand::int(64, 0)
            } else {
                Operand::Reg(reg(
                    reg_number(rt).ok_or_else(|| Error::unsupported("arm64: stp value reg"))?
                ))
            };
            insts.push(Inst::Store {
                ty: Type::int(64),
                ptr: Operand::Reg(ptr),
                value,
                align: 1,
                volatile: false,
            });
        } else {
            let dst = match reg_number(rt) {
                Some(n) => reg(n),
                None => temp_reg(off + 700 + slot),
            };
            insts.push(Inst::Load {
                dst,
                ty: Type::int(64),
                ptr: Operand::Reg(ptr),
                align: 1,
                volatile: false,
            });
        }
        Ok(())
    };
    emit(0, ops.first().copied().unwrap_or(""), &mut insts)?;
    emit(1, ops.get(1).copied().unwrap_or(""), &mut insts)?;
    Ok(insts)
}

/// The access width in bits from a load/store mnemonic suffix.
fn access_width(mnem: &str) -> u32 {
    if mnem.ends_with('b') {
        8
    } else if mnem.ends_with('h') {
        16
    } else if mnem == "ldrsw" || mnem.starts_with('w') {
        32
    } else {
        64
    }
}

/// Parse an AArch64 memory operand starting at `ops[i]` — `[base]`, `[base,
/// #imm]`, or `[base, Xindex, lsl #s]` (possibly split across tokens by the
/// operand comma-split) — emitting the `PtrOffset` chain and returning the
/// address register.
fn parse_mem(ops: &[&str], i: usize, off: usize) -> Result<(Vec<Inst>, RegId)> {
    // Rejoin the operands from index `i` (the split broke `[base, #off]` on the comma).
    let joined = ops[i.min(ops.len())..].join(", ");
    let inner = joined
        .trim()
        .strip_prefix('[')
        .and_then(|s| s.trim_end_matches(['!']).trim().strip_suffix(']'))
        .ok_or_else(|| Error::unsupported(format!("arm64: memory operand `{joined}`")))?;
    let parts: Vec<&str> = inner.split(',').map(str::trim).collect();
    let base = reg_number(parts.first().copied().unwrap_or(""))
        .ok_or_else(|| Error::unsupported("arm64: mem base"))?;
    let mut insts = Vec::new();
    let mut ptr = reg(base);
    match parts.get(1) {
        // `[base, #imm]`
        Some(t) if t.starts_with('#') => {
            let disp = parse_imm(t).unwrap_or(0);
            let dst = temp_reg(off);
            insts.push(Inst::PtrOffset {
                dst,
                base: Operand::Reg(ptr),
                index: Operand::int(64, disp as u128),
                elem: Type::int(8),
            });
            ptr = dst;
        }
        // `[base, Xindex {, lsl #s}]`
        Some(t) => {
            let index = reg_number(t)
                .ok_or_else(|| Error::unsupported(format!("arm64: mem index `{t}`")))?;
            let scale = parts.get(2).and_then(parse_lsl_scale).unwrap_or(1);
            let dst = temp_reg(off);
            insts.push(Inst::PtrOffset {
                dst,
                base: Operand::Reg(ptr),
                index: Operand::Reg(reg(index)),
                elem: Type::int(8 * scale),
            });
            ptr = dst;
        }
        // `[base]`
        None => {
            let dst = temp_reg(off);
            insts.push(Inst::PtrOffset {
                dst,
                base: Operand::Reg(ptr),
                index: Operand::int(64, 0),
                elem: Type::int(8),
            });
            ptr = dst;
        }
    }
    Ok((insts, ptr))
}

/// The byte scale from a `lsl #s` shift term (`lsl #3` → 8 bytes).
fn parse_lsl_scale(t: &&str) -> Option<u32> {
    let s = t.trim().strip_prefix("lsl")?.trim().strip_prefix('#')?;
    let bits: u32 = s.trim().parse().ok()?;
    Some(1u32 << bits)
}

/// Lower a `bl sym` / `blr Xn` call to an opaque `Inst::Call` binding x0 (the
/// PCS integer result register): a direct symbol, or an indirect register target.
fn lower_call(ops: &[&str]) -> Inst {
    let t = ops.first().map(|s| s.trim()).unwrap_or("");
    let callee = match reg_number(t) {
        Some(n) => Callee::Indirect(Operand::Reg(reg(n))),
        None if !t.is_empty() => Callee::Symbol(t.to_string()),
        None => Callee::Symbol("<indirect>".to_string()),
    };
    Inst::Call {
        dst: Some(reg(0)),
        callee,
        args: Vec::new(),
        ret_ty: Type::int(64),
        ret_ref: None,
    }
}

fn branch(
    off: usize,
    next: usize,
    target: usize,
    cc: CmpOp,
    flags: Option<(Operand, Operand)>,
) -> Result<DecodedInsn> {
    match flags {
        Some((a, b)) => branch_cmp(off, next, target, cc, a, b),
        None => branch_cmp(
            off,
            next,
            target,
            CmpOp::Ne,
            Operand::Reg(RegId(2000 + off as u32)),
            Operand::int(64, 0),
        ),
    }
}

fn branch_cmp(
    off: usize,
    next: usize,
    target: usize,
    op: CmpOp,
    lhs: Operand,
    rhs: Operand,
) -> Result<DecodedInsn> {
    let cond = temp_reg(off);
    Ok(DecodedInsn {
        offset: off,
        next,
        insts: vec![Inst::Assign {
            dst: cond,
            ty: Type::Bool,
            value: RValue::Cmp { op, lhs, rhs },
        }],
        ctrl: Ctrl::Jcc(target, cond),
    })
}

fn label(
    ops: &[&str],
    i: usize,
    labels: &std::collections::HashMap<String, usize>,
) -> Result<usize> {
    let t = ops.get(i).copied().unwrap_or("").trim();
    labels
        .get(t)
        .copied()
        .ok_or_else(|| Error::unsupported(format!("arm64: branch to unknown label `{t}`")))
}

/// `x0`/`w0`→0 … `x30`→30, `sp`/`xzr`/`wzr`→31, `fp`→29, `lr`→30. `None` if not
/// a GP register name.
fn reg_number(name: &str) -> Option<u8> {
    let name = name.trim();
    match name {
        "sp" | "xzr" | "wzr" => return Some(31),
        "fp" => return Some(29),
        "lr" => return Some(30),
        _ => {}
    }
    let digits = name.strip_prefix('x').or_else(|| name.strip_prefix('w'))?;
    let n: u8 = digits.parse().ok()?;
    if n <= 30 {
        Some(n)
    } else {
        None
    }
}

/// An AArch64 condition-name (`eq`/`ne`/`lt`/…) → the comparison it tests
/// (`cmp a, b` then `b.<cc>` branches iff `a <op> b`).
fn cc_name(cc: &str) -> Option<CmpOp> {
    Some(match cc {
        "eq" => CmpOp::Eq,
        "ne" => CmpOp::Ne,
        "cs" | "hs" => CmpOp::Uge,
        "cc" | "lo" => CmpOp::Ult,
        "hi" => CmpOp::Ugt,
        "ls" => CmpOp::Ule,
        "ge" => CmpOp::Sge,
        "lt" => CmpOp::Slt,
        "gt" => CmpOp::Sgt,
        "le" => CmpOp::Sle,
        _ => return None,
    })
}

/// Parse an AArch64 `#imm` (or bare) decimal/`0x`-hex immediate.
fn parse_imm(tok: &str) -> Option<i64> {
    let s = tok.trim();
    let s = s.strip_prefix('#').unwrap_or(s).trim();
    let (neg, s) = match s.strip_prefix('-') {
        Some(r) => (true, r.trim()),
        None => (false, s),
    };
    let v = if let Some(h) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        i64::from_str_radix(h, 16).ok()?
    } else {
        s.parse::<i64>().ok()?
    };
    Some(if neg { -v } else { v })
}

/// Strip a `:lo12:` / `:got:` relocation qualifier from a symbol reference.
fn strip_reloc(sym: &str) -> String {
    let s = sym.trim();
    match s.rsplit_once(':') {
        Some((_, name)) if s.starts_with(':') => name.to_string(),
        _ => s.to_string(),
    }
}

/// Split an operand list on top-level commas (commas inside `[...]` are kept).
fn split_operands(rest: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let (mut start, mut depth) = (0usize, 0i32);
    for (i, c) in rest.char_indices() {
        match c {
            '[' => depth += 1,
            ']' => depth -= 1,
            ',' if depth == 0 => {
                out.push(rest[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }
    let last = rest[start..].trim();
    if !last.is_empty() || !out.is_empty() {
        out.push(last);
    }
    out
}

/// Drop an assembly comment (`;` or `//` to end of line).
fn strip_comment(line: &str) -> &str {
    match line.find(';').into_iter().chain(line.find("//")).min() {
        Some(i) => &line[..i],
        None => line,
    }
}

fn is_symbol(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '.' || c == '$' || c == '@')
}

#[cfg(test)]
#[path = "arm64_text_tests.rs"]
mod tests;
