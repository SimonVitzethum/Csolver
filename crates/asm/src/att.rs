//! Textual **AT&T-syntax** x86-64 assembly (`.s`) → MSIR.
//!
//! A focused frontend for compiler-emitted (`clang/gcc -S`) and hand-written AT&T
//! assembly. It reuses the architecture-independent CFG assembly ([`build_blocks`])
//! and the x86 register/condition helpers, so only the *text* operand grammar and a
//! common instruction subset live here. An unrecognised mnemonic or operand fails
//! the enclosing function to `unanalyzed` (sound: never a guess), exactly like the
//! byte decoder.
//!
//! Supported: `mov`, `lea`, `add/sub/and/or/xor`, `cmp/test`, `inc/dec`, `cmov`,
//! `jmp`, `jcc`, `ret`, `nop`, `endbr64`. Operands: `%reg`, `$imm`,
//! `disp(%base,%index,scale)`. `push/pop`/anything else → the function drops.

use crate::blocks::{build_blocks, Ctrl, DecodedInsn};
use crate::x86::{cc_cmpop, reg, temp_reg};
use csolver_core::{Error, RegionKind, Result};
use csolver_ir::{BinOp, Const, FuncId, Function, Inst, Module, Operand, RValue, RegId, Type};

/// Decode a whole AT&T `.s` translation unit into a module (one function per
/// `NAME:` label that carries instructions; local `.L…` labels are jump targets).
pub fn decode_att(source: &str) -> Module {
    let mut m = Module::new("asm");
    for (name, body) in split_functions(source) {
        match decode_function_lines(&body) {
            Ok(f) => m.functions.push(Function { id: FuncId(m.functions.len() as u32), name, ..f }),
            Err(e) => m.unanalyzed.push((name, e.to_string())),
        }
    }
    m
}

/// Split the source into `(function name, its instruction/label lines)`. A function
/// starts at a **non-local** label (`foo:`, not `.L…:`) and runs until the next such
/// label, a `.size`, or `.cfi_endproc`.
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
                // A new function label.
                if let Some(f) = cur.take() {
                    out.push(f);
                }
                cur = Some((label.to_string(), Vec::new()));
                continue;
            }
            // A local label — a jump target inside the current function.
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
            continue; // any other directive (.text/.globl/.type/.p2align/.cfi_*/…)
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
fn decode_function_lines(lines: &[String]) -> Result<Function> {
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
    // Pass 2: lower each instruction. `flags` carries the last cmp/test operands.
    let mut decoded: Vec<DecodedInsn> = Vec::new();
    let mut flags: Option<(Operand, Operand)> = None;
    for (i, ins) in insns.iter().enumerate() {
        let d = lower_insn(ins, i, insns.len(), &labels, &mut flags)?;
        decoded.push(d);
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

/// Lower one AT&T instruction at sequential offset `off` (of `total`).
fn lower_insn(
    ins: &str,
    off: usize,
    total: usize,
    labels: &std::collections::HashMap<String, usize>,
    flags: &mut Option<(Operand, Operand)>,
) -> Result<DecodedInsn> {
    let next = off + 1;
    let fall = |insts: Vec<Inst>| DecodedInsn { offset: off, next, insts, ctrl: Ctrl::Fall };
    let (mnem, rest) = match ins.split_once(char::is_whitespace) {
        Some((m, r)) => (m, r.trim()),
        None => (ins, ""),
    };
    let ops = split_operands(rest);
    // Strip the AT&T size suffix (b/w/l/q) to get the base mnemonic; keep the width.
    let (base, width) = strip_suffix(mnem);

    match base {
        "ret" | "retq" => Ok(DecodedInsn { offset: off, next, insts: vec![], ctrl: Ctrl::Ret }),
        "nop" | "nopl" | "nopw" | "endbr64" | "endbr32" | "hlt" | "ud2" => Ok(fall(vec![])),
        "jmp" => {
            let t = label_target(&ops, 0, labels)?;
            Ok(DecodedInsn { offset: off, next, insts: vec![], ctrl: Ctrl::Jmp(t) })
        }
        // jcc: the base after stripping is `j<cc>`; the condition is the cc mnemonic.
        _ if base.starts_with('j') && base.len() >= 2 => {
            let cc = jcc_code(&base[1..]).ok_or_else(|| Error::unsupported(format!("asm: jcc `{base}`")))?;
            let t = label_target(&ops, 0, labels)?;
            let cond = temp_reg(off);
            let (op, lhs, rhs) = match (cc_cmpop(cc), flags.clone()) {
                (Some(op), Some((a, b))) => (op, a, b),
                _ => (csolver_ir::CmpOp::Ne, Operand::Reg(RegId(2000 + off as u32)), Operand::int(64, 0)),
            };
            Ok(DecodedInsn {
                offset: off,
                next,
                insts: vec![Inst::Assign { dst: cond, ty: Type::Bool, value: RValue::Cmp { op, lhs, rhs } }],
                ctrl: Ctrl::Jcc(t, cond),
            })
        }
        // cmp/test set the flags for a following jcc (src, dst order; the comparison
        // is dst <op> src, matched by cc_cmpop's convention).
        "cmp" | "test" => {
            let a = operand_value(&ops, 1, off, width)?; // dst
            let b = operand_value(&ops, 0, off, width)?; // src
            *flags = Some((a.value, b.value));
            let mut insts = a.pre;
            insts.extend(b.pre);
            Ok(fall(insts))
        }
        "mov" | "movl" | "movq" | "movabs" | "movabsq" => lower_mov(&ops, off, width).map(fall_wrap(off, next)),
        "movslq" | "movsbl" | "movzbl" | "movzwl" | "movswl" | "movsbq" | "movzbq" => {
            // Sign/zero-extending move: model as a plain move (the value flows through).
            lower_mov(&ops, off, width).map(fall_wrap(off, next))
        }
        "lea" => lower_lea(&ops, off).map(fall_wrap(off, next)),
        "add" | "sub" | "and" | "or" | "xor" => {
            // Stack-frame prologue/epilogue (rsp = register 4): `sub $N, %rsp` allocates
            // the frame — rsp becomes a fresh N-byte stack region so `[rsp+disp]` is
            // checked against it; `add $N, %rsp` tears it down (a no-op). Mirrors the
            // byte decoder, so the `.s` path proves stack accesses too.
            if matches!(base, "add" | "sub") && parse_reg(ops.get(1).copied().unwrap_or("")) == Some(4) {
                if let Some(n) = ops.first().and_then(|o| parse_imm(o)) {
                    return Ok(if base == "sub" {
                        fall(vec![Inst::Alloc {
                            dst: reg(4),
                            region: RegionKind::Stack,
                            elem: Type::int(8),
                            count: Operand::int(64, n as u128),
                            align: 16,
                        }])
                    } else {
                        fall(vec![])
                    });
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
            lower_alu(bin, &ops, off, width).map(fall_wrap(off, next))
        }
        "inc" | "dec" => {
            let d = reg_operand(&ops, 0)?;
            let bin = if base == "inc" { BinOp::Add } else { BinOp::Sub };
            Ok(fall(vec![Inst::Assign {
                dst: d,
                ty: Type::int(width),
                value: RValue::Bin { op: bin, lhs: Operand::Reg(d), rhs: Operand::int(width, 1) , flags: Default::default() },
            }]))
        }
        _ if base.starts_with("cmov") => {
            // Conditional move: destination becomes unknown (flags not modelled precisely).
            let d = reg_operand(&ops, 1)?;
            Ok(fall(vec![Inst::Assign { dst: d, ty: Type::int(width), value: RValue::Use(Operand::Const(Const::Undef)) }]))
        }
        _ => {
            let _ = total;
            Err(Error::unsupported(format!("asm: mnemonic `{mnem}`")))
        }
    }
}

/// A parsed operand: the MSIR value it denotes plus any address-computing insts.
struct OpVal {
    value: Operand,
    pre: Vec<Inst>,
}

fn fall_wrap(off: usize, next: usize) -> impl Fn(Vec<Inst>) -> DecodedInsn {
    move |insts| DecodedInsn { offset: off, next, insts, ctrl: Ctrl::Fall }
}

fn lower_mov(ops: &[&str], off: usize, width: u32) -> Result<Vec<Inst>> {
    let ty = Type::int(width);
    let dst = ops.get(1).copied().unwrap_or("");
    let src = operand_value(ops, 0, off, width)?;
    if let Some(d) = parse_reg(dst) {
        let mut insts = src.pre;
        insts.push(Inst::Assign { dst: reg(d), ty, value: RValue::Use(src.value) });
        Ok(insts)
    } else if let Some(mem) = parse_mem(dst) {
        // store src -> [mem]
        let (mut insts, ptr) = mem.lower(off);
        insts.extend(src.pre);
        insts.push(Inst::Store { ty, ptr: Operand::Reg(ptr), value: src.value, align: 1 , volatile: false});
        Ok(insts)
    } else {
        Err(Error::unsupported(format!("asm: mov destination `{dst}`")))
    }
}

fn lower_lea(ops: &[&str], off: usize) -> Result<Vec<Inst>> {
    let d = reg_operand(ops, 1)?;
    let mem = parse_mem(ops.first().copied().unwrap_or(""))
        .ok_or_else(|| Error::unsupported("asm: lea needs a memory operand"))?;
    let (mut insts, ptr) = mem.lower(off);
    insts.push(Inst::Assign { dst: d, ty: Type::int(64), value: RValue::Use(Operand::Reg(ptr)) });
    Ok(insts)
}

fn lower_alu(bin: BinOp, ops: &[&str], off: usize, width: u32) -> Result<Vec<Inst>> {
    let ty = Type::int(width);
    let d = reg_operand(ops, 1)?;
    // `xor %r, %r` is the zeroing idiom.
    if matches!(bin, BinOp::Xor) {
        if let (Some(a), Some(b)) = (parse_reg(ops.first().copied().unwrap_or("")), parse_reg(ops.get(1).copied().unwrap_or(""))) {
            if a == b {
                return Ok(vec![Inst::Assign { dst: d, ty, value: RValue::Use(Operand::int(width, 0)) }]);
            }
        }
    }
    let src = operand_value(ops, 0, off, width)?;
    let mut insts = src.pre;
    insts.push(Inst::Assign { dst: d, ty, value: RValue::Bin { op: bin, lhs: Operand::Reg(d), rhs: src.value , flags: Default::default() } });
    Ok(insts)
}

/// The value of operand `i`: a register, an immediate, or a load from a memory
/// operand (emitting the load into a temporary).
fn operand_value(ops: &[&str], i: usize, off: usize, width: u32) -> Result<OpVal> {
    let tok = ops.get(i).copied().unwrap_or("");
    if let Some(r) = parse_reg(tok) {
        return Ok(OpVal { value: Operand::Reg(reg(r)), pre: vec![] });
    }
    if let Some(imm) = parse_imm(tok) {
        return Ok(OpVal { value: Operand::int(width, imm as u128), pre: vec![] });
    }
    if let Some(mem) = parse_mem(tok) {
        let (mut pre, ptr) = mem.lower(off);
        let loaded = RegId(3000 + off as u32);
        pre.push(Inst::Load { dst: loaded, ty: Type::int(width), ptr: Operand::Reg(ptr), align: 1 , volatile: false});
        return Ok(OpVal { value: Operand::Reg(loaded), pre });
    }
    Err(Error::unsupported(format!("asm: operand `{tok}`")))
}

fn reg_operand(ops: &[&str], i: usize) -> Result<RegId> {
    parse_reg(ops.get(i).copied().unwrap_or(""))
        .map(reg)
        .ok_or_else(|| Error::unsupported(format!("asm: expected a register operand at {i}")))
}

fn label_target(ops: &[&str], i: usize, labels: &std::collections::HashMap<String, usize>) -> Result<usize> {
    let t = ops.get(i).copied().unwrap_or("").trim();
    labels.get(t).copied().ok_or_else(|| Error::unsupported(format!("asm: branch to unknown label `{t}`")))
}

// --- operand grammar -------------------------------------------------------

/// Split an operand list on top-level commas (commas inside `(...)` are part of a
/// memory operand and must not split).
fn split_operands(rest: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let (mut start, mut depth) = (0usize, 0i32);
    for (i, c) in rest.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
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

/// A parsed AT&T `disp(%base,%index,scale)` memory operand → the crate's byte
/// decoder `MemOperand` shape, reusing its `lower`.
fn parse_mem(tok: &str) -> Option<crate::x86::MemOperand> {
    let tok = tok.trim();
    let open = tok.find('(')?;
    if !tok.ends_with(')') {
        return None;
    }
    let disp_str = tok[..open].trim();
    let inner = &tok[open + 1..tok.len() - 1];
    let parts: Vec<&str> = inner.split(',').map(str::trim).collect();
    // A RIP-relative access `symbol(%rip)`: the base is `%rip` and the displacement is
    // a symbol name → a global symbol base (the executor resolves it to that region).
    if parts.first().copied() == Some("%rip") {
        return Some(crate::x86::MemOperand {
            base: reg(0),
            index: None,
            disp: 0,
            next: 0,
            symbol: Some(disp_str.to_string()),
        });
    }
    let disp: i64 = if open == 0 { 0 } else { parse_disp(disp_str)? };
    let base = parse_reg(parts.first().copied().unwrap_or(""))?;
    let index = match parts.get(1) {
        Some(r) if !r.is_empty() => {
            let ir = parse_reg(r)?;
            let scale: u8 = parts.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);
            Some((reg(ir), scale))
        }
        _ => None,
    };
    Some(crate::x86::MemOperand { base: reg(base), index, disp, next: 0, symbol: None })
}

fn parse_disp(s: &str) -> Option<i64> {
    let s = s.trim();
    if let Some(h) = s.strip_prefix("0x").or_else(|| s.strip_prefix("-0x").map(|_| &s[3..])) {
        let v = i64::from_str_radix(h, 16).ok()?;
        return Some(if s.starts_with('-') { -v } else { v });
    }
    s.parse().ok()
}

fn parse_imm(tok: &str) -> Option<i64> {
    parse_disp(tok.trim().strip_prefix('$')?)
}

fn parse_reg(tok: &str) -> Option<u8> {
    reg_number(tok.trim().strip_prefix('%')?)
}

/// AT&T register name → x86 register number (sub-registers alias their 64-bit reg).
fn reg_number(name: &str) -> Option<u8> {
    Some(match name {
        "rax" | "eax" | "ax" | "al" => 0,
        "rcx" | "ecx" | "cx" | "cl" => 1,
        "rdx" | "edx" | "dx" | "dl" => 2,
        "rbx" | "ebx" | "bx" | "bl" => 3,
        "rsp" | "esp" | "sp" | "spl" => 4,
        "rbp" | "ebp" | "bp" | "bpl" => 5,
        "rsi" | "esi" | "si" | "sil" => 6,
        "rdi" | "edi" | "di" | "dil" => 7,
        _ => {
            // r8..r15 with an optional d/w/b size suffix.
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

/// Strip the AT&T size suffix (`b`/`w`/`l`/`q`) from a mnemonic that carries one,
/// returning `(base, operand-width-in-bits)`. Only strips when the shortened form
/// is a recognised instruction so `jle`→`jl` etc. are not mangled.
fn strip_suffix(mnem: &str) -> (&str, u32) {
    let known_base = |m: &str| {
        matches!(m, "mov" | "add" | "sub" | "and" | "or" | "xor" | "cmp" | "test" | "inc" | "dec" | "lea")
            || m.starts_with("cmov")
    };
    if let Some(stripped) = mnem.strip_suffix('q') {
        if known_base(stripped) {
            return (stripped, 64);
        }
    }
    if let Some(stripped) = mnem.strip_suffix('l') {
        if known_base(stripped) {
            return (stripped, 32);
        }
    }
    if let Some(stripped) = mnem.strip_suffix('w') {
        if known_base(stripped) {
            return (stripped, 16);
        }
    }
    if let Some(stripped) = mnem.strip_suffix('b') {
        if known_base(stripped) {
            return (stripped, 8);
        }
    }
    (mnem, 64)
}

/// The x86 condition code for an AT&T `j<cc>` / `cmov<cc>` suffix.
fn jcc_code(cc: &str) -> Option<u8> {
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

fn strip_comment(line: &str) -> &str {
    match line.find(['#', ';']) {
        Some(i) => &line[..i],
        None => line,
    }
}

fn is_symbol(s: &str) -> bool {
    !s.is_empty() && s.chars().all(|c| c.is_alphanumeric() || c == '_' || c == '.' || c == '$' || c == '@')
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes_a_leaf_function() {
        // max: movl %esi,%eax; cmpl %esi,%edi; cmovgl %edi,%eax; retq
        let src = "\
\t.text
\t.globl max
\t.type max,@function
max:
\tmovl\t%esi, %eax
\tcmpl\t%esi, %edi
\tcmovgl\t%edi, %eax
\tretq
\t.size max, .-max
";
        let m = decode_att(src);
        assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
        assert_eq!(m.functions.len(), 1);
        assert_eq!(m.functions[0].name, "max");
    }

    #[test]
    fn decodes_a_loop_with_memory_and_branches() {
        let src = "\
sum:
\txorl\t%eax, %eax
\ttestq\t%rsi, %rsi
\tjle\t.LBB1_3
\txorl\t%ecx, %ecx
.LBB1_2:
\taddq\t(%rdi,%rcx,8), %rax
\tincq\t%rcx
\tcmpq\t%rcx, %rsi
\tjne\t.LBB1_2
.LBB1_3:
\tretq
";
        let m = decode_att(src);
        assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
        let f = &m.functions[0];
        assert!(f.blocks.len() >= 3, "loop CFG has multiple blocks");
        // The `addq (%rdi,%rcx,8), %rax` emits a load.
        assert!(f.blocks.iter().flat_map(|b| &b.insts).any(|i| matches!(i, Inst::Load { .. })));
    }

    #[test]
    fn sub_rsp_allocates_a_stack_frame() {
        // subq $16,%rsp allocates the frame; the store/load to (%rsp) are then checked
        // against it. Assert an Alloc{Stack} is emitted and the frame teardown is a no-op.
        let src = "\
f:
\tsubq\t$16, %rsp
\tmovl\t$1, (%rsp)
\tmovl\t(%rsp), %eax
\taddq\t$16, %rsp
\tretq
";
        let m = decode_att(src);
        assert!(m.unanalyzed.is_empty(), "must decode: {:?}", m.unanalyzed);
        let has_frame = m.functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.insts)
            .any(|i| matches!(i, Inst::Alloc { region: RegionKind::Stack, .. }));
        assert!(has_frame, "`sub $N,%rsp` must allocate a stack frame");
    }

    #[test]
    fn unknown_mnemonic_drops_the_function() {
        let src = "f:\n\tpushq\t%rbp\n\tretq\n";
        let m = decode_att(src);
        assert!(m.functions.is_empty());
        assert_eq!(m.unanalyzed.len(), 1);
    }

    #[test]
    fn reg_names_alias_sub_registers() {
        assert_eq!(reg_number("rax"), Some(0));
        assert_eq!(reg_number("eax"), Some(0));
        assert_eq!(reg_number("dil"), Some(7));
        assert_eq!(reg_number("r10d"), Some(10));
        assert_eq!(reg_number("r15"), Some(15));
        assert_eq!(reg_number("xmm0"), None);
    }
}
