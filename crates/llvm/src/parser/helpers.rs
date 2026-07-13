use super::*;

pub(crate) enum InstOrPhi {
    Phi(LPhi),
    Inst(LInst),
}

pub(crate) fn is_int_type(w: &str) -> bool {
    w.starts_with('i') && w.len() > 1 && w[1..].bytes().all(|b| b.is_ascii_digit())
}

/// Whether an inline-asm constraint string means the asm may **write memory** we
/// track — a `"memory"` clobber, or an OUTPUT operand that references memory
/// (`=m`/`+m`/`=*m`/`=&m`/`=*A`…). A register/immediate output, or a read-only
/// memory *input* (`m` with no `=`/`+`), touches no tracked memory. Conservative
/// by direction: any doubt about an output resolves to "may write" (a false havoc,
/// never a missed write), so an unrecognised shape can only lose precision.
/// The **memory operands** of an inline-asm constraint string: `(arg_index, is_write)` for each
/// operand that is a pointer the asm accesses (`=*m`/`+*m`/`*m`/`=m`/`m`). LLVM passes indirect
/// memory operands and inputs as call arguments in constraint order; a plain register output
/// (`=r`, no `*`/`m`) consumes no argument (it maps to the return). Best-effort: used only to
/// *add* precise access obligations on the pointer, so a mis-count can never cause a false PASS.
pub(crate) fn asm_memory_operands(constraints: &str) -> Vec<(usize, bool)> {
    let mut ops = Vec::new();
    let mut arg = 0usize;
    for tok in constraints.split(',') {
        let t = tok.trim();
        if t.is_empty() || t.starts_with('~') {
            continue; // a clobber (`~{memory}`, `~{cc}`, `~{reg}`) consumes no argument
        }
        let is_output = t.starts_with('=') || t.starts_with('+');
        let is_reg_output = is_output && !t.contains('*') && !t.contains('m');
        if is_reg_output {
            continue; // register output → the return value, not an argument
        }
        // This operand consumes an argument (an input, or an indirect/memory operand).
        let is_mem = t.contains('m') || t.contains('*');
        if is_mem {
            ops.push((arg, is_output));
        }
        arg += 1;
    }
    ops
}

/// The operand-index → source map of an inline-asm constraint string, in template-reference order
/// (`$0`, `$1`, …), mirroring LLVM's argument packing so `$k` resolves to the right SSA value:
/// - a **read-only register output** (`=r`/`=&r`, no memory) → the call's return, no argument
///   (`OperandSrc::Ret`);
/// - a **read-write register output** (`+r`) → the return, but its incoming value is the next
///   argument (`OperandSrc::RetTied(j)`) — an in-place op reads it and writes the return;
/// - everything else (a memory output, or an input) consumes an argument (`OperandSrc::Arg(j)`).
///
/// Clobbers (`~{…}`) consume nothing.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum OperandSrc {
    Ret,
    RetTied(usize),
    Arg(usize),
}
impl OperandSrc {
    /// The argument index this operand *reads its value from*, if any (`Ret` — a write-only
    /// output — has no readable value of its own).
    pub(crate) fn value_arg(self) -> Option<usize> {
        match self {
            OperandSrc::Arg(j) | OperandSrc::RetTied(j) => Some(j),
            OperandSrc::Ret => None,
        }
    }
    /// Whether this operand is an output (a destination the instruction writes).
    pub(crate) fn is_output(self) -> bool {
        matches!(self, OperandSrc::Ret | OperandSrc::RetTied(_))
    }
}

/// The operand layout of an inline-asm constraint string: each operand's source (`sources`), and,
/// per **output** operand index, the argument that supplies its *incoming* value (`tied_in`) — from
/// a `+r` (self-tied) or a numeric matching-constraint input (`"0"` ties an input to output 0). The
/// canonical clang form `"=r,0,r"` and the pre-canonical `"+r,r"` both resolve here.
pub(crate) struct AsmLayout {
    sources: Vec<OperandSrc>,
    tied_in: std::collections::HashMap<usize, usize>,
}
impl AsmLayout {
    pub(crate) fn source(&self, operand: usize) -> Option<OperandSrc> {
        self.sources.get(operand).copied()
    }
    /// The argument supplying an output operand's incoming value (for an in-place op).
    pub(crate) fn incoming_arg(&self, operand: usize) -> Option<usize> {
        match self.sources.get(operand)? {
            OperandSrc::RetTied(j) => Some(*j),
            _ => self.tied_in.get(&operand).copied(),
        }
    }
}

pub(crate) fn asm_operand_layout(constraints: &str) -> AsmLayout {
    let mut sources = Vec::new();
    let mut tied_in = std::collections::HashMap::new();
    let mut arg = 0usize;
    for tok in constraints.split(',') {
        let t = tok.trim();
        if t.is_empty() || t.starts_with('~') {
            continue;
        }
        let is_reg_output = t.starts_with('=') && !t.contains('*') && !t.contains('m');
        let is_rw_reg_output = t.starts_with('+') && !t.contains('*') && !t.contains('m');
        // A matching-constraint input: a bare number `n` — an input tied to output operand `n`,
        // supplying that output's incoming value (clang's canonical form of `+r`).
        let matches_output: Option<usize> = t.parse().ok();
        if is_reg_output {
            sources.push(OperandSrc::Ret);
        } else if is_rw_reg_output {
            let this = sources.len();
            sources.push(OperandSrc::RetTied(arg));
            tied_in.insert(this, arg);
            arg += 1;
        } else {
            if let Some(n) = matches_output {
                tied_in.insert(n, arg);
            }
            sources.push(OperandSrc::Arg(arg));
            arg += 1;
        }
    }
    AsmLayout { sources, tied_in }
}

/// Extract the operand index from a template token that references one: `$0`, `${1:w}`, … → the
/// number. A hardcoded register (`%rax`), a `$$`-escaped literal dollar, or anything else → `None`.
pub(crate) fn asm_operand_index(tok: &str) -> Option<usize> {
    let rest = tok.trim().strip_prefix('$')?;
    // `$$` is an escaped literal dollar (an AT&T immediate), not an operand reference.
    let digits: String = rest.trim_start_matches('{').chars().take_while(|c| c.is_ascii_digit()).collect();
    if digits.is_empty() {
        return None;
    }
    digits.parse().ok()
}

/// Strip an AT&T size suffix (`l`/`q`/`w`/`b`) from a mnemonic root, e.g. `addl` → `add`. Returns
/// the bare root; a mnemonic that is not `root{,l,q,w,b}` is returned unchanged.
pub(crate) fn asm_mnem_root<'a>(m: &'a str, root: &str) -> Option<&'a str> {
    if m == root {
        return Some(m);
    }
    m.strip_suffix(['l', 'q', 'w', 'b']).filter(|base| *base == root).map(|_| m)
}

/// The binop encoding letter for an arithmetic/bitwise AT&T/Intel mnemonic, and whether it is
/// order-sensitive (non-commutative). Returns `(letter, non_commutative)`.
pub(crate) fn asm_binop_code(m: &str) -> Option<(char, bool)> {
    let is = |r: &str| asm_mnem_root(m, r).is_some();
    if is("add") { Some(('a', false)) }
    else if is("sub") { Some(('s', true)) }
    else if is("and") { Some(('n', false)) }
    else if is("or") { Some(('o', false)) }
    else if is("xor") { Some(('x', false)) }
    else if is("shl") || is("sal") { Some(('l', true)) }
    else if is("shr") { Some(('r', true)) }
    else if is("sar") { Some(('h', true)) }
    else if is("imul") || is("mul") { Some(('m', false)) }
    else { None }
}

/// Recognize a **register-dataflow semantic** for a single-instruction inline-asm template whose
/// output register is a *provable* function of its operands, and encode it as a `|sem…` suffix the
/// lowering consumes. The output is bound to that value instead of an opaque havoc. Recognized —
/// each always-correct, so modeling can never introduce a wrong result (soundness preserved):
/// - `|semZ`   — a `xor r,r` / `sub r,r` self-zero → `0`.
/// - `|semC<j>` — a plain `mov` copy, or a bare-base `lea (r), d` → a copy of argument `j`.
/// - `|semB<op>:<ja>:<jb>` — an in-place binary op (`add`/`sub`/`and`/`or`/`xor`/`shl`/`shr`/
///   `sar`/`imul`) on a `+r` destination → `args[ja] OP args[jb]`.
/// - `|semNn:<j>` / `|semNt:<j>` — an in-place `neg` / `not` → `0 - args[j]` / `~args[j]`.
///
/// Handles both AT&T (`src, dst`) and Intel (`dst, src`) dialects. A width-extending move
/// (`movz*`/`movs*`), a multi-instruction template, a memory/immediate operand, or any operand that
/// does not resolve to a concrete argument returns `None` and stays opaquely havoc'd.
pub(crate) fn asm_reg_semantic(template: &str, constraints: &str, intel: bool) -> Option<String> {
    // Split a multi-line/multi-statement template into statements (newline, its `\0A` escape, or
    // `;`), dropping blank lines, `nop`s and directive lines (`.p2align`, …). A template that
    // reduces to exactly ONE real instruction is decoded (leading/trailing whitespace or a stray
    // `nop` is harmless); two or more real instructions cannot be tracked without a register file,
    // so they stay opaquely havoc'd (sound).
    let normalized = template.replace("\\0A", "\n").replace(';', "\n");
    let mut stmts = normalized.split('\n').map(str::trim).filter(|s| {
        !s.is_empty() && *s != "nop" && !s.starts_with('.') && !s.starts_with('#')
    });
    let t = stmts.next()?;
    if stmts.next().is_some() {
        return None; // more than one real instruction
    }
    let t = t.replace('\t', " ");
    let (mnem, rest) = t.split_once(' ')?;
    let ops: Vec<&str> = rest.split(',').map(str::trim).filter(|s| !s.is_empty()).collect();
    let layout = asm_operand_layout(constraints);
    let m = mnem.trim();
    // The operand index a template token refers to, and its source role.
    let resolve = |tok: &str| -> Option<OperandSrc> { layout.source(asm_operand_index(tok)?) };

    // --- Unary in-place (`neg`/`not`) on a read-write destination --------------------------
    if ops.len() == 1 {
        let code = if asm_mnem_root(m, "neg").is_some() {
            'n'
        } else if asm_mnem_root(m, "not").is_some() {
            't'
        } else {
            return None;
        };
        let k = asm_operand_index(ops[0])?;
        // Must be an output with a readable incoming value (`+r` or a matching-tied `=r`).
        if layout.source(k).map(OperandSrc::is_output) == Some(true) {
            if let Some(j) = layout.incoming_arg(k) {
                return Some(format!("|semN{code}:{j}"));
            }
        }
        return None;
    }
    if ops.len() != 2 {
        return None;
    }
    // AT&T: `mnem src, dst` (dst last). Intel: `mnem dst, src` (dst first).
    let (src_tok, dst_tok) = if intel { (ops[1], ops[0]) } else { (ops[0], ops[1]) };

    // --- Zero idiom: `xor $K, $K` / `sub $K, $K` with both operands the same output → 0 ------
    if asm_mnem_root(m, "xor").is_some() || asm_mnem_root(m, "sub").is_some() {
        if let (Some(a), Some(b)) = (asm_operand_index(src_tok), asm_operand_index(dst_tok)) {
            if a == b && resolve(dst_tok).map(OperandSrc::is_output) == Some(true) {
                return Some("|semZ".to_string());
            }
        }
    }

    // --- Plain copy: `mov $S, $D`, output `$D` = return, source `$S` = argument `j` ----------
    let is_copy = matches!(m, "mov" | "movl" | "movq" | "movw" | "movb" | "movabs" | "movabsq");
    if is_copy {
        let (s, d) = (resolve(src_tok)?, resolve(dst_tok)?);
        if d.is_output() {
            if let Some(j) = s.value_arg() {
                return Some(format!("|semC{j}"));
            }
        }
        return None;
    }
    // --- Bare-base `lea (r), d` → a copy (address = the base register, no disp/index) --------
    if asm_mnem_root(m, "lea").is_some() {
        // The source is a memory operand `(tok)`; only a lone base with no displacement/index
        // (no `,`/digits outside the parens) is a pure copy — anything else bails.
        let inner = src_tok.strip_prefix('(').and_then(|s| s.strip_suffix(')'))?;
        if inner.contains(',') {
            return None;
        }
        let (s, d) = (resolve(inner)?, resolve(dst_tok)?);
        if d.is_output() {
            if let Some(j) = s.value_arg() {
                return Some(format!("|semC{j}"));
            }
        }
        return None;
    }

    // --- In-place binary op on a read-write destination: `op $S, $D` → args[jd] OP args[js] --
    if let Some((code, _non_commutative)) = asm_binop_code(m) {
        let kd = asm_operand_index(dst_tok)?;
        // The destination must be an output carrying its incoming value (a `+r`, or a `=r` with a
        // matching-constraint input) — it is read and written; the destination is the left operand
        // (correct for the non-commutative `sub`/`shl`/`shr`/`sar`).
        if layout.source(kd).map(OperandSrc::is_output) != Some(true) {
            return None;
        }
        let jd = layout.incoming_arg(kd)?;
        let js = resolve(src_tok)?.value_arg()?;
        return Some(format!("|semB{code}:{jd}:{js}"));
    }
    None
}

pub(crate) fn asm_may_write_memory(constraints: &str) -> bool {
    // A `~{memory}` clobber, or an indirect operand (`*` — the asm is handed a pointer
    // and may write through it, in any direction), or an OUTPUT memory operand
    // (`=m`/`+m`). Register/immediate operands and a read-only register output do not.
    constraints.contains("memory")
        || constraints.contains('*')
        || constraints
            .split(',')
            .any(|tok| (tok.contains('=') || tok.contains('+')) && tok.contains('m'))
}

/// Round `v` up to a multiple of the power-of-two `align`; `None` on overflow.
pub(crate) fn align_up(v: u64, align: u64) -> Option<u64> {
    debug_assert!(align.is_power_of_two());
    let mask = align - 1;
    v.checked_add(mask).map(|x| x & !mask)
}

/// Byte size of a resolved `LType` under the 64-bit layout (matches the IR's
/// `DataLayout::LP64`, so an initializer offset agrees with the executor's gep).
/// `None` for a type whose size cannot be determined (bails the whole scan).
pub(crate) fn ltype_size(ty: &LType) -> Result<u64> {
    let bad = || Error::unsupported("unsizable init element");
    Ok(match ty {
        LType::Void | LType::Metadata => 0,
        LType::Int(bits) => (*bits as u64).div_ceil(8),
        LType::Ptr => 8,
        LType::Array(e, n) | LType::Vector(e, n) => {
            let stride = align_up(ltype_size(e)?, ltype_align(e)?).ok_or_else(bad)?;
            stride.checked_mul(*n).ok_or_else(bad)?
        }
        LType::Struct(fs) => {
            let mut off = 0u64;
            let mut max_a = 1u64;
            for f in fs {
                let a = ltype_align(f)?;
                max_a = max_a.max(a);
                off = align_up(off, a).ok_or_else(bad)?;
                off = off.checked_add(ltype_size(f)?).ok_or_else(bad)?;
            }
            align_up(off, max_a).ok_or_else(bad)?
        }
        LType::PackedStruct(fs) => {
            let mut off = 0u64;
            for f in fs {
                off = off.checked_add(ltype_size(f)?).ok_or_else(bad)?;
            }
            off
        }
        LType::Named(_) => return Err(bad()),
    })
}

/// Byte alignment of a resolved `LType` under the 64-bit layout.
pub(crate) fn ltype_align(ty: &LType) -> Result<u64> {
    Ok(match ty {
        LType::Void | LType::Metadata => 1,
        LType::Int(bits) => (*bits as u64).div_ceil(8).max(1).next_power_of_two().min(8),
        LType::Ptr => 8,
        LType::Array(e, _) | LType::Vector(e, _) => ltype_align(e)?,
        LType::Struct(fs) => {
            let mut a = 1u64;
            for f in fs {
                a = a.max(ltype_align(f)?);
            }
            a
        }
        LType::PackedStruct(_) => 1,
        LType::Named(_) => return Err(Error::unsupported("unsizable init element")),
    })
}

/// Whether a token can begin a type (used to tell a real operand from trailing
/// `, !dbg …` metadata in comma-separated operand lists).
pub(crate) fn is_type_start(t: &Tok) -> bool {
    match t {
        Tok::Word(w) => is_int_type(w) || float_bits(w).is_some() || w == "ptr" || w == "void",
        // `%"name"` — a named-type reference.
        Tok::Local(_) => true,
        Tok::Punct('[') | Tok::Punct('<') | Tok::Punct('{') => true,
        _ => false,
    }
}

pub(crate) fn int_bits(w: &str) -> Result<u32> {
    w[1..]
        .parse()
        .map_err(|_| Error::parse(format!("bad integer type `{w}`")))
}

/// The byte-accurate bit width of an LLVM floating-point type, or `None` if `w`
/// is not one. Modelled as an opaque integer scalar of this width.
pub(crate) fn float_bits(w: &str) -> Option<u32> {
    Some(match w {
        "half" | "bfloat" => 16,
        "float" => 32,
        "double" => 64,
        "x86_fp80" => 80,
        "fp128" | "ppc_fp128" => 128,
        _ => return None,
    })
}

/// Whether an opcode is a floating-point arithmetic/cast/compare op. These carry
/// no memory-safety content, so they are lowered opaquely (`Undef`).
pub(crate) fn is_float_op(op: &str) -> bool {
    matches!(
        op,
        "fadd"
            | "fsub"
            | "fmul"
            | "fdiv"
            | "frem"
            | "fneg"
            | "fcmp"
            | "fptrunc"
            | "fpext"
            | "fptoui"
            | "fptosi"
            | "uitofp"
            | "sitofp"
    )
}

pub(crate) fn bin_op(op: &str) -> Option<LBin> {
    Some(match op {
        "add" => LBin::Add,
        "sub" => LBin::Sub,
        "mul" => LBin::Mul,
        "udiv" => LBin::UDiv,
        "sdiv" => LBin::SDiv,
        "urem" => LBin::URem,
        "srem" => LBin::SRem,
        "and" => LBin::And,
        "or" => LBin::Or,
        "xor" => LBin::Xor,
        "shl" => LBin::Shl,
        "lshr" => LBin::LShr,
        "ashr" => LBin::AShr,
        _ => return None,
    })
}

pub(crate) fn cast_op(op: &str) -> Option<LCast> {
    Some(match op {
        "trunc" => LCast::Trunc,
        "zext" => LCast::ZExt,
        "sext" => LCast::SExt,
        "ptrtoint" => LCast::PtrToInt,
        "inttoptr" => LCast::IntToPtr,
        "bitcast" => LCast::Bitcast,
        _ => return None,
    })
}
