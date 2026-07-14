//! AT&T-syntax operand grammar: `%reg`, `$imm`, `disp(%base,%index,scale)`,
//! `sym(%rip)`. The size suffix (`b`/`w`/`l`/`q`) rides the mnemonic. Produces a
//! [`TextOp`] list in source order (which *is* AT&T's `src, dst` order) plus the
//! access width — the internal convention the shared lowering expects.

use super::{reg_number, TextOp};
use crate::x86::{reg, MemOperand};
use csolver_core::{Error, Result};

/// Parse `mnem`'s operands (`rest`) into `(base mnemonic, width bits, operands)`.
pub(super) fn parse(mnem: &str, rest: &str) -> Result<(String, u32, Vec<TextOp>)> {
    let (base, width) = strip_suffix(mnem);
    // Control-flow mnemonics take a bare label (not an `%reg`/`$imm`/mem operand).
    if base.starts_with('j') && base.len() >= 2 {
        return Ok((
            base.to_string(),
            width,
            vec![TextOp::Label(rest.trim().to_string())],
        ));
    }
    // `call`: a direct symbol, or an indirect `*%reg` / `*(mem)` target.
    if base == "call" {
        let t = rest.trim();
        let op = if let Some(r) = t.strip_prefix("*%").and_then(reg_number) {
            TextOp::Reg(r)
        } else if let Some(m) = t.strip_prefix('*').and_then(parse_mem) {
            TextOp::Mem(m)
        } else {
            TextOp::Label(t.to_string())
        };
        return Ok(("call".to_string(), width, vec![op]));
    }
    let mut ops = Vec::new();
    for tok in split_operands(rest) {
        ops.push(operand(tok)?);
    }
    Ok((base.to_string(), width, ops))
}

/// One AT&T operand token → [`TextOp`].
fn operand(tok: &str) -> Result<TextOp> {
    let tok = tok.trim();
    if let Some(imm) = parse_imm(tok) {
        return Ok(TextOp::Imm(imm));
    }
    if let Some(r) = tok.strip_prefix('%').and_then(reg_number) {
        return Ok(TextOp::Reg(r));
    }
    if let Some(mem) = parse_mem(tok) {
        return Ok(TextOp::Mem(mem));
    }
    Err(Error::unsupported(format!("asm: operand `{tok}`")))
}

/// Split an operand list on top-level commas (commas inside `(...)` belong to a
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

/// A `disp(%base,%index,scale)` / `sym(%rip)` memory operand → [`MemOperand`].
fn parse_mem(tok: &str) -> Option<MemOperand> {
    let tok = tok.trim();
    let open = tok.find('(')?;
    if !tok.ends_with(')') {
        return None;
    }
    let disp_str = tok[..open].trim();
    let inner = &tok[open + 1..tok.len() - 1];
    let parts: Vec<&str> = inner.split(',').map(str::trim).collect();
    // A RIP-relative access `symbol(%rip)`: base is `%rip`, displacement is a symbol.
    if parts.first().copied() == Some("%rip") {
        return Some(MemOperand {
            base: reg(0),
            index: None,
            disp: 0,
            next: 0,
            symbol: Some(disp_str.to_string()),
        });
    }
    let disp: i64 = if open == 0 { 0 } else { parse_disp(disp_str)? };
    let base = parts
        .first()
        .copied()?
        .strip_prefix('%')
        .and_then(reg_number)?;
    let index = match parts.get(1) {
        Some(r) if !r.is_empty() => {
            let ir = r.strip_prefix('%').and_then(reg_number)?;
            let scale: u8 = parts.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);
            Some((reg(ir), scale))
        }
        _ => None,
    };
    Some(MemOperand {
        base: reg(base),
        index,
        disp,
        next: 0,
        symbol: None,
    })
}

fn parse_disp(s: &str) -> Option<i64> {
    super::intel::parse_int(s.trim())
}

fn parse_imm(tok: &str) -> Option<i64> {
    parse_disp(tok.trim().strip_prefix('$')?)
}

/// Strip the AT&T size suffix (`b`/`w`/`l`/`q`) from a mnemonic that carries one,
/// returning `(base, operand-width-in-bits)`. Only strips when the shortened form
/// is a recognised instruction so `jle`→`jl` etc. are not mangled.
fn strip_suffix(mnem: &str) -> (&str, u32) {
    let known_base = |m: &str| {
        matches!(
            m,
            "mov"
                | "add"
                | "sub"
                | "and"
                | "or"
                | "xor"
                | "cmp"
                | "test"
                | "inc"
                | "dec"
                | "lea"
                | "push"
                | "pop"
                | "call"
        ) || m.starts_with("cmov")
    };
    for (suf, w) in [('q', 64u32), ('l', 32), ('w', 16), ('b', 8)] {
        if let Some(stripped) = mnem.strip_suffix(suf) {
            if known_base(stripped) {
                return (stripped, w);
            }
        }
    }
    // `retq` keeps its `q`; normalise the two spellings the shared layer accepts.
    (mnem, 64)
}
