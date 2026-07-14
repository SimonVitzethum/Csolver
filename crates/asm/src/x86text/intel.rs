//! Intel-syntax operand grammar (`clang -masm=intel`): `rax`, `123`/`0x7b`,
//! `<size> ptr [base + index*scale + disp]`, `[rip + sym]`; operand order is
//! `dst, src`, which this **reverses** to the shared `src, dst` convention.
//!
//! The access width comes from an explicit `byte/word/dword/qword ptr` keyword
//! or, absent that, from a register operand's width (default 64) — mirroring how
//! the CPU sizes an Intel instruction without a memory size suffix.

use super::{reg_number, reg_width, TextOp};
use crate::x86::{reg, MemOperand};
use csolver_core::{Error, Result};

/// Parse `mnem`'s operands (`rest`) into `(base mnemonic, width bits, operands)`
/// in the shared source-first order.
pub(super) fn parse(mnem: &str, rest: &str) -> Result<(String, u32, Vec<TextOp>)> {
    let base = mnem.to_ascii_lowercase();
    // Control-flow: a bare label target.
    if base.starts_with('j') && base.len() >= 2 {
        return Ok((base, 64, vec![TextOp::Label(rest.trim().to_string())]));
    }
    // `call`: a register, a `[mem]` indirect target, or a direct symbol.
    if base == "call" {
        let t = rest.trim();
        let op = if let Some((n, _)) = reg_token(t) {
            TextOp::Reg(n)
        } else if t.contains('[') {
            parse_mem(t)
                .map(TextOp::Mem)
                .unwrap_or_else(|| TextOp::Label(t.to_string()))
        } else {
            TextOp::Label(t.to_string())
        };
        return Ok((base, 64, vec![op]));
    }
    let toks = split_operands(rest);
    // Width: an explicit `ptr` size keyword wins; else the widest register operand.
    let mut width = 0u32;
    for t in &toks {
        if let Some(w) = ptr_size(t) {
            width = width.max(w);
        } else if let Some(w) = reg_token(t).map(|(_, w)| w) {
            width = width.max(w);
        }
    }
    let width = if width == 0 { 64 } else { width };
    let mut ops: Vec<TextOp> = Vec::new();
    for tok in toks {
        ops.push(operand(tok)?);
    }
    // Intel lists destination first; the shared lowering wants source first.
    ops.reverse();
    Ok((base, width, ops))
}

/// One Intel operand token → [`TextOp`].
fn operand(tok: &str) -> Result<TextOp> {
    let tok = tok.trim();
    if let Some((n, _)) = reg_token(tok) {
        return Ok(TextOp::Reg(n));
    }
    if tok.contains('[') {
        if let Some(mem) = parse_mem(tok) {
            return Ok(TextOp::Mem(mem));
        }
        return Err(Error::unsupported(format!("asm: memory operand `{tok}`")));
    }
    if let Some(v) = parse_int(tok) {
        return Ok(TextOp::Imm(v));
    }
    Err(Error::unsupported(format!("asm: operand `{tok}`")))
}

/// A bare register token → `(number, width)`; `None` if not a register.
fn reg_token(tok: &str) -> Option<(u8, u32)> {
    let name = tok.trim();
    reg_number(name).map(|n| (n, reg_width(name)))
}

/// The width a leading `byte/word/dword/qword/xmmword ptr` keyword denotes.
fn ptr_size(tok: &str) -> Option<u32> {
    let lower = tok.trim().to_ascii_lowercase();
    let kw = lower.split_whitespace().next()?;
    match kw {
        "byte" => Some(8),
        "word" => Some(16),
        "dword" => Some(32),
        "qword" => Some(64),
        "xmmword" => Some(128),
        _ => None,
    }
}

/// An Intel `[base + index*scale + disp]` / `[rip + sym]` memory operand,
/// optionally preceded by a `<size> ptr` keyword and/or a `seg:` prefix.
fn parse_mem(tok: &str) -> Option<MemOperand> {
    let open = tok.find('[')?;
    let close = tok.rfind(']')?;
    if close < open {
        return None;
    }
    let inner = &tok[open + 1..close];
    let (mut base, mut index, mut disp, mut symbol) =
        (None::<u8>, None::<(u8, u8)>, 0i64, None::<String>);
    let mut rip = false;
    for (sign, term) in signed_terms(inner) {
        let term = term.trim();
        if term.is_empty() {
            continue;
        }
        if term.eq_ignore_ascii_case("rip") {
            rip = true;
            continue;
        }
        // `index*scale` (or `scale*index`).
        if let Some((a, b)) = term.split_once('*') {
            let (a, b) = (a.trim(), b.trim());
            let (rname, sc) = match (reg_number(a), b.parse::<u8>().ok()) {
                (Some(r), Some(s)) => (r, s),
                _ => match (reg_number(b), a.parse::<u8>().ok()) {
                    (Some(r), Some(s)) => (r, s),
                    _ => return None,
                },
            };
            index = Some((rname, sc));
            continue;
        }
        if let Some(r) = reg_number(term) {
            // First bare register is the base; a second becomes an index (scale 1).
            if base.is_none() {
                base = Some(r);
            } else if index.is_none() {
                index = Some((r, 1));
            } else {
                return None;
            }
            continue;
        }
        // A displacement: a signed integer, or a relocation symbol name.
        if let Some(v) = parse_int(term) {
            disp += if sign { -v } else { v };
        } else if is_sym(term) {
            symbol = Some(term.to_string());
        } else {
            return None;
        }
    }
    // A RIP-relative access (`[rip + sym]`) or a base-less symbol reference resolves
    // to a global symbol base (the executor turns `@sym` into that global's region).
    if rip || (base.is_none() && symbol.is_some()) {
        return Some(MemOperand {
            base: reg(0),
            index: index.map(|(r, s)| (reg(r), s)),
            disp,
            next: 0,
            symbol: Some(symbol.unwrap_or_else(|| "<rip-unknown>".to_string())),
        });
    }
    Some(MemOperand {
        base: reg(base?),
        index: index.map(|(r, s)| (reg(r), s)),
        disp,
        next: 0,
        symbol: None,
    })
}

/// Split a memory operand's inner terms on `+`/`-`, keeping each term's sign
/// (`true` = subtracted). `rbp - 4` → `[(false,"rbp"), (true,"4")]`.
fn signed_terms(inner: &str) -> Vec<(bool, &str)> {
    let mut out = Vec::new();
    let (mut start, mut neg) = (0usize, false);
    for (i, c) in inner.char_indices() {
        if c == '+' || c == '-' {
            let term = inner[start..i].trim();
            if !term.is_empty() {
                out.push((neg, term));
            }
            neg = c == '-';
            start = i + 1;
        }
    }
    let last = inner[start..].trim();
    if !last.is_empty() {
        out.push((neg, last));
    }
    out
}

/// Split an Intel operand list on top-level commas (commas do not appear inside
/// `[...]`, but guard the bracket depth anyway).
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

/// Parse a decimal or `0x`-hex integer (with optional sign). Shared with the
/// AT&T grammar's displacement/immediate parsing.
pub(super) fn parse_int(s: &str) -> Option<i64> {
    let s = s.trim();
    let (neg, s) = match s.strip_prefix('-') {
        Some(rest) => (true, rest.trim()),
        None => (false, s),
    };
    let v = if let Some(h) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        i64::from_str_radix(h, 16).ok()?
    } else {
        s.parse::<i64>().ok()?
    };
    Some(if neg { -v } else { v })
}

fn is_sym(s: &str) -> bool {
    let s = s.strip_prefix("offset ").unwrap_or(s).trim();
    !s.is_empty()
        && s.chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_' || c == '.')
        && s.chars()
            .all(|c| c.is_alphanumeric() || matches!(c, '_' | '.' | '$' | '@'))
}
