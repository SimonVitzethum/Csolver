//! A recursive-descent parser for a practical subset of textual LLVM IR.
//!
//! Supported: `define`d functions; integer/`ptr`/array/`void` types (and legacy
//! `T*`); the instructions `alloca`, `load`, `store`, `getelementptr`
//! (pointer-arith and `[N x T]` array forms), the integer binary ops, `icmp`,
//! the integer/pointer casts, `call`, and `phi`; the terminators `ret`, `br`
//! (conditional and unconditional) and `unreachable`. Anything outside the
//! subset is reported as an error so the caller degrades to `UNKNOWN` rather
//! than silently mis-modelling it.

use crate::lexer::{lex, Tok};
use csolver_core::{Error, Result};
use std::collections::HashMap;


// --- module split (mechanical refactor) ---
mod ast;
mod attrs;
mod func;
mod globals;
mod helpers;
mod inst;
mod lex;
#[cfg(test)]
#[path = "parser/tests.rs"]
mod tests;
pub use ast::*;
pub(crate) use helpers::*;

/// Parse a `.ll` source into an [`LModule`].
pub fn parse_module(src: &str) -> Result<LModule> {
    let debuginfo = crate::debuginfo::parse(src);
    let toks = lex(src)?;
    let mut p = Parser {
        toks,
        pos: 0,
        types: HashMap::new(),
        meta_ints: scan_meta_ints(src),
        deref_hints: HashMap::new(),
    };
    // Pre-scan for `%"name" = type <T>` definitions: a definition may lexically
    // follow its first use, so the table must be complete before any function
    // parses. An unparseable definition is skipped — a function using it then
    // fails per-function recovery (UNKNOWN), never a silent guess.
    p.collect_type_defs();
    p.pos = 0;
    let mut funcs = Vec::new();
    let mut unanalyzed = Vec::new();
    let mut globals = Vec::new();
    loop {
        p.skip_newlines();
        match p.peek() {
            Tok::Eof => break,
            // `@name = … global/constant <ty> <init>[, align N]` — a definition
            // the analysis can size. An unparseable line is skipped whole (its
            // symbol stays an opaque scalar).
            Tok::Global(_) if matches!(p.peek2(), Tok::Punct('=')) => {
                if let Some(g) = p.global_def() {
                    globals.push(g);
                }
            }
            Tok::Word(w) if w == "define" => {
                let start = p.pos;
                match p.function() {
                    Ok(f) => funcs.push(f),
                    // Per-function recovery: skip this function's body and
                    // record it so the verifier reports it as UNKNOWN.
                    Err(e) => {
                        p.pos = start;
                        let name = p.recover_function();
                        unanalyzed.push((name, e.to_string()));
                    }
                }
            }
            // Every other top-level line — `declare`, `source_filename`,
            // `target …`, `attributes #N = …`, `%T = type …`, `@g = …`, and
            // `!…` metadata — is irrelevant to the analysis and skipped.
            _ => p.skip_to_eol(),
        }
    }
    Ok(LModule {
        funcs,
        unanalyzed,
        globals,
        debuginfo,
        deref_hints: std::mem::take(&mut p.deref_hints),
    })
}

pub(crate) struct Parser {
    pub(crate) toks: Vec<Tok>,
    pub(crate) pos: usize,
    /// Top-level `%"name" = type <T>` definitions, collected in a pre-scan (a
    /// definition may lexically follow its first use). Values may themselves
    /// contain [`LType::Named`] references; [`Parser::resolve_named`] substitutes
    /// them at use time.
    pub(crate) types: HashMap<String, LType>,
    /// Single-integer metadata nodes (`!N = !{iW V}`), pre-scanned so an
    /// instruction's `!align !N` reference can be resolved to its value `V` while
    /// the instruction is parsed (the node may lexically follow the use).
    pub(crate) meta_ints: HashMap<u32, u64>,
    /// Per global-symbol, the largest `dereferenceable(N)` any use asserts on a
    /// **bare** `@g` operand. Clang emits it from the operand's *type* size, so it is
    /// an authoritative lower bound on the global's byte size — used to correct a
    /// size our own type-layout computation gets wrong (e.g. a 1-byte packed-struct
    /// discrepancy). Sound: it can only *raise* a global's size.
    pub(crate) deref_hints: HashMap<String, u64>,
}

/// Pre-scan single-integer metadata nodes (`!126 = !{i64 8}`) into a map from
/// node id to value. Only exact `!{iW V}` shapes are recorded — enough for the
/// `!align`/`!range`-style annotations the analysis reads; anything else is left
/// out (a missing entry just means the annotation is not credited).
fn scan_meta_ints(src: &str) -> HashMap<u32, u64> {
    let mut m = HashMap::new();
    for line in src.lines() {
        let Some((id, after)) = line
            .trim()
            .strip_prefix('!')
            .and_then(|r| r.split_once(" = "))
        else {
            continue;
        };
        let Ok(id) = id.trim().parse::<u32>() else {
            continue;
        };
        let Some(inner) = after
            .trim()
            .strip_prefix("!{")
            .and_then(|s| s.strip_suffix('}'))
        else {
            continue;
        };
        let mut parts = inner.split_whitespace();
        match (parts.next(), parts.next(), parts.next()) {
            // A single `iW V` element (no trailing tokens).
            (Some(ty), Some(val), None) if ty.starts_with('i') => {
                if let Ok(v) = val.trim_end_matches(',').parse::<u64>() {
                    m.insert(id, v);
                }
            }
            _ => {}
        }
    }
    m
}

