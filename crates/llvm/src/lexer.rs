//! A tokenizer for textual LLVM IR (`.ll`).
//!
//! It recognizes the lexical classes the parser needs: local (`%x`) and global
//! (`@x`) identifiers, bare words (keywords, type names), integer literals, and
//! single-character punctuation. Line comments (`;` to end of line) and
//! whitespace are skipped. Quoted identifiers (`%"a b"`) are supported.

use csolver_core::{Error, Result};

/// A single LLVM-IR token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Tok {
    /// A local identifier without the leading `%` (e.g. `0`, `buf`).
    Local(String),
    /// A global identifier without the leading `@` (e.g. `memcpy`).
    Global(String),
    /// A bare word: keyword, opcode, or type name (e.g. `define`, `i32`, `x`).
    Word(String),
    /// An integer literal.
    Int(i128),
    /// A floating-point literal — decimal (`1.5`, `1.0e10`) or LLVM hex
    /// (`0x3E70000000000000`, `0xK…`). The text is kept verbatim; the value is
    /// never modelled (floats carry no memory-safety content), so the parser maps
    /// it to an opaque operand.
    Float(String),
    /// A single punctuation character: one of `(){}[],=:*<>#!`.
    Punct(char),
    /// A line break (statement separator; lets the parser drop trailing
    /// instruction metadata and skip top-level directive lines).
    Newline,
    /// End of input.
    Eof,
}

/// Tokenize the whole input, or report the first lexical error.
pub(crate) fn lex(src: &str) -> Result<Vec<Tok>> {
    let bytes = src.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    while i < bytes.len() {
        let b = bytes[i];
        match b {
            b' ' | b'\t' | b'\r' => i += 1,
            b'\n' => {
                out.push(Tok::Newline);
                i += 1;
            }
            b';' => {
                // Line comment (the terminating newline is emitted separately).
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'%' | b'@' => {
                let global = b == b'@';
                i += 1;
                let name = if i < bytes.len() && bytes[i] == b'"' {
                    let (s, ni) = lex_quoted(bytes, i)?;
                    i = ni;
                    s
                } else {
                    let start = i;
                    while i < bytes.len() && is_ident_byte(bytes[i]) {
                        i += 1;
                    }
                    if i == start {
                        return Err(Error::parse("empty identifier after % or @"));
                    }
                    str_of(&bytes[start..i])
                };
                out.push(if global { Tok::Global(name) } else { Tok::Local(name) });
            }
            b'"' => {
                let (s, ni) = lex_quoted(bytes, i)?;
                i = ni;
                out.push(Tok::Word(s));
            }
            // `|` occurs only in debug-metadata flag unions (`spFlags: A | B`),
            // on lines the parser skips wholesale; lex it as punctuation so a
            // debug-info (`-g`) module tokenises rather than erroring.
            b'(' | b')' | b'{' | b'}' | b'[' | b']' | b',' | b'=' | b':' | b'*' | b'<' | b'>'
            | b'#' | b'!' | b'|' => {
                out.push(Tok::Punct(b as char));
                i += 1;
            }
            // A standalone `-` (not the sign of a number) is punctuation.
            b'-' if !matches!(bytes.get(i + 1), Some(d) if d.is_ascii_digit()) => {
                out.push(Tok::Punct('-'));
                i += 1;
            }
            b'-' | b'0'..=b'9' => {
                let start = i;
                if b == b'-' {
                    i += 1;
                }
                let digits_start = i;
                while i < bytes.len() && bytes[i].is_ascii_digit() {
                    i += 1;
                }
                // Distinguish a float literal from an integer. LLVM hex float
                // constants are `0x` (optionally `0xK`/`0xH`/… ) + hex digits;
                // decimal floats carry a `.` and/or an `[eE]` exponent. Integers
                // in textual IR are plain decimal.
                let is_hex_float = i == digits_start + 1
                    && bytes[digits_start] == b'0'
                    && matches!(bytes.get(i), Some(b'x' | b'X'));
                let is_dec_float = matches!(bytes.get(i), Some(b'.'))
                    || matches!(bytes.get(i), Some(b'e' | b'E')
                        if matches!(bytes.get(i + 1), Some(d) if d.is_ascii_digit() || *d == b'+' || *d == b'-'));
                if is_hex_float || is_dec_float {
                    // Consume the rest of the float literal: hex digits, `.`,
                    // exponent, sign, and the `0xK`-style type letter.
                    i += 1; // the `.`, `x`, or `e`
                    // Optional `0xK`/`0xH`/`0xL`/`0xM`/`0xR` extended-precision tag.
                    if is_hex_float && matches!(bytes.get(i), Some(b'K' | b'H' | b'L' | b'M' | b'R')) {
                        i += 1;
                    }
                    while i < bytes.len()
                        && (bytes[i].is_ascii_hexdigit()
                            || matches!(bytes[i], b'.' | b'+' | b'-' | b'e' | b'E'))
                    {
                        i += 1;
                    }
                    out.push(Tok::Float(str_of(&bytes[start..i])));
                } else {
                    let text = str_of(&bytes[start..i]);
                    let n: i128 = text
                        .parse()
                        .map_err(|_| Error::parse(format!("bad integer literal `{text}`")))?;
                    out.push(Tok::Int(n));
                }
            }
            _ if is_word_start(b) => {
                let start = i;
                while i < bytes.len() && is_ident_byte(bytes[i]) {
                    i += 1;
                }
                out.push(Tok::Word(str_of(&bytes[start..i])));
            }
            other => {
                return Err(Error::parse(format!("unexpected character `{}`", other as char)));
            }
        }
    }
    out.push(Tok::Eof);
    Ok(out)
}

fn lex_quoted(bytes: &[u8], mut i: usize) -> Result<(String, usize)> {
    debug_assert_eq!(bytes[i], b'"');
    i += 1;
    let start = i;
    while i < bytes.len() && bytes[i] != b'"' {
        i += 1;
    }
    if i >= bytes.len() {
        return Err(Error::parse("unterminated quoted identifier"));
    }
    let s = str_of(&bytes[start..i]);
    Ok((s, i + 1))
}

fn is_word_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_' || b == b'.'
}

fn is_ident_byte(b: u8) -> bool {
    // `-` is a valid LLVM identifier byte (`%bb9thread-pre-split.i`, emitted by
    // jump threading). A *leading* `-` still lexes as a number/punct, so
    // negative literals are unaffected.
    b.is_ascii_alphanumeric() || b == b'_' || b == b'.' || b == b'$' || b == b'-'
}

fn str_of(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_no_nl(src: &str) -> Vec<Tok> {
        lex(src).unwrap().into_iter().filter(|t| *t != Tok::Newline).collect()
    }

    #[test]
    fn lexes_a_store() {
        let toks = lex_no_nl("store i32 0, ptr %p, align 4 ; comment\n");
        assert_eq!(
            toks,
            vec![
                Tok::Word("store".into()),
                Tok::Word("i32".into()),
                Tok::Int(0),
                Tok::Punct(','),
                Tok::Word("ptr".into()),
                Tok::Local("p".into()),
                Tok::Punct(','),
                Tok::Word("align".into()),
                Tok::Int(4),
                Tok::Eof,
            ]
        );
    }

    #[test]
    fn lexes_idents_and_negatives() {
        let toks = lex_no_nl("%0 @memcpy -7 [8 x i32]");
        assert_eq!(
            toks,
            vec![
                Tok::Local("0".into()),
                Tok::Global("memcpy".into()),
                Tok::Int(-7),
                Tok::Punct('['),
                Tok::Int(8),
                Tok::Word("x".into()),
                Tok::Word("i32".into()),
                Tok::Punct(']'),
                Tok::Eof,
            ]
        );
    }

    /// Float literals must lex as one `Float` token — hex (`0x…`, `0xK…`),
    /// decimal, and exponent forms — while plain decimal integers stay `Int`.
    #[test]
    fn lexes_float_literals() {
        assert_eq!(
            lex_no_nl("0x3E70000000000000 1.5 1.0e10 -2.5E-3 0xK4000C000000000000000 42 -7"),
            vec![
                Tok::Float("0x3E70000000000000".into()),
                Tok::Float("1.5".into()),
                Tok::Float("1.0e10".into()),
                Tok::Float("-2.5E-3".into()),
                Tok::Float("0xK4000C000000000000000".into()),
                Tok::Int(42),
                Tok::Int(-7),
                Tok::Eof,
            ]
        );
    }
}
