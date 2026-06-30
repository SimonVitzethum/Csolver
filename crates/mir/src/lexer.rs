//! A tokenizer for textual Rust MIR (as emitted by `rustc --emit=mir` /
//! `-Zunpretty=mir`).
//!
//! It recognizes the lexical classes the parser needs: bare words (keywords,
//! locals `_N`, blocks `bbN`, type names, rvalue/operator names), integer
//! literals (with Rust's `_` digit separators and type suffixes), string
//! literals (assert messages), the `->` and `=>` arrows, and single-character
//! punctuation. Line (`//`) comments and whitespace are skipped.

use csolver_core::Result;

/// A single MIR token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Tok {
    /// A bare word: keyword, local (`_1`), block (`bb0`), type, or operator name.
    Word(String),
    /// An integer literal (suffix and `_` separators stripped).
    Int(i128),
    /// A string literal's contents (e.g. an assert message).
    Str(String),
    /// A single punctuation character: one of `(){}[],;:=.*&<>+%`.
    Punct(char),
    /// `->` (terminator edge).
    Arrow,
    /// `=>` (debug binding).
    FatArrow,
    /// End of input.
    Eof,
}

/// Tokenize the whole input, returning the tokens plus a parallel vector giving
/// each token's source location (`FILE:LINE:COL`) when the MIR carries one
/// (`rustc +nightly --emit=mir -Z mir-include-spans`). A token's location is the
/// span comment trailing its line, back-filled to every token on that line; it is
/// `None` for stable MIR (no spans) and non-statement lines, so the result
/// degrades cleanly. The two vectors are the same length.
pub(crate) fn lex(src: &str) -> Result<(Vec<Tok>, Vec<Option<String>>)> {
    let b = src.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    let mut locs: Vec<Option<String>> = Vec::new();
    // Index in `out` where the current source line's tokens began, so a trailing
    // `// … at FILE:L:C` comment can be back-filled to the whole line.
    let mut line_start = 0usize;
    while i < b.len() {
        let c = b[i];
        match c {
            b'\n' => {
                i += 1;
                line_start = out.len();
            }
            b' ' | b'\t' | b'\r' => i += 1,
            b'/' if b.get(i + 1) == Some(&b'/') => {
                let start = i;
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
                if let Some(loc) = extract_src_loc(&b[start..i]) {
                    for slot in locs.iter_mut().take(out.len()).skip(line_start) {
                        *slot = Some(loc.clone());
                    }
                }
            }
            b'-' if b.get(i + 1) == Some(&b'>') => {
                out.push(Tok::Arrow);
                i += 2;
            }
            b'=' if b.get(i + 1) == Some(&b'>') => {
                out.push(Tok::FatArrow);
                i += 2;
            }
            b'"' => {
                let (s, ni) = lex_string(b, i)?;
                i = ni;
                out.push(Tok::Str(s));
            }
            b'0'..=b'9' => {
                let (v, ni) = lex_number(b, i);
                i = ni;
                out.push(Tok::Int(v));
            }
            _ if is_ident_start(c) => {
                let start = i;
                while i < b.len() && is_ident_byte(b[i]) {
                    i += 1;
                }
                out.push(Tok::Word(str_of(&b[start..i])));
            }
            b'(' | b')' | b'{' | b'}' | b'[' | b']' | b',' | b';' | b':' | b'=' | b'.' | b'*'
            | b'&' | b'<' | b'>' | b'+' | b'-' | b'%' | b'!' => {
                out.push(Tok::Punct(c as char));
                i += 1;
            }
            // Skip anything else (e.g. stray sigils in annotations) defensively.
            _ => i += 1,
        }
        // Keep `locs` parallel to `out` without touching each token-push site.
        locs.resize(out.len(), None);
    }
    out.push(Tok::Eof);
    locs.resize(out.len(), None);
    Ok((out, locs))
}

/// Extract a `FILE:LINE:COL` source location from a MIR span comment of the form
/// `// … at FILE:L1:C1: L2:C2`, taking the start (`FILE:L1:C1`). Tolerant: returns
/// `None` for any comment without a well-formed span (stable MIR has none), so the
/// lexer just skips it as before.
fn extract_src_loc(comment: &[u8]) -> Option<String> {
    let text = std::str::from_utf8(comment).ok()?;
    let after = text.rsplit_once(" at ")?.1.trim();
    // `FILE:L1:C1: L2:C2` → the start span is everything before the `": "`.
    let loc = after.split_once(": ").map_or(after, |(a, _)| a).trim();
    // Validate it ends with `:digits:digits`, so a stray "… at the call site" is
    // not mistaken for a location.
    let mut parts = loc.rsplit(':');
    let col_ok = parts.next().is_some_and(|c| !c.is_empty() && c.bytes().all(|d| d.is_ascii_digit()));
    let line_ok = parts.next().is_some_and(|l| !l.is_empty() && l.bytes().all(|d| d.is_ascii_digit()));
    (col_ok && line_ok && parts.next().is_some()).then(|| loc.to_string())
}

/// Read a number with Rust `_` digit separators and an optional type suffix
/// (`8_usize`, `1_000`, `0i32`): the value with separators removed, ignoring the
/// suffix.
fn lex_number(b: &[u8], mut i: usize) -> (i128, usize) {
    let mut digits = String::new();
    while i < b.len() {
        match b[i] {
            d @ b'0'..=b'9' => {
                digits.push(d as char);
                i += 1;
            }
            b'_' => i += 1, // separator, or start of a `_usize`-style suffix
            // A trailing type suffix (`usize`, `i32`, …): consume and drop it.
            c if c.is_ascii_alphabetic() => {
                while i < b.len() && is_ident_byte(b[i]) {
                    i += 1;
                }
                break;
            }
            _ => break,
        }
    }
    (digits.parse().unwrap_or(0), i)
}

/// Read a double-quoted string (with simple `\"` / `\\` escapes), returning its
/// contents and the index past the closing quote.
fn lex_string(b: &[u8], mut i: usize) -> Result<(String, usize)> {
    i += 1; // opening quote
    let mut s = String::new();
    while i < b.len() {
        match b[i] {
            b'"' => return Ok((s, i + 1)),
            // A real MIR string literal never spans a line (newlines are emitted as
            // `\n`). So a `"` with no close on its line is *not* a string opener —
            // it is a stray quote, e.g. in an `alloc … { 0x00 │ … │ !"#$… }` data
            // dump's ASCII column. End the token at the newline instead of eating
            // the rest of the file, so one such quote cannot vanish the whole crate
            // (lexing runs before per-function recovery).
            b'\n' => return Ok((s, i)),
            b'\\' if i + 1 < b.len() => {
                s.push(b[i + 1] as char);
                i += 2;
            }
            c => {
                s.push(c as char);
                i += 1;
            }
        }
    }
    Ok((s, i)) // EOF: recover rather than fail the module
}

fn is_ident_start(c: u8) -> bool {
    c.is_ascii_alphabetic() || c == b'_'
}

fn is_ident_byte(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

fn str_of(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}
