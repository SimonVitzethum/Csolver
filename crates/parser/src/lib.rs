//! # csolver-parser
//!
//! Shared, frontend-agnostic parsing infrastructure: a byte [`Cursor`] with
//! lookahead and a [`Diagnostics`] sink that produces [`csolver_core::Error`]s
//! carrying [`csolver_core::Span`]s. The LLVM-IR and assembly textual frontends
//! build their lexers on top of this rather than re-implementing cursor
//! bookkeeping.
//!
//! This crate deliberately contains no grammar; it is plumbing.

use csolver_core::{Error, Location, SourceLevel, Span};

/// A forward byte cursor over a source string with O(1) lookahead.
#[derive(Debug, Clone)]
pub struct Cursor<'a> {
    src: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    /// Create a cursor at the start of `src`.
    pub fn new(src: &'a str) -> Self {
        Cursor {
            src: src.as_bytes(),
            pos: 0,
        }
    }

    /// The current byte offset.
    pub fn offset(&self) -> u32 {
        self.pos as u32
    }

    /// Whether the cursor is at end of input.
    pub fn is_eof(&self) -> bool {
        self.pos >= self.src.len()
    }

    /// Peek at the next byte without consuming it.
    pub fn peek(&self) -> Option<u8> {
        self.src.get(self.pos).copied()
    }

    /// Peek `n` bytes ahead.
    pub fn peek_at(&self, n: usize) -> Option<u8> {
        self.src.get(self.pos + n).copied()
    }

    /// Consume and return the next byte.
    pub fn bump(&mut self) -> Option<u8> {
        let b = self.src.get(self.pos).copied();
        if b.is_some() {
            self.pos += 1;
        }
        b
    }

    /// Consume bytes while `pred` holds, returning the consumed slice as `&str`
    /// (the input is assumed UTF-8; bytes are ASCII for our grammars).
    pub fn take_while(&mut self, mut pred: impl FnMut(u8) -> bool) -> &'a str {
        let start = self.pos;
        while let Some(b) = self.peek() {
            if pred(b) {
                self.pos += 1;
            } else {
                break;
            }
        }
        std::str::from_utf8(&self.src[start..self.pos]).unwrap_or("")
    }

    /// Skip ASCII whitespace.
    pub fn skip_whitespace(&mut self) {
        self.take_while(|b| b.is_ascii_whitespace());
    }

    /// A [`Span`] from `start` to the current offset.
    pub fn span_from(&self, start: u32) -> Span {
        Span::new(start, self.offset())
    }
}

/// A collector of parse diagnostics, tagged with the level being parsed.
#[derive(Debug, Clone)]
pub struct Diagnostics {
    level: SourceLevel,
    errors: Vec<Error>,
}

impl Diagnostics {
    /// A new sink for the given level.
    pub fn new(level: SourceLevel) -> Self {
        Diagnostics {
            level,
            errors: Vec::new(),
        }
    }

    /// Record a parse error at `span`.
    pub fn error(&mut self, message: impl Into<String>, span: Span) {
        let mut loc = Location::level_only(self.level);
        loc.span = Some(span);
        self.errors.push(Error::Parse {
            message: message.into(),
            location: Some(loc),
        });
    }

    /// Whether any errors were recorded.
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// The recorded errors.
    pub fn errors(&self) -> &[Error] {
        &self.errors
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cursor_walks_and_takes() {
        let mut c = Cursor::new("ab12  cd");
        assert_eq!(c.peek(), Some(b'a'));
        let word = c.take_while(|b| b.is_ascii_alphanumeric());
        assert_eq!(word, "ab12");
        c.skip_whitespace();
        assert_eq!(c.peek(), Some(b'c'));
        assert!(!c.is_eof());
    }

    #[test]
    fn diagnostics_record_spans() {
        let mut d = Diagnostics::new(SourceLevel::Llvm);
        assert!(!d.has_errors());
        d.error("unexpected token", Span::new(2, 4));
        assert!(d.has_errors());
        assert_eq!(d.errors().len(), 1);
    }
}
