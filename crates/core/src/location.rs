//! Source locations, abstracted over the analysis level.
//!
//! A proof obligation can originate at any of the levels CSolver understands
//! (MIR, LLVM-IR, assembly, ELF). [`Location`] is the common, level-tagged
//! coordinate that flows through obligations, proofs, and reports.

use std::fmt;

/// Which representation level a location refers to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SourceLevel {
    /// Rust MIR.
    Mir,
    /// LLVM intermediate representation.
    Llvm,
    /// Machine assembly (x86-64 or AArch64).
    Asm,
    /// A loaded ELF/PE/Mach-O image.
    Elf,
}

impl fmt::Display for SourceLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            SourceLevel::Mir => "mir",
            SourceLevel::Llvm => "llvm",
            SourceLevel::Asm => "asm",
            SourceLevel::Elf => "elf",
        };
        f.write_str(s)
    }
}

/// A half-open byte span `[start, end)` into an input artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Span {
    /// Inclusive start byte offset.
    pub start: u32,
    /// Exclusive end byte offset.
    pub end: u32,
}

impl Span {
    /// Create a span; `start` must not exceed `end`.
    pub fn new(start: u32, end: u32) -> Self {
        debug_assert!(start <= end, "span start must not exceed end");
        Span { start, end }
    }

    /// The number of bytes covered.
    pub fn len(&self) -> u32 {
        self.end.saturating_sub(self.start)
    }

    /// Whether the span is empty.
    pub fn is_empty(&self) -> bool {
        self.start >= self.end
    }
}

/// A level-tagged program location.
///
/// `function` and `instruction` are symbolic, stable identifiers (names or
/// indices rendered as strings) rather than typed IDs, so that `core` stays
/// free of dependencies on the IR crate while still letting reports point at a
/// precise spot.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Location {
    /// The representation level this location lives at.
    pub level: SourceLevel,
    /// The enclosing function/symbol name, if known.
    pub function: Option<String>,
    /// The instruction index within the function, if known.
    pub instruction: Option<u32>,
    /// A free-form pointer for the level (e.g. a virtual address, a `.ll` line,
    /// a MIR statement path) for human consumption.
    pub raw: Option<String>,
    /// An optional byte span into the originating textual artifact.
    pub span: Option<Span>,
}

impl Location {
    /// A location that only names the level (used when nothing finer is known).
    pub fn level_only(level: SourceLevel) -> Self {
        Location {
            level,
            function: None,
            instruction: None,
            raw: None,
            span: None,
        }
    }

    /// Builder: attach a function name.
    pub fn in_function(mut self, name: impl Into<String>) -> Self {
        self.function = Some(name.into());
        self
    }

    /// Builder: attach an instruction index.
    pub fn at_instruction(mut self, index: u32) -> Self {
        self.instruction = Some(index);
        self
    }

    /// Builder: attach the free-form source pointer (`raw`), e.g. a
    /// `FILE:LINE:COL` from MIR spans or a DWARF line for a binary. A no-op for
    /// `None`, so callers thread it unconditionally.
    pub fn with_raw(mut self, raw: Option<String>) -> Self {
        if raw.is_some() {
            self.raw = raw;
        }
        self
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.level)?;
        if let Some(func) = &self.function {
            write!(f, ":{func}")?;
        }
        if let Some(i) = self.instruction {
            write!(f, "#{i}")?;
        }
        if let Some(raw) = &self.raw {
            write!(f, " ({raw})")?;
        }
        Ok(())
    }
}
