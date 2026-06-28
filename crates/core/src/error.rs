//! The crate-wide error type.
//!
//! CSolver distinguishes *tool errors* (something went wrong inside the
//! verifier — a parse failure, an unsupported construct, an I/O problem) from
//! *verification outcomes* (`FAIL` / `UNKNOWN`). The latter are **not** errors;
//! they are first-class results modelled by [`crate::Verdict`] and
//! [`crate::ObligationResult`]. This type only covers the former.

use std::fmt;

/// A tool-level error: the verifier could not run an analysis to completion.
///
/// This is never used to report that a program is unsafe — that is a
/// [`crate::Verdict::Fail`], not an `Error`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// An input could not be parsed at the given (best-effort) location.
    Parse {
        /// Human-readable description of what failed to parse.
        message: String,
        /// Where the failure was detected, if known.
        location: Option<crate::Location>,
    },
    /// A construct is recognized but not yet handled by an analysis.
    ///
    /// Unsupported constructs must degrade a verdict to `Unknown` with an
    /// explicit residual obligation — never silently to `Pass`.
    Unsupported {
        /// What is not supported.
        what: String,
    },
    /// An internal invariant was violated. This indicates a bug in CSolver.
    Internal {
        /// Description of the violated invariant.
        message: String,
    },
    /// An I/O error while reading an input artifact.
    Io {
        /// Description of the I/O failure.
        message: String,
    },
}

impl Error {
    /// Construct an [`Error::Unsupported`].
    pub fn unsupported(what: impl Into<String>) -> Self {
        Error::Unsupported { what: what.into() }
    }

    /// Construct an [`Error::Internal`].
    pub fn internal(message: impl Into<String>) -> Self {
        Error::Internal {
            message: message.into(),
        }
    }

    /// Construct an [`Error::Parse`] without a location.
    pub fn parse(message: impl Into<String>) -> Self {
        Error::Parse {
            message: message.into(),
            location: None,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Parse { message, location } => match location {
                Some(loc) => write!(f, "parse error at {loc}: {message}"),
                None => write!(f, "parse error: {message}"),
            },
            Error::Unsupported { what } => write!(f, "unsupported construct: {what}"),
            Error::Internal { message } => write!(f, "internal error: {message}"),
            Error::Io { message } => write!(f, "i/o error: {message}"),
        }
    }
}

impl std::error::Error for Error {}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Error::Io {
            message: e.to_string(),
        }
    }
}

/// The crate-wide result alias for tool-level operations.
pub type Result<T> = std::result::Result<T, Error>;
