//! Opt-in parameter **preconditions** from a sidecar file.
//!
//! C's type system cannot state "this pointer is valid for `n` elements" or "this
//! string is non-null", so a raw pointer parameter is soundly `UNKNOWN` in
//! isolation (its validity is the caller's obligation). A precondition file lets
//! the user declare that obligation — the way a `_Nonnull` / `access(...)`
//! attribute documents an API contract — so an annotated library function
//! verifies without needing every caller in view.
//!
//! Each precondition becomes a **prove-only** parameter contract (`refutable =
//! false`): the callee may assume it, and proofs resting on it surface the
//! `precondition` assumption, making the trust basis explicit in the report. It
//! is the caller's job to establish it — so a witness *against* it (a null or
//! undersized argument) is not treated as a real counterexample.
//!
//! ## Format
//!
//! One precondition per line; `#` starts a comment. Fields are whitespace-
//! separated:
//!
//! ```text
//! <function>  <param-index>  bytes     <N>            [readonly]
//! <function>  <param-index>  elements  <len-param>  <elem-bytes>  [readonly]
//! ```
//!
//! - `bytes N` — the pointer is valid for `N` bytes.
//! - `elements L E` — valid for `(param L)` elements of `E` bytes each (a
//!   `(ptr, len)` buffer: `sum(const T* p, int n)` is `p 0 elements 1 sizeof(T)`).
//! - `cstring N` — valid for `N` bytes AND null-terminated (a zero *byte* before
//!   the end): bounds a `strlen`-shaped `while (p[n]) n++` scan.
//! - `sentinel N E` — as `cstring`, but with an `E`-byte zero terminator element.
//! - `readonly` — grant read but not write (default is read+write).

use csolver_ir::{FuncId, Module, PtrContract, SizeSpec};
use std::collections::HashMap;

/// One parsed precondition, before it is resolved against a module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Precondition {
    /// Name of the function the precondition applies to.
    pub function: String,
    /// 0-based index of the pointer parameter.
    pub param: u32,
    /// The size of the valid region behind the pointer.
    pub size: SizeSpec,
    /// Guaranteed alignment of the pointer in bytes.
    pub align: u32,
    /// Whether the pointee may be written (else read-only).
    pub writable: bool,
    /// `Some(elem_bytes)` if the region is sentinel-terminated (a zero element of
    /// that width exists before the end) — bounds a `while (p[n] != 0)` scan.
    pub sentinel: Option<u64>,
}

/// Parse a precondition file, returning a helpful error (with the 1-based line
/// number) on the first malformed line.
pub fn parse(text: &str) -> Result<Vec<Precondition>, String> {
    let mut out = Vec::new();
    for (n, line) in text.lines().enumerate() {
        let line = line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        out.push(parse_line(line).map_err(|e| format!("precondition line {}: {e}", n + 1))?);
    }
    Ok(out)
}

fn parse_line(line: &str) -> Result<Precondition, String> {
    let f: Vec<&str> = line.split_whitespace().collect();
    let err = || format!("expected `<fn> <param> bytes <N> | elements <lp> <eb> [readonly]`, got `{line}`");
    if f.len() < 4 {
        return Err(err());
    }
    let function = f[0].to_string();
    let param: u32 = f[1].parse().map_err(|_| err())?;
    let (size, align, sentinel, rest_at) = match f[2] {
        // A byte size carries no element type, so alignment stays 1 (an aligned
        // access through it then remains an obligation).
        "bytes" => (SizeSpec::Bytes(f[3].parse().map_err(|_| err())?), 1, None, 4),
        "elements" => {
            if f.len() < 5 {
                return Err(err());
            }
            let len_param: u32 = f[3].parse().map_err(|_| err())?;
            let elem_size: u64 = f[4].parse().map_err(|_| err())?;
            // A buffer of `E`-byte elements is naturally `E`-aligned (capped).
            let align = (elem_size.max(1) as u32).min(16).next_power_of_two();
            (SizeSpec::ParamElements { len_param, elem_size }, align, None, 5)
        }
        // A null-terminated C string: `N` bytes, with a zero *byte* terminator
        // within. `sentinel <N> <E>` generalizes to an `E`-byte zero element.
        "cstring" => (SizeSpec::Bytes(f[3].parse().map_err(|_| err())?), 1, Some(1), 4),
        "sentinel" => {
            if f.len() < 5 {
                return Err(err());
            }
            let n: u64 = f[3].parse().map_err(|_| err())?;
            let elem: u64 = f[4].parse().map_err(|_| err())?;
            let align = (elem.max(1) as u32).min(16).next_power_of_two();
            (SizeSpec::Bytes(n), align, Some(elem), 5)
        }
        other => return Err(format!("unknown precondition kind `{other}`")),
    };
    let writable = match f.get(rest_at) {
        None => true,
        Some(&"readonly") => false,
        Some(other) => return Err(format!("expected `readonly` or end of line, got `{other}`")),
    };
    Ok(Precondition { function, param, size, align, writable, sentinel })
}

/// Apply preconditions to a module's parameter contracts. A function named in the
/// file but absent from the module is reported; a parameter already carrying a
/// declared contract is left untouched (the declared attribute wins). Returns the
/// number of preconditions applied.
pub fn apply(module: &mut Module, preconds: &[Precondition]) -> Result<usize, String> {
    let by_name: HashMap<&str, FuncId> =
        module.functions.iter().map(|f| (f.name.as_str(), f.id)).collect();
    let mut applied = 0;
    for p in preconds {
        let fid = *by_name
            .get(p.function.as_str())
            .ok_or_else(|| format!("precondition names unknown function `{}`", p.function))?;
        let key = (fid, p.param);
        // An explicit precondition outranks a contract the frontend *guessed* (the opt-in C
        // `(buf, len)` pairing), but never one the IR actually declares (`dereferenceable`, a
        // Rust slice): those are facts, not heuristics, and the sidecar must not weaken them.
        let guessed = |c: &PtrContract| c.assumption == Some("param-buffer-len");
        if module.param_contracts.get(&key).is_some_and(|c| !guessed(c)) {
            continue;
        }
        module.param_contracts.insert(
            key,
            PtrContract {
                size: p.size,
                align: p.align,
                readable: true,
                writable: p.writable,
                assumption: Some("precondition"),
                // Caller-established: prove-only, never refuted (a witness against
                // it may be an argument no valid caller passes).
                refutable: false,
                sentinel: p.sentinel,
            },
        );
        applied += 1;
    }
    Ok(applied)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_specs_and_comments() {
        let text = "# a comment\nsum 0 elements 1 8\nfill 2 bytes 64 readonly\n\n";
        let p = parse(text).expect("parse");
        assert_eq!(p.len(), 2);
        assert_eq!(p[0].function, "sum");
        assert_eq!(p[0].param, 0);
        assert!(matches!(p[0].size, SizeSpec::ParamElements { len_param: 1, elem_size: 8 }));
        assert_eq!(p[0].align, 8, "an 8-byte element buffer is 8-aligned");
        assert!(p[0].writable);
        assert!(matches!(p[1].size, SizeSpec::Bytes(64)));
        assert!(!p[1].writable, "readonly");
    }

    #[test]
    fn parses_cstring_and_sentinel() {
        let p = parse("s 0 cstring 4096\nw 1 sentinel 800 2").expect("parse");
        assert!(matches!(p[0].size, SizeSpec::Bytes(4096)));
        assert_eq!(p[0].sentinel, Some(1), "cstring is a 1-byte zero terminator");
        assert!(matches!(p[1].size, SizeSpec::Bytes(800)));
        assert_eq!(p[1].sentinel, Some(2), "sentinel element width");
        assert_eq!(p[1].align, 2);
    }

    #[test]
    fn rejects_malformed_lines_with_line_number() {
        assert!(parse("sum 0 wat 3").unwrap_err().contains("line 1"));
        assert!(parse("ok 0 bytes 8\nbad line here too few").unwrap_err().contains("line 2"));
    }

    #[test]
    fn apply_reports_unknown_function() {
        let module = Module::new("m");
        let pre = vec![Precondition {
            function: "nope".into(),
            param: 0,
            size: SizeSpec::Bytes(8),
            align: 1,
            writable: true,
            sentinel: None,
        }];
        assert!(apply(&mut { module }, &pre).unwrap_err().contains("unknown function"));
    }
}
