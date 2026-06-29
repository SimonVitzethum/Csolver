//! Differential-validation corpus.
//!
//! Each `pub fn` here is verified **statically** by CSolver (on its
//! `rustc --emit=mir` output) and exercised **dynamically** by Miri (via a
//! sibling driver in `tests/drive.rs`). The harness (`run.sh`) compares the two:
//!
//! - Miri reports UB on some driven input  ⟹  CSolver must **never** say `PASS`
//!   (a `PASS` here would be an unsound false positive — the cardinal sin).
//! - Miri stays clean                       ⟹  CSolver should ideally `PASS`,
//!   but `UNKNOWN` is acceptable (a precision miss, not a soundness break).
//!
//! The corpus deliberately mixes provably-safe functions (CSolver should PASS,
//! Miri clean) with functions that are UB on a reachable input (CSolver must not
//! PASS, Miri finds the UB when driven there).

// ---- safe: bounds-checked / statically in range. CSolver should PASS. --------

/// A guarded slice index — safe for every `i`.
pub fn checked_get(s: &[i32], i: usize) -> i32 {
    if i < s.len() {
        s[i]
    } else {
        -1
    }
}

/// A constant index into a fixed-size array — statically in bounds.
pub fn array_first(a: &[i32; 8]) -> i32 {
    a[0]
}

/// An index-based slice loop — every access is in bounds by the guard.
pub fn sum(s: &[i32]) -> i64 {
    let mut acc = 0i64;
    let mut i = 0;
    while i < s.len() {
        acc += s[i] as i64;
        i += 1;
    }
    acc
}

/// The last-element idiom — `len - 1` is a derived index, safe when non-empty.
pub fn last(s: &[i32]) -> i32 {
    if s.is_empty() {
        0
    } else {
        s[s.len() - 1]
    }
}

/// A mutable-slice fill loop — every write is in bounds by the guard.
pub fn fill(s: &mut [u8], v: u8) {
    let mut i = 0;
    while i < s.len() {
        s[i] = v;
        i += 1;
    }
}

/// A guarded two-slice access — safe for every `i` by the conjoined guard.
pub fn two_slice(a: &[i32], b: &[i32], i: usize) -> i32 {
    if i < a.len() && i < b.len() {
        a[i] + b[i]
    } else {
        0
    }
}

// ---- unsafe: UB on a reachable input. CSolver must NOT say PASS. -------------

/// `get_unchecked(i)` with no bounds check — out of bounds for `i >= len`.
pub fn unchecked_oob(s: &[i32], i: usize) -> i32 {
    unsafe { *s.get_unchecked(i) }
}

/// Reads one past the end — out of bounds for any slice.
pub fn past_end(s: &[i32]) -> i32 {
    unsafe { *s.get_unchecked(s.len()) }
}

/// An unchecked write past the end — out of bounds for `i >= len`.
pub fn unchecked_write(s: &mut [i32], i: usize) {
    unsafe {
        *s.get_unchecked_mut(i) = 0;
    }
}

/// A raw-pointer offset and dereference with no bounds check — out of bounds for
/// `i >= len`. A distinct unsafe shape from `get_unchecked`.
pub fn raw_add(s: &[i32], i: usize) -> i32 {
    unsafe { *s.as_ptr().add(i) }
}
