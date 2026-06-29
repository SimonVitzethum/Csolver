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
//! The drivers **fuzz** their inputs (a tiny dependency-free PRNG — see
//! `tests/drive.rs`) rather than hard-wiring one value, so Miri reaches UB paths
//! that a hand-picked input would miss, and the safe functions are exercised over
//! a broad input range instead of a single case.
//!
//! The corpus deliberately mixes provably-safe functions (CSolver should PASS,
//! Miri clean) with functions that are UB on a reachable input (CSolver must not
//! PASS, Miri finds the UB when driven there). It is organised by the realistic
//! code patterns that dominate real Rust — helper chains, nested indexing,
//! off-by-one at a slice end, conditional frees — so the `UNKNOWN`-on-safe rows
//! become a data-driven priority list for the remaining capabilities.
//!
//! Private `fn` helpers are *not* corpus entries (the harness keys off `pub fn`),
//! but they still appear in the emitted MIR, so the helper-chain functions test
//! CSolver's interprocedural reasoning end to end.

// ===== safe: memory-safe for every input. CSolver should ideally PASS. ========

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

/// A modulo-reduced index — always in bounds when the slice is non-empty.
pub fn clamp_get(s: &[i32], i: usize) -> i32 {
    if s.is_empty() {
        0
    } else {
        s[i % s.len()]
    }
}

/// Off-by-one at the end, the *safe* side: touches the last two elements behind a
/// length guard.
pub fn guarded_pair(s: &[i32]) -> i32 {
    if s.len() >= 2 {
        s[s.len() - 2] + s[s.len() - 1]
    } else {
        0
    }
}

/// A nested index (`m[i][j]`) behind a conjoined guard — safe for every `i`,`j`.
pub fn nested_get(m: &[[i32; 4]], i: usize, j: usize) -> i32 {
    if i < m.len() && j < 4 {
        m[i][j]
    } else {
        0
    }
}

/// A two-slice copy loop bounded by the shorter length — every access in bounds.
pub fn copy_within_guard(dst: &mut [i32], src: &[i32]) {
    let n = dst.len().min(src.len());
    let mut k = 0;
    while k < n {
        dst[k] = src[k];
        k += 1;
    }
}

/// A `min`-clamped index — always in bounds when the slice is non-empty.
pub fn min_index_get(s: &[i32], i: usize) -> i32 {
    if s.is_empty() {
        0
    } else {
        s[i.min(s.len() - 1)]
    }
}

/// A sliding-window sum (safe iterator) — no explicit index at all.
pub fn window_sum(s: &[i32]) -> i64 {
    s.windows(2).map(|w| w[0] as i64 + w[1] as i64).sum()
}

// ---- struct field access through a reference: always in bounds by typing ------

/// A small struct, to exercise field access through a reference.
pub struct Pair {
    pub a: i32,
    pub b: i32,
}

/// A field read through `&Pair` — a typed field of a valid reference is always in
/// bounds.
pub fn read_field(p: &Pair) -> i32 {
    p.a
}

/// A field write through `&mut Pair` — always in bounds and permitted (mutable).
pub fn write_field(p: &mut Pair, v: i32) {
    p.a = v;
}

// ---- helper chains: the safety precondition flows across a call boundary ------

/// First element via a helper that returns `Option<&_>` — safe for every slice.
pub fn head_via_helper(s: &[i32]) -> i32 {
    *first_ref(s).unwrap_or(&0)
}

fn first_ref(s: &[i32]) -> Option<&i32> {
    s.first()
}

/// A guarded index whose bound comes from a helper call — safe for every `i`.
pub fn helper_bound(s: &[i32], i: usize) -> i32 {
    if i < len_of(s) {
        s[i]
    } else {
        -1
    }
}

fn len_of(s: &[i32]) -> usize {
    s.len()
}

// ===== unsafe: UB on a reachable input. CSolver must NOT say PASS. ============

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

/// Off-by-one at the end, the *UB* side: the loop bound `<=` reads `s[len]`.
pub fn off_by_one_loop(s: &[i32]) -> i64 {
    let mut acc = 0i64;
    let mut i = 0;
    while i <= s.len() {
        acc += unsafe { *s.get_unchecked(i) } as i64;
        i += 1;
    }
    acc
}

/// A raw pointer stepped *before* the start of the allocation — always UB.
pub fn raw_sub(s: &[i32]) -> i32 {
    unsafe { *s.as_ptr().sub(1) }
}

/// A helper computes an out-of-range index, then it is used unchecked — UB.
pub fn oob_via_helper(s: &[i32]) -> i32 {
    unsafe { *s.get_unchecked(over_len(s)) }
}

fn over_len(s: &[i32]) -> usize {
    s.len() + 1
}

/// A conditional free, then a use of the dangling pointer — UB iff `free_it`.
pub fn cond_use_after_free(free_it: bool) -> i32 {
    let v = vec![1, 2, 3];
    let p = v.as_ptr();
    if free_it {
        drop(v);
    }
    unsafe { *p }
}

/// A null dereference — UB iff `use_null` (otherwise a valid promoted constant).
pub fn null_deref(use_null: bool) -> i32 {
    let p: *const i32 = if use_null {
        std::ptr::null()
    } else {
        &7
    };
    unsafe { *p }
}

/// A slice fabricated longer than its allocation, then read past the end — UB.
pub fn slice_oob_from_raw(s: &[i32]) -> i32 {
    let longer = unsafe { std::slice::from_raw_parts(s.as_ptr(), s.len() + 4) };
    longer[s.len() + 2]
}

/// An unchecked nested index — out of bounds for `i >= rows` or `j >= 4`.
pub fn nested_oob(m: &[[i32; 4]], i: usize, j: usize) -> i32 {
    unsafe { *m.get_unchecked(i).as_ptr().add(j) }
}
