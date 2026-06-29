//! Miri drivers: one `drive_<fn>` test per corpus function, run in isolation by
//! the harness (`cargo +nightly miri test -- --exact drive_<fn>`). Each drives
//! its target with concrete inputs; `black_box` prevents the access from being
//! optimised away. The safe drivers exercise edge cases (empty, full, one-past);
//! the unsafe drivers pass the input that reaches the UB, so Miri reports it.

use differential::*;
use std::hint::black_box;

// ---- safe drivers: Miri should stay clean -----------------------------------

#[test]
fn drive_checked_get() {
    for &len in &[0usize, 1, 8] {
        let v: Vec<i32> = (0..len as i32).collect();
        for i in 0..len + 3 {
            black_box(checked_get(black_box(&v), black_box(i)));
        }
    }
}

#[test]
fn drive_array_first() {
    black_box(array_first(black_box(&[3, 1, 4, 1, 5, 9, 2, 6])));
}

#[test]
fn drive_sum() {
    for len in 0..6 {
        let v: Vec<i32> = (0..len).collect();
        black_box(sum(black_box(&v)));
    }
}

#[test]
fn drive_last() {
    for len in 0..6usize {
        let v: Vec<i32> = (0..len as i32).collect();
        black_box(last(black_box(&v)));
    }
}

#[test]
fn drive_fill() {
    for len in 0..6 {
        let mut v = vec![0u8; len];
        fill(black_box(&mut v), black_box(7));
        black_box(&v);
    }
}

#[test]
fn drive_two_slice() {
    let a = vec![1, 2, 3, 4];
    let b = vec![5, 6, 7];
    for i in 0..6 {
        black_box(two_slice(black_box(&a), black_box(&b), black_box(i)));
    }
}

// ---- unsafe drivers: Miri must report UB ------------------------------------

#[test]
fn drive_unchecked_oob() {
    let v = vec![1, 2, 3];
    black_box(unchecked_oob(black_box(&v), black_box(5)));
}

#[test]
fn drive_past_end() {
    let v = vec![1, 2, 3];
    black_box(past_end(black_box(&v)));
}

#[test]
fn drive_unchecked_write() {
    let mut v = vec![1, 2, 3];
    unchecked_write(black_box(&mut v), black_box(5));
    black_box(&v);
}

#[test]
fn drive_raw_add() {
    let v = vec![1, 2, 3];
    black_box(raw_add(black_box(&v), black_box(7)));
}
