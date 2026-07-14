use super::*;
use crate::bitprecise::prove_implies;

/// Truncate a `u128` to `w` low bits.
fn mask(v: u128, w: u32) -> u128 {
    if w >= 128 {
        v
    } else {
        v & ((1u128 << w) - 1)
    }
}

/// Interpret the low `w` bits of `v` as a two's-complement signed integer.
fn as_signed(v: u128, w: u32) -> i128 {
    let v = mask(v, w);
    if v & (1u128 << (w - 1)) != 0 {
        (v as i128) - (1i128 << w)
    } else {
        v as i128
    }
}

/// Reference oracle for a `w`-bit binary op, computed independently of the
/// bit-blaster (plain wrapping arithmetic, masked to width).
fn oracle_bin(op: BvOp, a: u128, b: u128, w: u32) -> u128 {
    match op {
        BvOp::Add => mask(a.wrapping_add(b), w),
        BvOp::Sub => mask(a.wrapping_sub(b), w),
        BvOp::Mul => mask(a.wrapping_mul(b), w),
        BvOp::And => a & b,
        BvOp::Or => a | b,
        BvOp::Xor => a ^ b,
        // Shifts by >= width are all-zero (Shl/LShr) or all-sign (AShr),
        // matching `Blaster::shift_const`.
        BvOp::Shl if b >= w as u128 => 0,
        BvOp::Shl => mask(a << b, w),
        BvOp::LShr if b >= w as u128 => 0,
        BvOp::LShr => mask(a, w) >> b,
        BvOp::AShr => {
            let s = as_signed(a, w);
            let k = if b >= w as u128 { w - 1 } else { b as u32 };
            mask((s >> k) as u128, w)
        }
        // Division/remainder — the caller guarantees `b != 0` (the 0-divisor totality
        // contract is checked separately). Signed ops round toward zero (Rust `/`, `%`
        // on `i128`), matching LLVM/SMT; `INT_MIN / -1` masks back to `INT_MIN` with no
        // `i128` overflow since `w < 128`.
        BvOp::UDiv => mask(a / b, w),
        BvOp::URem => mask(a % b, w),
        BvOp::SDiv => mask((as_signed(a, w) / as_signed(b, w)) as u128, w),
        BvOp::SRem => mask((as_signed(a, w) % as_signed(b, w)) as u128, w),
    }
}

/// Reference oracle for a `w`-bit comparison.
fn oracle_cmp(op: CmpOp, a: u128, b: u128, w: u32) -> bool {
    match op {
        CmpOp::Eq => a == b,
        CmpOp::Ne => a != b,
        CmpOp::Ult => a < b,
        CmpOp::Ule => a <= b,
        CmpOp::Ugt => a > b,
        CmpOp::Uge => a >= b,
        CmpOp::Slt => as_signed(a, w) < as_signed(b, w),
        CmpOp::Sle => as_signed(a, w) <= as_signed(b, w),
        CmpOp::Sgt => as_signed(a, w) > as_signed(b, w),
        CmpOp::Sge => as_signed(a, w) >= as_signed(b, w),
    }
}

/// Exhaustively check every `w`-bit input pair against the oracle. For each
/// op we assert two things: the correct result *is* provable (the circuit is
/// not under-constrained) and a deliberately wrong result is *not* provable
/// (the circuit — and the equality assumptions pinning the inputs — are not
/// over-constrained, which would make everything vacuously "provable").
fn check_exhaustive(w: u32) {
    let n = 1u128 << w;
    let bin_ops = [
        BvOp::Add,
        BvOp::Sub,
        BvOp::Mul,
        BvOp::And,
        BvOp::Or,
        BvOp::Xor,
    ];
    let shift_ops = [BvOp::Shl, BvOp::LShr, BvOp::AShr];
    let cmp_ops = [
        CmpOp::Eq,
        CmpOp::Ne,
        CmpOp::Ult,
        CmpOp::Ule,
        CmpOp::Ugt,
        CmpOp::Uge,
        CmpOp::Slt,
        CmpOp::Sle,
        CmpOp::Sgt,
        CmpOp::Sge,
    ];

    for va in 0..n {
        for vb in 0..n {
            let mut c = ExprCtx::new();
            let a = c.symbol("a", w);
            let b = c.symbol("b", w);
            let ca = c.int(w, va);
            let cb = c.int(w, vb);
            let eq_a = c.cmp(CmpOp::Eq, a, ca);
            let eq_b = c.cmp(CmpOp::Eq, b, cb);
            let assume_ab = [eq_a, eq_b];
            let assume_a = [eq_a];

            // Two symbolic operands: Add/Sub/Mul/And/Or/Xor.
            for op in bin_ops {
                let expr = c.bin(op, a, b);
                let want = oracle_bin(op, va, vb, w);
                let goal = {
                    let k = c.int(w, want);
                    c.cmp(CmpOp::Eq, expr, k)
                };
                assert!(
                    prove_implies(&c, &assume_ab, goal),
                    "{op:?} a={va} b={vb} (w{w}): correct result {want} not provable",
                );
                let bad = {
                    let wrong = c.int(w, mask(want.wrapping_add(1), w));
                    c.cmp(CmpOp::Eq, expr, wrong)
                };
                assert!(
                    !prove_implies(&c, &assume_ab, bad),
                    "{op:?} a={va} b={vb} (w{w}): a wrong result was provable",
                );
            }

            // Division/remainder (two symbolic operands), skipping the 0-divisor case
            // (its SMT-LIB-total valuation is asserted separately below).
            if vb != 0 {
                for op in [BvOp::UDiv, BvOp::SDiv, BvOp::URem, BvOp::SRem] {
                    let expr = c.bin(op, a, b);
                    let want = oracle_bin(op, va, vb, w);
                    let goal = {
                        let k = c.int(w, want);
                        c.cmp(CmpOp::Eq, expr, k)
                    };
                    assert!(
                        prove_implies(&c, &assume_ab, goal),
                        "{op:?} a={va} b={vb} (w{w}): correct result {want} not provable",
                    );
                    let bad = {
                        let wrong = c.int(w, mask(want.wrapping_add(1), w));
                        c.cmp(CmpOp::Eq, expr, wrong)
                    };
                    assert!(
                        !prove_implies(&c, &assume_ab, bad),
                        "{op:?} a={va} b={vb} (w{w}): a wrong result was provable",
                    );
                }
            }

            // Constant-amount shifts (the right operand is the constant cb).
            for op in shift_ops {
                let expr = c.bin(op, a, cb);
                let want = oracle_bin(op, va, vb, w);
                let goal = {
                    let k = c.int(w, want);
                    c.cmp(CmpOp::Eq, expr, k)
                };
                assert!(
                    prove_implies(&c, &assume_a, goal),
                    "{op:?} a={va} by {vb} (w{w}): correct result {want} not provable",
                );
            }

            // Symbolic-amount shifts (both operands symbolic → the barrel shifter). The oracle
            // covers `amount >= w` (all-zero for Shl/LShr, all-sign for AShr).
            for op in shift_ops {
                let expr = c.bin(op, a, b);
                let want = oracle_bin(op, va, vb, w);
                let goal = {
                    let k = c.int(w, want);
                    c.cmp(CmpOp::Eq, expr, k)
                };
                assert!(
                    prove_implies(&c, &assume_ab, goal),
                    "{op:?} a={va} by symbolic {vb} (w{w}): correct result {want} not provable",
                );
                let bad = {
                    let wrong = c.int(w, mask(want.wrapping_add(1), w));
                    c.cmp(CmpOp::Eq, expr, wrong)
                };
                assert!(
                    !prove_implies(&c, &assume_ab, bad),
                    "{op:?} a={va} by symbolic {vb} (w{w}): a wrong result was provable",
                );
            }

            // Comparisons: the truth value must be provable, its negation not.
            for op in cmp_ops {
                let res = c.cmp(op, a, b);
                let nres = c.not(res);
                let want = oracle_cmp(op, va, vb, w);
                assert_eq!(
                    prove_implies(&c, &assume_ab, res),
                    want,
                    "{op:?} a={va} b={vb} (w{w}): truth value mismatch",
                );
                assert_eq!(
                    prove_implies(&c, &assume_ab, nres),
                    !want,
                    "{op:?} a={va} b={vb} (w{w}): negated truth value mismatch",
                );
            }
        }
    }
}

/// Always-on TCB guard: 4 bits exercise full carry/borrow chains across
/// every position, in well under a second.
#[test]
fn bitblast_matches_oracle_4bit() {
    check_exhaustive(4);
}

/// Deeper paranoia run (`cargo test -- --ignored`): 6 bits, ~4k pairs.
#[test]
#[ignore = "slow exhaustive sweep; run on demand"]
fn bitblast_matches_oracle_6bit() {
    check_exhaustive(6);
}

/// The **symbolic** barrel shifter at the full 64-bit width — the stage count (6) and the
/// out-of-range guard (`amount >= 64`) are exercised only here, not by the small sweeps. For a
/// fixed `a` and each of a few boundary amounts (0, 1, 63, 64, u64::MAX) pinned on the symbolic
/// operand, the correct result must be provable and a wrong one not.
#[test]
fn symbolic_shift_at_width_64_boundaries() {
    let w = 64;
    let a_val = 0xF0F0_F0F0_0F0F_0F0Fu128;
    for op in [BvOp::Shl, BvOp::LShr, BvOp::AShr] {
        for amt in [0u128, 1, 63, 64, u64::MAX as u128] {
            let mut c = ExprCtx::new();
            let a = c.symbol("a", w);
            let b = c.symbol("b", w);
            let ca = c.int(w, a_val);
            let cb = c.int(w, amt);
            let assume = [c.cmp(CmpOp::Eq, a, ca), c.cmp(CmpOp::Eq, b, cb)];
            let expr = c.bin(op, a, b);
            let want = oracle_bin(op, a_val, amt, w);
            let goal = {
                let k = c.int(w, want);
                c.cmp(CmpOp::Eq, expr, k)
            };
            assert!(prove_implies(&c, &assume, goal), "{op:?} by {amt} (w64): {want:#x} not provable");
            let bad = {
                let wrong = c.int(w, mask(want.wrapping_add(1), w));
                c.cmp(CmpOp::Eq, expr, wrong)
            };
            assert!(!prove_implies(&c, &assume, bad), "{op:?} by {amt} (w64): wrong result provable");
        }
    }
}

/// Full **128-bit** width (`MAX_WIDTH`): the adder, shift-add multiplier, barrel shifter,
/// bitwise and comparison circuits must all stay exact at the widest blastable width — the
/// small sweeps never reach it. Two pinned `i128`-range operands are checked against plain
/// `u128` wrapping arithmetic. (128-bit `udiv`/`urem` build a ~370k-clause divider that
/// exceeds the CNF cap and fall back soundly to the linear procedure, so they are not asserted
/// here — see `MAX_CLAUSES`.)
#[test]
fn wide_ops_at_width_128_are_bit_precise() {
    let w = 128;
    let av = 0x1234_5678_9abc_def0_0fed_cba9_8765_4321u128;
    let bv = 0x0000_0000_dead_beef_0000_0000_cafe_babeu128;
    let checks: [(BvOp, u128); 6] = [
        (BvOp::Add, av.wrapping_add(bv)),
        (BvOp::Sub, av.wrapping_sub(bv)),
        (BvOp::Mul, av.wrapping_mul(bv)),
        (BvOp::And, av & bv),
        (BvOp::Or, av | bv),
        (BvOp::Xor, av ^ bv),
    ];
    for (op, want) in checks {
        let mut c = ExprCtx::new();
        let a = c.symbol("a", w);
        let b = c.symbol("b", w);
        let ca = c.int(w, av);
        let cb = c.int(w, bv);
        let assume = [c.cmp(CmpOp::Eq, a, ca), c.cmp(CmpOp::Eq, b, cb)];
        let expr = c.bin(op, a, b);
        let k = c.int(w, want);
        let goal = c.cmp(CmpOp::Eq, expr, k);
        assert!(prove_implies(&c, &assume, goal), "{op:?} at w128: {want:#x} not provable");
        let bad = c.int(w, want.wrapping_add(1));
        let badgoal = c.cmp(CmpOp::Eq, expr, bad);
        assert!(!prove_implies(&c, &assume, badgoal), "{op:?} at w128: wrong result provable");
    }
    // A symbolic 128-bit shift (barrel shifter) by a pinned amount, and an unsigned compare.
    let mut c = ExprCtx::new();
    let a = c.symbol("a", w);
    let b = c.symbol("b", w);
    let ca = c.int(w, av);
    let cb = c.int(w, 100);
    let assume = [c.cmp(CmpOp::Eq, a, ca), c.cmp(CmpOp::Eq, b, cb)];
    let shl = c.bin(BvOp::Shl, a, b);
    let k = c.int(w, av << 100); // 100 < 128, well-defined
    let goal = c.cmp(CmpOp::Eq, shl, k);
    assert!(prove_implies(&c, &assume, goal), "shl by 100 at w128 not provable");
    let cmp = c.cmp(CmpOp::Ugt, a, b); // av > 100
    assert!(prove_implies(&c, &assume, cmp), "128-bit unsigned compare not decided");
}

/// The division circuits must be **total** on a zero divisor, matching SMT-LIB:
/// `bvudiv a 0 = ~0` (all ones) and `bvurem a 0 = a`. This pins the corner the
/// exhaustive sweep skips, so a term is never left under-constrained even absent
/// a `NoDivByZero` guard (the guard independently flags the UB, but the solver
/// must still be sound if it ever encodes the raw term).
#[test]
fn division_by_zero_is_smtlib_total() {
    let w = 4;
    let ones = mask(u128::MAX, w);
    for va in 0..(1u128 << w) {
        let mut c = ExprCtx::new();
        let a = c.symbol("a", w);
        let ca = c.int(w, va);
        let z = c.int(w, 0);
        let assume = [c.cmp(CmpOp::Eq, a, ca)];

        let udiv = c.bin(BvOp::UDiv, a, z);
        let want_q = c.int(w, ones);
        let q_ok = c.cmp(CmpOp::Eq, udiv, want_q);
        assert!(prove_implies(&c, &assume, q_ok), "udiv a 0 must be all-ones (a={va})");

        let urem = c.bin(BvOp::URem, a, z);
        let want_r = c.int(w, va);
        let r_ok = c.cmp(CmpOp::Eq, urem, want_r);
        assert!(prove_implies(&c, &assume, r_ok), "urem a 0 must be a (a={va})");
    }
}

/// Regression for the `shift_const` overflow: at width 64 a constant shift
/// amount near `u64::MAX` used to overflow `i + k` and wrap to a small index,
/// fabricating `a[wrapped]` where the result must be all-zero / all-sign. A
/// huge shift must be provably 0 (Shl/LShr) for every `a`, and its negation
/// unprovable.
#[test]
fn huge_constant_shift_is_zero_at_width_64() {
    let w = 64;
    for op in [BvOp::Shl, BvOp::LShr] {
        let mut c = ExprCtx::new();
        let a = c.symbol("a", w);
        let amt = c.int(w, u64::MAX as u128); // 2^64 - 1, well past the width
        let shifted = c.bin(op, a, amt);
        let zero = c.int(w, 0);
        let is_zero = c.cmp(CmpOp::Eq, shifted, zero);
        assert!(
            prove_implies(&c, &[], is_zero),
            "{op:?} by u64::MAX must be 0 for all a",
        );
        let nonzero = c.not(is_zero);
        assert!(
            !prove_implies(&c, &[], nonzero),
            "{op:?} by u64::MAX must not be provably non-zero",
        );
    }
}
