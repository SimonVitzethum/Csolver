use super::*;

#[test]
fn hash_consing_shares_structure() {
    let mut c = ExprCtx::new();
    let x = c.symbol("x", 64);
    let a = c.bin(BvOp::Add, x, x);
    let b = c.bin(BvOp::Add, x, x);
    assert_eq!(a, b, "identical expressions intern to the same id");
    let before = c.len();
    let _ = c.bin(BvOp::Add, x, x);
    assert_eq!(c.len(), before, "no new node for a repeated expression");
}

#[test]
fn symbols_of_collects_variables() {
    let mut c = ExprCtx::new();
    let x = c.symbol("x", 64);
    let y = c.symbol("y", 64);
    let five = c.int(64, 5);
    // (x + 5) < y  — variables {x, y}, sorted & deduplicated.
    let sum = c.bin(BvOp::Add, x, five);
    let cmp = c.cmp(CmpOp::Ult, sum, y);
    let mut want = vec![x, y];
    want.sort_unstable();
    assert_eq!(c.symbols_of(cmp), want, "collects each distinct variable once");
    // A constant expression has no variables.
    let konst = c.bin(BvOp::Add, five, five);
    assert!(c.symbols_of(konst).is_empty(), "a constant has no variables");
    // A shared variable used twice appears once.
    let xx = c.bin(BvOp::Xor, x, x);
    assert_eq!(c.symbols_of(xx), vec![x], "a repeated variable is deduplicated");
}

#[test]
fn constant_folding() {
    let mut c = ExprCtx::new();
    let two = c.int(64, 2);
    let three = c.int(64, 3);
    let sum = c.bin(BvOp::Add, two, three);
    assert_eq!(c.as_const(sum).map(|v| v.unsigned()), Some(5));
    let four = c.int(64, 4);
    let prod = c.bin(BvOp::Mul, sum, four);
    assert_eq!(c.as_const(prod).map(|v| v.unsigned()), Some(20));
}

#[test]
fn identities() {
    let mut c = ExprCtx::new();
    let x = c.symbol("x", 64);
    let zero = c.int(64, 0);
    assert_eq!(c.bin(BvOp::Add, x, zero), x);
    assert_eq!(c.bin(BvOp::Sub, x, zero), x);
    assert_eq!(c.bin(BvOp::Mul, x, zero), zero);
    let self_sub = c.bin(BvOp::Sub, x, x);
    assert_eq!(c.as_const(self_sub).map(|v| v.unsigned()), Some(0));
}

#[test]
fn comparison_folding_and_negation() {
    let mut c = ExprCtx::new();
    let three = c.int(64, 3);
    let eight = c.int(64, 8);
    let lt = c.cmp(CmpOp::Ult, three, eight);
    assert_eq!(c.as_bool(lt), Some(true));
    let x = c.symbol("x", 64);
    let y = c.symbol("y", 64);
    let cmp = c.cmp(CmpOp::Ult, x, y);
    let neg = c.not(cmp);
    // ¬(x < y) is (x >= y).
    assert!(matches!(c.node(neg), Node::Cmp { op: CmpOp::Uge, .. }));
    // double negation cancels.
    assert_eq!(c.not(neg), cmp);
}

#[test]
fn boolean_connectives_normalize() {
    let mut c = ExprCtx::new();
    let t = c.boolean(true);
    let f = c.boolean(false);
    let x = c.symbol("x", 64);
    let eight = c.int(64, 8);
    let p = c.cmp(CmpOp::Ult, x, eight);
    assert_eq!(c.and(vec![t, p]), p);
    let and_f = c.and(vec![f, p]);
    assert_eq!(c.as_bool(and_f), Some(false));
    let or_t = c.or(vec![t, p]);
    assert_eq!(c.as_bool(or_t), Some(true));
    assert_eq!(c.or(vec![f, p]), p);
}

#[test]
fn ite_collapses() {
    let mut c = ExprCtx::new();
    let t = c.boolean(true);
    let a = c.int(64, 1);
    let b = c.int(64, 2);
    assert_eq!(c.ite(t, a, b), a);
    let x = c.symbol("x", 1);
    assert_eq!(c.ite(x, a, a), a);
}
