use super::*;

/// Evaluate a condition under a fixed interval state.
pub(crate) fn eval_condition_in(cond: &Condition, state: &IntervalState) -> Trivalent {
    match cond {
        Condition::True => Trivalent::True,
        Condition::Cmp { op, lhs, rhs } => {
            compare_intervals(*op, &eval_operand(lhs, state), &eval_operand(rhs, state))
        }
        Condition::And(cs) => {
            let mut all_true = true;
            for c in cs {
                match eval_condition_in(c, state) {
                    Trivalent::False => return Trivalent::False,
                    Trivalent::Unknown => all_true = false,
                    Trivalent::True => {}
                }
            }
            if all_true {
                Trivalent::True
            } else {
                Trivalent::Unknown
            }
        }
        Condition::Or(cs) => {
            let mut all_false = true;
            for c in cs {
                match eval_condition_in(c, state) {
                    Trivalent::True => return Trivalent::True,
                    Trivalent::Unknown => all_false = false,
                    Trivalent::False => {}
                }
            }
            if all_false {
                Trivalent::False
            } else {
                Trivalent::Unknown
            }
        }
        Condition::Not(c) => eval_condition_in(c, state).negate(),
    }
}

/// `x <= y` in the extended bound order.
pub(crate) fn bound_le(x: Bound, y: Bound) -> bool {
    use Bound::*;
    match (x, y) {
        (NegInf, _) => true,
        (_, PosInf) => true,
        (_, NegInf) => false,
        (PosInf, _) => false,
        (Fin(a), Fin(b)) => a <= b,
    }
}

/// `x < y` in the extended bound order.
pub(crate) fn bound_lt(x: Bound, y: Bound) -> bool {
    bound_le(x, y) && !bound_le(y, x)
}

/// Trivalent comparison of two intervals under the given predicate. Values are
/// compared as signed integers; this is sound for the non-negative indices and
/// sizes that dominate bounds checks, and the verifier escalates genuinely
/// unsigned-sensitive cases to the solver (M1+).
pub(crate) fn compare_intervals(op: CmpOp, a: &Interval, b: &Interval) -> Trivalent {
    let (Some(alo), Some(ahi), Some(blo), Some(bhi)) =
        (a.lower(), a.upper(), b.lower(), b.upper())
    else {
        // One side is bottom (unreachable value): indeterminate.
        return Trivalent::Unknown;
    };

    // Helper closures for the primitive relations.
    let lt = || {
        if bound_lt(ahi, blo) {
            Trivalent::True
        } else if bound_le(bhi, alo) {
            Trivalent::False
        } else {
            Trivalent::Unknown
        }
    };
    let le = || {
        if bound_le(ahi, blo) {
            Trivalent::True
        } else if bound_lt(bhi, alo) {
            Trivalent::False
        } else {
            Trivalent::Unknown
        }
    };
    let gt = || {
        // a > b  <=>  b < a
        if bound_lt(bhi, alo) {
            Trivalent::True
        } else if bound_le(ahi, blo) {
            Trivalent::False
        } else {
            Trivalent::Unknown
        }
    };
    let ge = || {
        // a >= b  <=>  b <= a
        if bound_le(bhi, alo) {
            Trivalent::True
        } else if bound_lt(ahi, blo) {
            Trivalent::False
        } else {
            Trivalent::Unknown
        }
    };

    match op {
        CmpOp::Ult | CmpOp::Slt => lt(),
        CmpOp::Ule | CmpOp::Sle => le(),
        CmpOp::Ugt | CmpOp::Sgt => gt(),
        CmpOp::Uge | CmpOp::Sge => ge(),
        CmpOp::Eq => {
            // Disjoint => never equal; identical singletons => always equal.
            if bound_lt(ahi, blo) || bound_lt(bhi, alo) {
                Trivalent::False
            } else if alo == ahi && blo == bhi && alo == blo {
                Trivalent::True
            } else {
                Trivalent::Unknown
            }
        }
        CmpOp::Ne => compare_intervals(CmpOp::Eq, a, b).negate(),
    }
}
