#![allow(clippy::unwrap_used)]
use super::*;

fn check_model(clauses: &[Vec<Lit>], model: &[bool]) -> bool {
    clauses.iter().all(|c| {
        c.iter()
            .any(|l| model[l.var as usize] != l.neg)
    })
}

#[test]
fn empty_clause_is_unsat() {
    let mut s = Solver::new(1, vec![vec![]]);
    assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
}

#[test]
fn no_clauses_is_sat() {
    let mut s = Solver::new(3, vec![]);
    assert!(matches!(s.solve(DEFAULT_BUDGET), SatResult::Sat(_)));
}

#[test]
fn unit_contradiction_is_unsat() {
    // (x) ∧ (¬x)
    let mut s = Solver::new(1, vec![vec![Lit::pos(0)], vec![Lit::neg(0)]]);
    assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
}

#[test]
fn simple_sat_has_valid_model() {
    // (x ∨ y) ∧ (¬x ∨ z)
    let clauses = vec![
        vec![Lit::pos(0), Lit::pos(1)],
        vec![Lit::neg(0), Lit::pos(2)],
    ];
    let mut s = Solver::new(3, clauses.clone());
    match s.solve(DEFAULT_BUDGET) {
        SatResult::Sat(m) => assert!(check_model(&clauses, &m)),
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn pigeonhole_2_into_1_is_unsat() {
    // Two pigeons, one hole: p0, p1 each must be in hole 0, but not both.
    // vars: x0 = pigeon0 in hole0, x1 = pigeon1 in hole0.
    // each pigeon in the hole: (x0), (x1); not both: (¬x0 ∨ ¬x1).
    let clauses = vec![
        vec![Lit::pos(0)],
        vec![Lit::pos(1)],
        vec![Lit::neg(0), Lit::neg(1)],
    ];
    let mut s = Solver::new(2, clauses);
    assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
}

#[test]
fn xor_chain_unsat() {
    // x0=x1, x1=x2, x2≠x0 — unsatisfiable.
    // x=y encoded (¬x∨y)(x∨¬y); x≠y encoded (x∨y)(¬x∨¬y).
    let clauses = vec![
        vec![Lit::neg(0), Lit::pos(1)],
        vec![Lit::pos(0), Lit::neg(1)],
        vec![Lit::neg(1), Lit::pos(2)],
        vec![Lit::pos(1), Lit::neg(2)],
        vec![Lit::pos(2), Lit::pos(0)],
        vec![Lit::neg(2), Lit::neg(0)],
    ];
    let mut s = Solver::new(3, clauses);
    assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
}

#[test]
fn pigeonhole_4_into_3_is_unsat() {
    // 4 pigeons into 3 holes — the smallest hole-principle instance that
    // actually forces conflict-driven learning + backjumping. var(p,h) = p*3+h.
    let v = |p: u32, h: u32| p * 3 + h;
    let mut clauses = Vec::new();
    // each pigeon sits in some hole
    for p in 0..4 {
        clauses.push((0..3).map(|h| Lit::pos(v(p, h))).collect());
    }
    // no two pigeons share a hole
    for h in 0..3 {
        for p1 in 0..4 {
            for p2 in (p1 + 1)..4 {
                clauses.push(vec![Lit::neg(v(p1, h)), Lit::neg(v(p2, h))]);
            }
        }
    }
    let mut s = Solver::new(12, clauses);
    assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
}

/// Pigeonhole `pigeons` into `holes` as a CNF over vars `v(p,h)=p*holes+h`.
fn pigeonhole(pigeons: u32, holes: u32) -> (usize, Vec<Vec<Lit>>) {
    let v = |p: u32, h: u32| p * holes + h;
    let mut clauses = Vec::new();
    for p in 0..pigeons {
        clauses.push((0..holes).map(|h| Lit::pos(v(p, h))).collect());
    }
    for h in 0..holes {
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                clauses.push(vec![Lit::neg(v(p1, h)), Lit::neg(v(p2, h))]);
            }
        }
    }
    ((pigeons * holes) as usize, clauses)
}

#[test]
fn restarts_fire_on_a_hard_unsat_without_changing_the_verdict() {
    // Pigeonhole 6→5 is unsatisfiable and needs well over RESTART_UNIT
    // conflicts, so at least one restart must fire — and the verdict must
    // still be exactly Unsat (a restart only reorders the search).
    let (n, clauses) = pigeonhole(6, 5);
    let mut s = Solver::new(n, clauses);
    assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
    assert!(s.restarts > 0, "expected a restart, got {}", s.restarts);
}

#[test]
fn clause_deletion_fires_without_changing_the_verdict() {
    // Pigeonhole 6→5 learns enough clauses to cross the reduction threshold, so
    // at least one database reduction must run — and the verdict must still be
    // exactly Unsat. Deleting learnt clauses may only forgo pruning, never a
    // model nor an original clause.
    let (n, clauses) = pigeonhole(6, 5);
    let mut s = Solver::new(n, clauses);
    assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
    assert!(s.reductions > 0, "expected a reduction, got {}", s.reductions);
}

#[test]
fn learned_clause_never_loses_a_model() {
    // A satisfiable instance that drives several conflicts before a model is
    // found; the learnt clauses must not prune the (only) solution.
    // (a∨b)(¬a∨c)(¬b∨c)(¬c∨d)(a∨¬d∨e) with a forced route.
    let clauses = vec![
        vec![Lit::pos(0), Lit::pos(1)],
        vec![Lit::neg(0), Lit::pos(2)],
        vec![Lit::neg(1), Lit::pos(2)],
        vec![Lit::neg(2), Lit::pos(3)],
        vec![Lit::pos(0), Lit::neg(3), Lit::pos(4)],
    ];
    let mut s = Solver::new(5, clauses.clone());
    match s.solve(DEFAULT_BUDGET) {
        SatResult::Sat(m) => assert!(check_model(&clauses, &m)),
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn conflict_at_level_zero_after_learning_is_unsat() {
    // Forces a learnt unit that then propagates into a top-level conflict.
    // (x∨y)(x∨¬y)(¬x∨z)(¬x∨¬z) ⇒ x must be false (first two) and true
    // (last two, once y/z resolved) — unsatisfiable via learning.
    let clauses = vec![
        vec![Lit::pos(0), Lit::pos(1)],
        vec![Lit::pos(0), Lit::neg(1)],
        vec![Lit::neg(0), Lit::pos(2)],
        vec![Lit::neg(0), Lit::neg(2)],
    ];
    let mut s = Solver::new(3, clauses);
    assert_eq!(s.solve(DEFAULT_BUDGET), SatResult::Unsat);
}

#[test]
fn budget_zero_on_open_problem_is_unknown() {
    // A problem needing at least one decision, with budget 0 ⇒ Unknown.
    let clauses = vec![vec![Lit::pos(0), Lit::pos(1)]];
    let mut s = Solver::new(2, clauses);
    assert_eq!(s.solve(0), SatResult::Unknown);
}

/// Brute-force oracle: is `clauses` satisfiable over `n` variables?
fn brute_force_sat(n: u32, clauses: &[Vec<Lit>]) -> bool {
    (0u32..(1u32 << n)).any(|mask| {
        let model: Vec<bool> = (0..n).map(|v| mask & (1 << v) != 0).collect();
        check_model(clauses, &model)
    })
}

#[test]
fn cdcl_agrees_with_brute_force_under_forced_restarts_and_reductions() {
    // The plain fuzz below never triggers restarts or DB reductions (tiny
    // instances solve in < RESTART_UNIT conflicts), leaving the two paths where
    // a bug could fabricate a false Unsat untested. Here we force both to fire
    // constantly (restart almost every conflict, keep almost no learnt clauses)
    // and still demand exact agreement with the exhaustive oracle.
    let mut state: u64 = 0x1234_5678_9abc_def0;
    let mut rng = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut total_reductions = 0u64;
    let mut total_restarts = 0u64;
    for _ in 0..500 {
        // Deeper trees (10..=13 vars) so learnt clauses reach LBD > 2 and are
        // actually deletable — tiny instances only ever make glue (LBD ≤ 2).
        let n: u32 = 10 + (rng() % 4) as u32; // 10..=13 vars (≤8192 brute force)
        // Proper hard random 3-SAT near the phase transition (ratio ≈ 4.3):
        // exactly three distinct variables per clause, which actually forces
        // deep search, conflicts, restarts and LBD>2 learnt clauses.
        let m = (n as usize * 43) / 10 + (rng() % 5) as usize;
        let clauses: Vec<Vec<Lit>> = (0..m)
            .map(|_| {
                let mut vars = [0u32; 3];
                let mut count = 0;
                while count < 3 {
                    let cand = (rng() % n as u64) as u32;
                    if !vars[..count].contains(&cand) {
                        vars[count] = cand;
                        count += 1;
                    }
                }
                vars.iter()
                    .map(|&var| if rng() & 1 == 0 { Lit::pos(var) } else { Lit::neg(var) })
                    .collect()
            })
            .collect();
        let oracle = brute_force_sat(n, &clauses);
        let mut s = Solver::new(n as usize, clauses.clone());
        s.restart_unit = 2; // restart frequently
        s.max_learnt = 3; // reduce the learnt DB aggressively
        match s.solve(DEFAULT_BUDGET) {
            SatResult::Sat(model) => {
                assert!(oracle, "SAT but oracle says UNSAT: {clauses:?}");
                assert!(check_model(&clauses, &model), "invalid model: {clauses:?} / {model:?}");
            }
            SatResult::Unsat => {
                assert!(!oracle, "false refutation under restart/reduce: {clauses:?}");
            }
            SatResult::Unknown => panic!("tiny instance hit the budget: {clauses:?}"),
        }
        total_reductions += s.reductions;
        total_restarts += s.restarts;
    }
    // Prove the stressed paths were actually exercised.
    assert!(total_restarts > 0, "no restarts fired");
    assert!(total_reductions > 0, "no reductions fired");
}

#[test]
fn cdcl_agrees_with_brute_force_on_random_instances() {
    // The decisive "nothing is lost" guard: over many random small 3-CNFs,
    // CDCL's verdict must match an exhaustive truth-table oracle exactly —
    // in particular it must NEVER report Unsat on a satisfiable instance
    // (a false refutation) nor Sat with an invalid model.
    let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut rng = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..4000 {
        let n: u32 = 3 + (rng() % 4) as u32; // 3..=6 vars
        let m = 1 + (rng() % 14) as usize; // 1..=14 clauses
        let clauses: Vec<Vec<Lit>> = (0..m)
            .map(|_| {
                let k = 1 + (rng() % 3) as usize; // 1..=3 literals
                (0..k)
                    .map(|_| {
                        let var = (rng() % n as u64) as u32;
                        if rng() & 1 == 0 { Lit::pos(var) } else { Lit::neg(var) }
                    })
                    .collect()
            })
            .collect();

        let oracle = brute_force_sat(n, &clauses);
        let mut s = Solver::new(n as usize, clauses.clone());
        match s.solve(DEFAULT_BUDGET) {
            SatResult::Sat(model) => {
                assert!(oracle, "CDCL said SAT but oracle says UNSAT: {clauses:?}");
                assert!(
                    check_model(&clauses, &model),
                    "CDCL returned an invalid model: {clauses:?} / {model:?}"
                );
            }
            SatResult::Unsat => {
                assert!(!oracle, "CDCL falsely refuted a satisfiable instance: {clauses:?}");
            }
            SatResult::Unknown => panic!("small instance hit the budget: {clauses:?}"),
        }
    }
}
