//! Lockset-based data-race detection (G1) — the Eraser algorithm over whole-program facts.
//!
//! Each function contributes, per access to a **shareable** memory location (a global, or an
//! object reached through a parameter — see `csolver_symbolic`), the location's stable
//! *class*, whether the access is a write, and the set of lock *classes* held at the access
//! (its lockset). Across the whole program these form the Eraser candidate-lockset relation:
//!
//! * the **candidate lockset** of a location is the intersection of the locksets of *all* its
//!   accesses — the locks that consistently protect it;
//! * a location whose candidate lockset is **empty** (no lock protects every access), that has
//!   **≥1 write**, is touched by **≥2 functions** (a cross-thread proxy), and is protected by
//!   a lock on **some** access (evidence it is meant to be guarded) is a **candidate race**.
//!
//! This is a bug-finding heuristic (the classic Eraser false-positive profile — it does not
//! model thread-creation happens-before, RCU, per-CPU data, or `atomic`/`READ_ONCE` accesses
//! that are race-free by construction), reported as a *candidate*, never a soundness verdict.
//! A full symbolic interleaving / weak-memory product (a genuine second timeline) remains the
//! larger open frontier; this is the tractable lockset realisation the taxonomy recommends.

use std::collections::{BTreeSet, HashMap};

/// One candidate data race: the shared location and the functions that access it under an
/// inconsistent lockset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataRace {
    /// The shared location's access class (a global symbol or a struct-field class).
    pub location: String,
    /// The functions that access the location (sorted, de-duplicated).
    pub functions: Vec<String>,
    /// An **IRQ-context race** (G9): the location is protected against interrupts
    /// (`spin_lock_irqsave`, the synthetic `@irqoff` lock) on some access but not all — a plain
    /// `spin_lock` on IRQ-shared data lets an interrupt handler race.
    pub irq_unsafe: bool,
}

/// The synthetic lock class marking an IRQ-disabled access (see the executor). Consistent IRQ
/// protection intersects to it; a plain-locked access to the same location lacks it.
const IRQOFF: &str = "@irqoff";

/// One observed shared-memory access, tagged with the function it occurred in.
pub struct TaggedAccess<'a> {
    /// The function the access is in.
    pub function: &'a str,
    /// The shared location's access class.
    pub location: &'a str,
    /// Whether the access is a write.
    pub write: bool,
    /// The lock classes held at the access (its lockset).
    pub lockset: &'a [String],
}

/// Detect all candidate data races in the program's shared-access records, most-accessed
/// first. One [`DataRace`] per location whose lockset is inconsistent (Eraser signal).
///
/// **Happens-before pruning.** A data race needs two accesses that can run *concurrently*. When
/// `concurrent` is `Some(set)` — the sound closed-world set of functions reachable from an attacker
/// entry or a spawned thread — an access in a function outside it is dropped before the lockset is
/// folded: a `module_init`/setup helper that touches a location unlocked, sequentially before any
/// runtime handler can run, then neither empties the candidate lockset nor counts toward the
/// ≥2-function proxy (the dominant Eraser false positive). Sound over-approximation: a genuinely
/// concurrent function is always in the set, so pruning never hides a real race. `None` ⇒ every
/// access participates (the heuristic default, e.g. a single-module run with no call graph).
pub fn detect_races(
    accesses: &[TaggedAccess],
    concurrent: Option<&std::collections::HashSet<String>>,
) -> Vec<DataRace> {
    // Per location: the running candidate lockset (intersection), whether any access wrote,
    // whether any access held a lock, and the set of functions touching it.
    struct Loc {
        candidate: Option<BTreeSet<String>>, // None = no access folded yet
        has_write: bool,
        any_locked: bool,
        irq_in_union: bool, // some access held @irqoff (the location is IRQ-relevant)
        functions: BTreeSet<String>,
    }
    let mut locs: HashMap<&str, Loc> = HashMap::new();
    for a in accesses {
        // Happens-before pruning: only an access that can run concurrently participates.
        if concurrent.is_some_and(|set| !set.contains(a.function)) {
            continue;
        }
        let ls: BTreeSet<String> = a.lockset.iter().cloned().collect();
        let loc = locs.entry(a.location).or_insert_with(|| Loc {
            candidate: None,
            has_write: false,
            any_locked: false,
            irq_in_union: false,
            functions: BTreeSet::new(),
        });
        loc.candidate = Some(match loc.candidate.take() {
            None => ls.clone(),
            Some(cur) => cur.intersection(&ls).cloned().collect(),
        });
        loc.has_write |= a.write;
        loc.any_locked |= !ls.is_empty();
        loc.irq_in_union |= ls.contains(IRQOFF);
        loc.functions.insert(a.function.to_string());
    }

    let mut races: Vec<DataRace> = locs
        .into_iter()
        .filter_map(|(location, loc)| {
            let candidate = loc.candidate.unwrap_or_default();
            let candidate_empty = candidate.is_empty();
            // Standard Eraser race: no lock protects every access.
            let eraser = candidate_empty && loc.any_locked;
            // IRQ-context race (G9): the location is IRQ-protected somewhere (@irqoff in the
            // union) but not on every access (@irqoff not in the intersection) — a plain lock on
            // IRQ-shared data. Fires even when a *real* lock is shared by all accesses.
            let irq_unsafe = loc.irq_in_union && !candidate.contains(IRQOFF);
            // Cross-thread proxy. Without the concurrency oracle, require ≥2 distinct functions (a
            // single function's mixed locking in a single-threaded program is not a race). WITH the
            // oracle every surviving function is reachable from a **re-entrant** entry (a syscall /
            // ops-handler runs on many CPUs at once), so a *single* such function that accesses the
            // location under an inconsistent lockset races with a **concurrent instance of itself**
            // — the same-entry re-entrancy race the ≥2 proxy misses. So ≥1 suffices there.
            let min_fns = if concurrent.is_some() { 1 } else { 2 };
            let is_race = (eraser || irq_unsafe) && loc.has_write && loc.functions.len() >= min_fns;
            is_race.then(|| DataRace {
                location: location.to_string(),
                functions: loc.functions.into_iter().collect(),
                irq_unsafe: irq_unsafe && !eraser,
            })
        })
        .collect();
    // Stable order: most functions first, then by location name.
    races.sort_by(|a, b| {
        b.functions.len().cmp(&a.functions.len()).then_with(|| a.location.cmp(&b.location))
    });
    races
}

#[cfg(test)]
mod tests {
    use super::*;

    fn acc<'a>(f: &'a str, loc: &'a str, w: bool, ls: &'a [String]) -> TaggedAccess<'a> {
        TaggedAccess { function: f, location: loc, write: w, lockset: ls }
    }

    #[test]
    fn inconsistent_lock_is_a_race() {
        let l = vec!["g:lk@0".to_string()];
        // writer holds the lock; reader in another function holds nothing → empty candidate.
        let accesses = vec![
            acc("writer", "g:counter@0", true, &l),
            acc("reader", "g:counter@0", false, &[]),
        ];
        let races = detect_races(&accesses, None);
        assert_eq!(races.len(), 1, "an unlocked access to an otherwise-locked shared write is a race");
        assert_eq!(races[0].location, "g:counter@0");
        assert_eq!(races[0].functions, vec!["reader".to_string(), "writer".to_string()]);
    }

    #[test]
    fn irq_unsafe_access_is_a_race_even_with_a_shared_lock() {
        // Both access under the same real lock, but the IRQ side adds @irqoff and the process
        // side does not → IRQ-unsafe (a plain spin_lock on IRQ-shared data).
        let irq = vec!["g:lk@0".to_string(), "@irqoff".to_string()];
        let proc = vec!["g:lk@0".to_string()];
        let accesses = vec![
            acc("irq_handler", "g:shared@0", true, &irq),
            acc("process_ctx", "g:shared@0", false, &proc),
        ];
        let races = detect_races(&accesses, None);
        assert_eq!(races.len(), 1, "inconsistent IRQ protection is a race despite a shared lock");
        assert!(races[0].irq_unsafe, "flagged as IRQ-unsafe");
        // Consistent irqsave on both sides → no race.
        let ok = vec![acc("a", "g:s@0", true, &irq), acc("b", "g:s@0", false, &irq)];
        assert!(detect_races(&ok, None).is_empty(), "consistent irqsave is safe");
    }

    #[test]
    fn consistent_lock_is_not_a_race() {
        let l = vec!["g:lk@0".to_string()];
        let accesses = vec![
            acc("writer", "g:counter@0", true, &l),
            acc("reader", "g:counter@0", false, &l),
        ];
        assert!(detect_races(&accesses, None).is_empty(), "a consistently-locked location is not a race");
    }

    #[test]
    fn single_function_is_not_flagged() {
        // Only one function touches it — no cross-thread proxy, even with mixed locking.
        let l = vec!["g:lk@0".to_string()];
        let accesses = vec![
            acc("only", "g:x@0", true, &l),
            acc("only", "g:x@0", false, &[]),
        ];
        assert!(detect_races(&accesses, None).is_empty(), "a single-function location is not flagged");
    }

    #[test]
    fn non_concurrent_access_is_pruned_by_happens_before() {
        use std::collections::HashSet;
        let l = vec!["g:lk@0".to_string()];
        // A runtime handler writes the counter under a lock; `module_init` writes it unlocked.
        // Without concurrency info this is the classic Eraser false positive (empty candidate).
        let accesses = vec![
            acc("handler", "g:counter@0", true, &l),
            acc("module_init", "g:counter@0", true, &[]),
        ];
        assert_eq!(detect_races(&accesses, None).len(), 1, "no oracle → the init access is a false race");
        // With the concurrency oracle: only `handler` runs concurrently; `module_init` happens
        // before it, so its unlocked access neither empties the lockset nor forms a cross-thread
        // pair → no race. Sound FP removal.
        let concurrent: HashSet<String> = ["handler".to_string()].into_iter().collect();
        assert!(
            detect_races(&accesses, Some(&concurrent)).is_empty(),
            "init happens-before the runtime handler → not a concurrent race",
        );
        // But two genuinely-concurrent handlers with inconsistent locking still race.
        let two = vec![
            acc("handler", "g:counter@0", true, &l),
            acc("worker", "g:counter@0", false, &[]),
        ];
        let both: HashSet<String> = ["handler".to_string(), "worker".to_string()].into_iter().collect();
        assert_eq!(
            detect_races(&two, Some(&both)).len(),
            1,
            "two concurrent functions with inconsistent locking still race",
        );
    }

    #[test]
    fn single_reentrant_function_races_with_itself() {
        use std::collections::HashSet;
        let l = vec!["g:lk@0".to_string()];
        // One syscall handler writes g:counter under a lock on one path and unlocked on another —
        // two concurrent invocations (the same handler on two CPUs) race on the unlocked path.
        let accesses = vec![
            acc("sys_write", "g:counter@0", true, &l),
            acc("sys_write", "g:counter@0", true, &[]),
        ];
        // Without the oracle we cannot confirm re-entrancy → not flagged (≥2 functions).
        assert!(detect_races(&accesses, None).is_empty(), "no oracle → a single function is not a race");
        // With the oracle, sys_write is a concurrent (re-entrant) entry → self-race candidate.
        let conc: HashSet<String> = ["sys_write".to_string()].into_iter().collect();
        assert_eq!(
            detect_races(&accesses, Some(&conc)).len(),
            1,
            "a re-entrant entry with inconsistent locking races with a concurrent instance of itself",
        );
    }

    #[test]
    fn never_locked_read_only_is_not_flagged() {
        // Never locked and no write → not the Eraser signal (likely intentional lockless read).
        let accesses = vec![
            acc("a", "g:ro@0", false, &[]),
            acc("b", "g:ro@0", false, &[]),
        ];
        assert!(detect_races(&accesses, None).is_empty(), "a never-locked read-only location is not flagged");
    }
}
