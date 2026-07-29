//! The verifier's result types.

use csolver_core::{Assumption, ObligationResult, ProofObligation, Verdict};

/// One obligation paired with the result of trying to discharge it.
#[derive(Debug, Clone)]
pub struct ObligationOutcome {
    /// The obligation.
    pub obligation: ProofObligation,
    /// Its discharge result.
    pub result: ObligationResult,
}

impl ObligationOutcome {
    /// The verdict this single obligation contributes.
    pub fn verdict(&self) -> Verdict {
        self.result.verdict()
    }
}

/// The verification result for one function.
#[derive(Debug, Clone)]
pub struct FunctionReport {
    /// The function name.
    pub function: String,
    /// The rolled-up verdict over all its obligations.
    pub verdict: Verdict,
    /// Per-obligation outcomes.
    pub outcomes: Vec<ObligationOutcome>,
    /// Whether symbolic exploration was **truncated at its budget** (visit or
    /// wall-clock) for this function — so its `Unknown` obligations are a
    /// resource limit, not genuine undecidability. Lets a scan *defer* a
    /// budget-limited unit for a full-effort re-run instead of accepting Unknown.
    pub truncated: bool,
    /// **Lock-order edges** observed in this function: `(held-class, acquired-class)`
    /// pairs (see `csolver_symbolic::lockclass`). Aggregated across the program to detect
    /// ABBA lock-order cycles (an A→B here plus a B→A elsewhere is a potential deadlock).
    pub lock_edges: Vec<(String, String)>,
    /// **Shared-memory access records**: `(access-class, is_write, lock-classes held)` per
    /// access to a shareable location. Aggregated program-wide for the lockset data-race check.
    pub race_accesses: Vec<(String, bool, Vec<String>)>,
    /// **Ordered event trace** `(kind, class)` (0=acquire,1=release,2=read,3=write) for the
    /// two-thread interleaving atomicity check.
    pub race_trace: Vec<(u8, String)>,
}

impl FunctionReport {
    /// Count outcomes with the given verdict.
    pub fn count(&self, verdict: Verdict) -> usize {
        self.outcomes
            .iter()
            .filter(|o| o.verdict() == verdict)
            .count()
    }

    /// **Assumption footprint** (Phase 0d): the ids of every named assumption this function's
    /// proofs rest on, sorted and deduplicated. Empty ⇒ the function is decided **strictly
    /// soundly**, with no opt-in assumption in the chain.
    ///
    /// Deliberately collected over **all** of the function's obligations, not only over the ones
    /// carrying its verdict. A `Fail` is witnessed by a `Refuted` counterexample, which holds no
    /// assumption record of its own — but the symbolic state that counterexample was found in may
    /// have been *shaped* by one (`param-valid` is what materialises a parameter's region in the
    /// first place). Attributing the whole function is therefore the conservative reading: it can
    /// only move a function out of the sound bucket, never into it.
    pub fn assumption_footprint(&self) -> Vec<String> {
        let mut ids: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
        for o in &self.outcomes {
            if let csolver_core::ObligationResult::Proven(tree) = &o.result {
                ids.extend(tree.assumptions.iter().map(String::as_str));
            }
        }
        ids.into_iter().map(str::to_string).collect()
    }

    /// Whether this function is **decided strictly soundly**: a `Pass`/`Fail` verdict with an
    /// empty [`assumption_footprint`](Self::assumption_footprint). An `Unknown` is never
    /// sound-decided — it is not decided at all.
    pub fn is_sound_decided(&self) -> bool {
        self.verdict != Verdict::Unknown && self.assumption_footprint().is_empty()
    }
}

#[cfg(test)]
mod footprint_tests {
    use super::{FunctionReport, ObligationOutcome};
    use csolver_core::proof::{Justification, ProofStep, ProofTree};
    use csolver_core::{Location, ObligationId, ObligationResult, ProofObligation, SafetyProperty, Verdict};

    fn proven(assumptions: &[&str]) -> ObligationResult {
        let step = ProofStep {
            conclusion: "c".to_string(),
            justification: Justification::Axiom { name: "test".to_string() },
            premises: Vec::new(),
        };
        ObligationResult::Proven(
            ProofTree::new(step).with_assumptions(assumptions.iter().map(|s| (*s).to_string()).collect()),
        )
    }

    fn func(verdict: Verdict, results: Vec<ObligationResult>) -> FunctionReport {
        let outcomes = results
            .into_iter()
            .map(|result| ObligationOutcome {
                obligation: ProofObligation::new(
                    ObligationId(0),
                    SafetyProperty::InBounds,
                    Location::level_only(csolver_core::SourceLevel::Llvm),
                    "p",
                ),
                result,
            })
            .collect();
        FunctionReport {
            function: "f".to_string(),
            verdict,
            outcomes,
            truncated: false,
            lock_edges: Vec::new(),
            race_accesses: Vec::new(),
            race_trace: Vec::new(),
        }
    }

    #[test]
    fn a_proof_with_no_assumption_is_sound_decided() {
        let f = func(Verdict::Pass, vec![proven(&[])]);
        assert!(f.assumption_footprint().is_empty());
        assert!(f.is_sound_decided());
    }

    #[test]
    fn the_footprint_is_deduplicated_and_sorted() {
        let f = func(
            Verdict::Pass,
            vec![proven(&["param-valid", "alloc-succeeds"]), proven(&["param-valid"])],
        );
        assert_eq!(f.assumption_footprint(), vec!["alloc-succeeds", "param-valid"]);
        assert!(!f.is_sound_decided(), "an assumption in the chain rules out the sound bucket");
    }

    /// An UNKNOWN is not decided at all, so it can never be sound-decided — even though its
    /// (absent) footprint is empty, which is the trap a naive `footprint.is_empty()` would fall into.
    #[test]
    fn an_undecided_function_is_never_sound_decided() {
        let open = ObligationResult::Open { residual: Vec::new(), suggested: Vec::new() };
        let f = func(Verdict::Unknown, vec![open]);
        assert!(f.assumption_footprint().is_empty());
        assert!(!f.is_sound_decided());
    }

    /// A FAIL is witnessed by a `Refuted`, which carries no assumption of its own — but the state
    /// the witness was found in may have been shaped by one, so the whole function is attributed.
    #[test]
    fn a_fail_inherits_the_assumptions_of_its_other_obligations() {
        let refuted = ObligationResult::Refuted(csolver_core::CounterExample::new(
            "oob",
            csolver_core::Model { assignments: Vec::new() },
        ));
        let f = func(Verdict::Fail, vec![refuted, proven(&["param-valid"])]);
        assert_eq!(f.assumption_footprint(), vec!["param-valid"]);
        assert!(!f.is_sound_decided(), "a FAIL found under an assumption is not sound-decided");
    }
}

/// The verification result for a whole module.
#[derive(Debug, Clone)]
pub struct ModuleReport {
    /// The module name.
    pub module: String,
    /// The rolled-up verdict over all functions.
    pub verdict: Verdict,
    /// Per-function reports.
    pub functions: Vec<FunctionReport>,
    /// Assumptions the proofs in this module depend on.
    pub assumptions: Vec<Assumption>,
}

impl ModuleReport {
    /// Total obligations with the given verdict across the module.
    pub fn count(&self, verdict: Verdict) -> usize {
        self.functions.iter().map(|f| f.count(verdict)).sum()
    }

    /// Whether any function's symbolic exploration was truncated at its budget.
    pub fn any_truncated(&self) -> bool {
        self.functions.iter().any(|f| f.truncated)
    }

    /// ABBA lock-order cycles among this module's functions (bug-finding). Aggregates
    /// every function's lock-order edges and reports the strongly-connected cycles. For
    /// whole-program detection across files, aggregate `lock_edges` from every module's
    /// functions and call [`crate::detect_cycles`] directly.
    pub fn lock_order_cycles(&self) -> Vec<crate::LockOrderCycle> {
        let edges: Vec<crate::TaggedEdge> = self
            .functions
            .iter()
            .flat_map(|f| {
                f.lock_edges.iter().map(move |(from, to)| crate::TaggedEdge {
                    function: f.function.as_str(),
                    from,
                    to,
                })
            })
            .collect();
        crate::detect_cycles(&edges)
    }

    /// Candidate data races (lockset / Eraser, bug-finding) among this module's functions.
    /// Aggregates every function's shared-access records and flags locations with an
    /// inconsistent lockset. For whole-program detection, aggregate `race_accesses` from every
    /// module's functions and call [`crate::detect_races`] directly.
    pub fn data_races(&self) -> Vec<crate::DataRace> {
        let accesses: Vec<crate::TaggedAccess> = self
            .functions
            .iter()
            .flat_map(|f| {
                f.race_accesses.iter().map(move |(location, write, lockset)| crate::TaggedAccess {
                    function: f.function.as_str(),
                    location,
                    write: *write,
                    lockset,
                })
            })
            .collect();
        // Single-module report: no whole-program call graph, so no concurrency oracle — every
        // access participates (the whole-program scan supplies the concurrent-function set).
        crate::detect_races(&accesses, None)
    }

    /// Candidate **atomicity violations** among this module's functions (the two-thread
    /// interleaving product, subsystem 4): a split-critical-section read-modify-write one
    /// function performs, which another function's write can interrupt in a valid interleaving.
    /// Complements the lockset pass — it finds lost updates where every access is *consistently*
    /// locked (so Eraser sees no race) but the RMW spans two critical sections.
    pub fn atomicity_violations(&self) -> Vec<crate::AtomicityWitness> {
        let threads: Vec<crate::Thread> = self
            .functions
            .iter()
            .filter(|f| !f.race_trace.is_empty())
            .map(|f| crate::trace_to_thread(&f.function, &f.race_trace))
            .collect();
        crate::find_atomicity_violations(&threads)
    }

    /// Candidate **store-buffer / missing-barrier** weak-memory bugs among this module's
    /// functions (subsystem 4): two functions each writing one shared location then reading the
    /// other's, with no barrier between — the store-buffer litmus (SC-impossible, weak-memory
    /// possible).
    pub fn store_buffer_bugs(&self) -> Vec<crate::interleave::StoreBufferWitness> {
        let threads: Vec<crate::Thread> = self
            .functions
            .iter()
            .filter(|f| !f.race_trace.is_empty())
            .map(|f| crate::trace_to_thread(&f.function, &f.race_trace))
            .collect();
        crate::interleave::store_buffer_violations(&threads)
    }

    /// Candidate **cross-thread use-after-free / double-free** among this module's functions: a
    /// free in one thread concurrent (disjoint lockset) with an access or free of the same
    /// object in another. Reuses the interleaving traces (`Free` events).
    pub fn cross_thread_uaf(&self) -> Vec<crate::FreeUseWitness> {
        let threads: Vec<crate::Thread> = self
            .functions
            .iter()
            .filter(|f| !f.race_trace.is_empty())
            .map(|f| crate::trace_to_thread(&f.function, &f.race_trace))
            .collect();
        crate::find_cross_thread_uaf(&threads)
    }

    /// Candidate **ABA problems** among this module's functions: a compare-and-swap of a location
    /// concurrent (disjoint lockset) with a modification of the same location in another thread.
    pub fn aba_bugs(&self) -> Vec<crate::AbaWitness> {
        let threads: Vec<crate::Thread> = self
            .functions
            .iter()
            .filter(|f| !f.race_trace.is_empty())
            .map(|f| crate::trace_to_thread(&f.function, &f.race_trace))
            .collect();
        crate::find_aba(&threads)
    }

    /// Candidate **concurrent reference-count races** among this module's functions: an unchecked
    /// get of an object in one thread concurrent (disjoint lockset) with a put of the same object in
    /// another — the get can resurrect a zeroed count (UAF). A checked `*_not_zero` get never fires.
    pub fn refcount_races(&self) -> Vec<crate::interleave::RefcountRaceWitness> {
        let threads: Vec<crate::Thread> = self
            .functions
            .iter()
            .filter(|f| !f.race_trace.is_empty())
            .map(|f| crate::trace_to_thread(&f.function, &f.race_trace))
            .collect();
        crate::interleave::find_refcount_races(&threads)
    }

    /// Candidate **cross-entry (cross-syscall) use-after-free / double-free**: an object freed via
    /// a shared global root in one entry and dereferenced (or freed again) in another, independently
    /// reachable entry — the `ioctl`→`close`→`read` pattern across *separate* syscall entries with
    /// no common caller. `is_entry` selects the attacker-reachable entries (e.g. `matches_entry`
    /// against the configured patterns); pass `|_| true` to consider every function. The search
    /// only ever fires on global-rooted (persistent) state, so a parameter-passed object never does.
    pub fn cross_entry_uaf(
        &self,
        is_entry: impl Fn(&str) -> bool,
    ) -> Vec<crate::interleave::CrossEntryWitness> {
        let threads: Vec<crate::Thread> = self
            .functions
            .iter()
            .filter(|f| is_entry(&f.function) && !f.race_trace.is_empty())
            .map(|f| crate::trace_to_thread(&f.function, &f.race_trace))
            .collect();
        crate::interleave::find_cross_entry_uaf(&threads)
    }

    /// Candidate **cross-entry (cross-syscall) typestate violations**: an object driven into a
    /// forbidden protocol state (`closed`/`freed`) via a shared global root in one entry and used
    /// (with a `require-not` of that state) in another, independently reachable entry — the
    /// use-after-close/free analogue of [`Self::cross_entry_uaf`] across separate syscalls.
    pub fn cross_entry_typestate(
        &self,
        is_entry: impl Fn(&str) -> bool,
    ) -> Vec<crate::interleave::CrossEntryTypestateWitness> {
        let threads: Vec<crate::Thread> = self
            .functions
            .iter()
            .filter(|f| is_entry(&f.function) && !f.race_trace.is_empty())
            .map(|f| crate::trace_to_thread(&f.function, &f.race_trace))
            .collect();
        crate::interleave::find_cross_entry_typestate(&threads)
    }

    /// Candidate **weak-memory (SC-robustness) bugs** among this module's functions (subsystem
    /// 4, full operational model): a pair of functions whose concurrent execution under the PSO
    /// store-buffer model can observe a read outcome no sequentially-consistent execution allows
    /// — a missing barrier. Subsumes the store-buffer *and* message-passing (`smp_wmb`) litmus.
    pub fn weak_memory_bugs(&self) -> Vec<crate::interleave::WeakMemoryWitness> {
        let threads: Vec<crate::Thread> = self
            .functions
            .iter()
            .filter(|f| !f.race_trace.is_empty())
            .map(|f| crate::trace_to_thread(&f.function, &f.race_trace))
            .collect();
        crate::interleave::find_weak_memory_bugs(&threads)
    }
}
