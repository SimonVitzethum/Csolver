//! Pre-solve **synchronisation-classification collector**.
//!
//! The executor's concurrency checks (AA self-deadlock, sleep-in-atomic, IRQ-context
//! races, RCU read-section exclusion, per-CPU exclusion, cross-syscall lookup naming)
//! need to recognise the kernel/POSIX primitives by name at each opaque call. Those
//! names used to be hardcoded `const` tables in the executor; they now live in the
//! contract files (`crates/contracts/data/kernel_sync.contract` et al.) as
//! `lock-acquire`/`blocking`/`irq-*`/`rcu-read-*`/`percpu-ptr`/`*-lookup` effects.
//!
//! Before solving, [`SyncClasses::collect`] runs once over the loaded contracts and
//! builds the name-indexed classification the executor then consults per call — so
//! covering a new primitive is a contract line, not a code change. [`classes`] is the
//! process-wide table over the built-in defaults (mirroring the frontend's global
//! contract registry); [`install`] lets an embedder layer user contract files on top
//! **before** the first query.

use csolver_contracts::{Contracts, Effect};
use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;

/// The per-acquire lock classification a `lock-acquire` effect declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LockSpec {
    /// The 0-based argument index of the lock pointer.
    pub arg: usize,
    /// Whether the acquire spins (enters atomic / preemption-off context).
    pub spin: bool,
}

/// Name-indexed synchronisation classification, collected from the contracts before
/// solving. All queries are by the callee's symbol name.
#[derive(Debug, Default, Clone)]
pub struct SyncClasses {
    lock_acquire: HashMap<String, LockSpec>,
    blocking: HashSet<String>,
    irq_disable: HashSet<String>,
    irq_enable: HashSet<String>,
    rcu_read_lock: HashSet<String>,
    rcu_read_unlock: HashSet<String>,
    percpu: HashSet<String>,
    container_lookup: HashMap<String, usize>,
    global_lookup: HashMap<String, String>,
}

impl SyncClasses {
    /// Collect every synchronisation effect from `contracts` into the name-indexed
    /// table. Names carrying no sync effect are simply absent (every query is `false`
    /// / `None` for them — the sound default: an unknown call is opaque, not a lock).
    pub fn collect(contracts: &Contracts) -> SyncClasses {
        let mut t = SyncClasses::default();
        for c in contracts.iter() {
            for effect in &c.effects {
                let names = c.names.iter().cloned();
                match effect {
                    Effect::LockAcquire { arg, spin } => {
                        for n in names {
                            t.lock_acquire.insert(n, LockSpec { arg: *arg, spin: *spin });
                        }
                    }
                    Effect::Blocking => t.blocking.extend(names),
                    Effect::IrqDisable => t.irq_disable.extend(names),
                    Effect::IrqEnable => t.irq_enable.extend(names),
                    Effect::RcuReadLock => t.rcu_read_lock.extend(names),
                    Effect::RcuReadUnlock => t.rcu_read_unlock.extend(names),
                    Effect::PercpuPtr => t.percpu.extend(names),
                    Effect::ContainerLookup { arg } => {
                        for n in names {
                            t.container_lookup.insert(n, *arg);
                        }
                    }
                    Effect::GlobalLookup { root } => {
                        for n in names {
                            t.global_lookup.insert(n, root.clone());
                        }
                    }
                    _ => {}
                }
            }
        }
        t
    }

    /// The lock specification of an unconditional lock-acquire call, if `name` is one.
    pub fn lock_acquire(&self, name: &str) -> Option<LockSpec> {
        self.lock_acquire.get(name).copied()
    }

    /// Whether `name` may sleep (illegal while a spinning lock is held).
    pub fn blocking(&self, name: &str) -> bool {
        self.blocking.contains(name)
    }

    /// Whether `name` disables IRQs / soft-IRQs.
    pub fn irq_disable(&self, name: &str) -> bool {
        self.irq_disable.contains(name)
    }

    /// Whether `name` re-enables IRQs / soft-IRQs.
    pub fn irq_enable(&self, name: &str) -> bool {
        self.irq_enable.contains(name)
    }

    /// Whether `name` enters an RCU read-side critical section.
    pub fn rcu_read_lock(&self, name: &str) -> bool {
        self.rcu_read_lock.contains(name)
    }

    /// Whether `name` leaves an RCU read-side critical section.
    pub fn rcu_read_unlock(&self, name: &str) -> bool {
        self.rcu_read_unlock.contains(name)
    }

    /// Whether `name` returns a pointer to per-CPU (thread-local) data.
    pub fn percpu(&self, name: &str) -> bool {
        self.percpu.contains(name)
    }

    /// The container-argument index of a cross-syscall container lookup, if `name` is one.
    pub fn container_lookup(&self, name: &str) -> Option<usize> {
        self.container_lookup.get(name).copied()
    }

    /// The synthetic global root a lookup's result is named after, if `name` is one.
    pub fn global_lookup(&self, name: &str) -> Option<&str> {
        self.global_lookup.get(name).map(String::as_str)
    }
}

static CLASSES: OnceLock<SyncClasses> = OnceLock::new();

/// The process-wide classification table: the built-in default contracts unless
/// [`install`] provided a layered registry first.
pub fn classes() -> &'static SyncClasses {
    CLASSES.get_or_init(|| SyncClasses::collect(&Contracts::defaults()))
}

/// Install the classification collected from `contracts` (defaults plus user files) as
/// the process-wide table. Must run **before** the first [`classes`] query; returns
/// `false` (and changes nothing) if the table was already initialised.
pub fn install(contracts: &Contracts) -> bool {
    CLASSES.set(SyncClasses::collect(contracts)).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The default table reproduces the executor's former hardcoded classification.
    #[test]
    fn default_classification() {
        let t = classes();
        // Spinning lock, no IRQ effect.
        assert_eq!(t.lock_acquire("spin_lock"), Some(LockSpec { arg: 0, spin: true }));
        assert!(!t.irq_disable("spin_lock"));
        // Spinning lock that disables IRQs.
        assert_eq!(t.lock_acquire("spin_lock_irqsave"), Some(LockSpec { arg: 0, spin: true }));
        assert!(t.irq_disable("spin_lock_irqsave"));
        // Plain raw_spin_lock spins but does NOT disable IRQs.
        assert_eq!(t.lock_acquire("raw_spin_lock"), Some(LockSpec { arg: 0, spin: true }));
        assert!(!t.irq_disable("raw_spin_lock"));
        // Sleeping locks: acquire + blocking, not spin.
        assert_eq!(t.lock_acquire("mutex_lock"), Some(LockSpec { arg: 0, spin: false }));
        assert!(t.blocking("mutex_lock"));
        assert_eq!(t.lock_acquire("down_write"), Some(LockSpec { arg: 0, spin: false }));
        // pthread: spin vs. sleeping.
        assert_eq!(t.lock_acquire("pthread_spin_lock").map(|s| s.spin), Some(true));
        assert_eq!(t.lock_acquire("pthread_mutex_lock").map(|s| s.spin), Some(false));
        assert!(!t.blocking("pthread_mutex_lock"));
        // Trylock stays unclassified (may fail — no unconditional acquire).
        assert_eq!(t.lock_acquire("mutex_trylock"), None);
        assert_eq!(t.lock_acquire("spin_trylock"), None);
        // Blocking-only primitives.
        assert!(t.blocking("schedule"));
        assert!(t.blocking("might_sleep"));
        assert!(t.blocking("synchronize_rcu"));
        assert!(t.lock_acquire("schedule").is_none());
        // IRQ enable/disable without a lock.
        assert!(t.irq_disable("local_irq_save"));
        assert!(t.irq_enable("local_irq_restore"));
        assert!(t.irq_enable("spin_unlock_irqrestore"));
        // RCU read sections.
        assert!(t.rcu_read_lock("rcu_read_lock"));
        assert!(t.rcu_read_unlock("srcu_read_unlock"));
        // Per-CPU accessors.
        assert!(t.percpu("this_cpu_ptr"));
        // Container / file-table lookups.
        assert_eq!(t.container_lookup("idr_find"), Some(0));
        assert_eq!(t.global_lookup("fget"), Some("@files"));
        // An unknown name matches nothing (the sound default).
        assert!(t.lock_acquire("my_helper").is_none());
        assert!(!t.blocking("my_helper"));
    }
}
