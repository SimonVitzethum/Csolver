/// **Unconditional** lock-acquiring kernel primitives (by argument-0 = the lock).
/// Re-acquiring one already held on a path is an AA self-deadlock
/// (`SafetyProperty::DataRace`). Only primitives that *always* take the lock are
/// listed — `*_trylock` may fail, so it is deliberately excluded (adding it would
/// false-flag a `trylock`-then-`lock` retry). A *release* needs no list: any call
/// handed a held lock's base drops it (see `check_lock_call`), which covers matched
/// unlocks (incl. `spin_unlock_irqrestore`), unlock wrappers, and callees that unlock.
pub(crate) const LOCK_ACQUIRE: &[&str] = &[
    "spin_lock", "_raw_spin_lock", "spin_lock_irq", "spin_lock_bh", "spin_lock_irqsave",
    "_raw_spin_lock_irq", "_raw_spin_lock_bh", "_raw_spin_lock_irqsave",
    "raw_spin_lock", "raw_spin_lock_irq", "raw_spin_lock_irqsave", "raw_spin_lock_bh",
    "mutex_lock", "mutex_lock_nested", "mutex_lock_interruptible", "mutex_lock_killable",
    "read_lock", "write_lock", "read_lock_irq", "write_lock_irq",
    "read_lock_irqsave", "write_lock_irqsave", "read_lock_bh", "write_lock_bh",
    "_raw_read_lock", "_raw_write_lock", "down", "down_write", "down_read",
    "down_interruptible", "down_killable", "down_write_killable",
    // Seqlock write side: `write_seqlock` excludes other writers exactly like a spinlock (the
    // read side is lock-free and retried, so only writers take a lock). A missing unlock, a
    // double `write_seqlock` (AA), or an ABBA against another lock is then caught for free.
    "write_seqlock", "write_seqlock_irq", "write_seqlock_bh", "write_seqlock_irqsave",
    "raw_write_seqlock", "__write_seqlock",
    // Userspace POSIX threads: the lock is arg0 exactly as in the kernel model, so lockset
    // race detection, AA self-deadlock and ABBA lock-order all work on pthread code. `*_trylock`
    // is excluded (it may fail). Unlocks need no list (a call handed a held lock's base drops it).
    "pthread_mutex_lock", "pthread_mutex_timedlock",
    "pthread_rwlock_rdlock", "pthread_rwlock_wrlock", "pthread_rwlock_timedrdlock",
    "pthread_rwlock_timedwrlock", "pthread_spin_lock",
];

/// **Spinning** lock acquisitions — those that enter **atomic context** (preemption off),
/// so a subsequent sleeping call deadlocks. Spinlocks and rwlocks spin; `mutex`/`down`
/// (semaphore) may themselves sleep and are NOT atomic context (they are blocking calls).
pub(crate) const SPIN_ACQUIRE: &[&str] = &[
    "spin_lock", "_raw_spin_lock", "spin_lock_irq", "spin_lock_bh", "spin_lock_irqsave",
    "_raw_spin_lock_irq", "_raw_spin_lock_bh", "_raw_spin_lock_irqsave",
    "raw_spin_lock", "raw_spin_lock_irq", "raw_spin_lock_irqsave", "raw_spin_lock_bh",
    "read_lock", "write_lock", "read_lock_irq", "write_lock_irq",
    "read_lock_irqsave", "write_lock_irqsave", "read_lock_bh", "write_lock_bh",
    "_raw_read_lock", "_raw_write_lock",
    "write_seqlock", "write_seqlock_irq", "write_seqlock_bh", "write_seqlock_irqsave",
    "raw_write_seqlock", "__write_seqlock",
    // A userspace `pthread_spin_lock` spins (busy-wait) exactly like a kernel spinlock — holding
    // it across a blocking call is the same anti-pattern. `pthread_mutex`/`rwlock` block/sleep and
    // are NOT atomic context, so they stay out of this list (as `mutex_lock`/`down` do).
    "pthread_spin_lock",
];

/// RCU read-side critical-section entry/exit. A shared **read** inside an RCU read-side section
/// is race-free by the RCU contract (the updater publishes atomically and defers reclamation),
/// so the data-race pass excludes it — a major false-positive reducer for RCU-heavy code.
pub(crate) const RCU_READ_LOCK: &[&str] = &[
    "rcu_read_lock", "rcu_read_lock_bh", "rcu_read_lock_sched", "srcu_read_lock",
    "rcu_read_lock_trace", "rcu_read_lock_any_held",
];
pub(crate) const RCU_READ_UNLOCK: &[&str] = &[
    "rcu_read_unlock", "rcu_read_unlock_bh", "rcu_read_unlock_sched", "srcu_read_unlock",
    "rcu_read_unlock_trace",
];

/// Calls that **disable IRQs** (or soft-IRQs) — an access made while IRQs are off is protected
/// against an interrupt handler on the same CPU, modelled as holding a synthetic `@irqoff` lock.
/// A location accessed *irqsave* in one place and under a plain `spin_lock` in another is an
/// IRQ-context race (G9) the data-race pass then flags via the missing `@irqoff`.
pub(crate) const IRQ_DISABLE: &[&str] = &[
    "spin_lock_irqsave", "spin_lock_irq", "_raw_spin_lock_irqsave", "_raw_spin_lock_irq",
    "raw_spin_lock_irqsave", "raw_spin_lock_irq", "read_lock_irqsave", "write_lock_irqsave",
    "read_lock_irq", "write_lock_irq", "local_irq_save", "local_irq_disable",
    "local_bh_disable", "spin_lock_bh", "_raw_spin_lock_bh", "raw_spin_lock_bh",
    "write_seqlock_irqsave", "write_seqlock_irq",
];
pub(crate) const IRQ_ENABLE: &[&str] = &[
    "spin_unlock_irqrestore", "spin_unlock_irq", "_raw_spin_unlock_irqrestore",
    "_raw_spin_unlock_irq", "raw_spin_unlock_irqrestore", "raw_spin_unlock_irq",
    "read_unlock_irqrestore", "write_unlock_irqrestore", "read_unlock_irq", "write_unlock_irq",
    "local_irq_restore", "local_irq_enable", "local_bh_enable", "spin_unlock_bh",
    "_raw_spin_unlock_bh", "raw_spin_unlock_bh",
    "write_sequnlock_irqrestore", "write_sequnlock_irq",
];

/// Accessors returning a pointer to **per-CPU** data — thread-local by construction (each CPU
/// has its own instance, accessed with preemption disabled), so accesses through the result are
/// not shared races. The data-race pass excludes them.
pub(crate) const PERCPU_ACCESSOR: &[&str] = &[
    "this_cpu_ptr", "per_cpu_ptr", "raw_cpu_ptr", "get_cpu_ptr", "get_cpu_var",
    "__this_cpu_ptr", "this_cpu_read", "alloc_percpu", "__alloc_percpu",
];

// A spinning-lock **release** (`spin_unlock`/…) leaves atomic context. It is not a named
// set here: like any other call it is handed the lock base as a pointer argument, and the
// general call arm below already drops every passed base from `spin_held` (and `locks_held`).

/// Calls that **may sleep** (block): illegal while a spinlock is held (atomic context).
/// The unambiguous always-may-sleep primitives — a `mutex`/semaphore acquire, an explicit
/// yield/sleep, a completion/RCU wait, or the kernel's own `might_sleep` marker. (GFP-flag-
/// conditional allocators like `kmalloc(GFP_KERNEL)` need flag analysis and are not here.)
pub(crate) const BLOCKING: &[&str] = &[
    "mutex_lock", "mutex_lock_nested", "mutex_lock_interruptible", "mutex_lock_killable",
    "down", "down_write", "down_read", "down_interruptible", "down_killable",
    "down_write_killable", "down_timeout", "schedule", "schedule_timeout",
    "schedule_timeout_interruptible", "schedule_timeout_uninterruptible", "io_schedule",
    "msleep", "msleep_interruptible", "ssleep", "usleep_range", "might_sleep",
    "___might_sleep", "__might_sleep", "wait_for_completion", "wait_for_completion_interruptible",
    "wait_for_completion_killable", "wait_for_completion_timeout", "synchronize_rcu",
    "synchronize_srcu", "synchronize_net", "synchronize_irq", "flush_work",
    "flush_workqueue", "cond_resched",
];
