//! External, per-API **memory-effect contracts**.
//!
//! CSolver recognizes a handful of library/kernel APIs — allocators, deallocators,
//! user-copy helpers, and (in the future) crypto/scatterlist primitives — whose memory
//! effects it cannot recover from a single translation unit (the body is elsewhere, or
//! opaque). Historically those APIs were a **hardcoded** match in the LLVM frontend.
//!
//! This crate replaces that with a small, declarative contract language kept in
//! *separate files, one block per API family*. A contract is written **once per API**
//! and states the API's memory effects abstractly (what it allocates / frees / writes /
//! reads, and with what byte length). The frontend then lowers any recognized call from
//! its contract instead of a baked-in table, and users can add coverage for a new API by
//! writing another block — no code change.
//!
//! The default contracts (see `data/*.contract`) are compiled in via [`include_str!`], so
//! the binary stays self-contained; [`Contracts::load_dir`] layers user-supplied files on
//! top for private/proprietary APIs.
//!
//! # File format
//!
//! ```text
//! # comments start with '#'
//! [kmalloc __kmalloc vmalloc]      # one block, shared by all listed names
//! alloc size=arg0 align=16         # result is a fresh region of arg0 bytes
//!
//! [copy_from_user _copy_from_user]
//! write arg0 len=arg2 fill=user    # bulk-writes arg2 bytes of untrusted data to arg0
//! ```
//!
//! Effects: `alloc size=<size> align=<int>`, `free arg<k>`,
//! `write arg<k> len=<size> [fill=user|undef]`, `read arg<k> len=<size>`.
//! A `<size>` is `arg<k>`, `arg<k>*arg<j>`, or a decimal integer (a byte count).
//!
//! The contract language is deliberately *sound-preserving*: it can only describe effects
//! the executor already models faithfully. It says nothing about a function's return
//! value semantics beyond "this call was recognized"; the frontend decides how to bind the
//! result (an allocation's result is the fresh pointer, everything else is opaque).

use std::collections::{HashMap, HashSet};
use std::path::Path;

/// A byte-length expression referring to a call's arguments (0-based) or a constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SizeExpr {
    /// The value of argument `k`, in bytes.
    Arg(usize),
    /// The product `arg_a * arg_b` (an element count times an element size).
    Product(usize, usize),
    /// A fixed byte count.
    Const(u64),
}

/// How a bulk write initializes the destination bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Fill {
    /// Ordinary bytes (their value is unknown but not attacker-tainted).
    Undef,
    /// Untrusted **user data** (`copy_from_user`): a value later read back from the
    /// written region is a genuine adversarial input and may drive a refutation.
    User,
}

/// Where a bulk read's bytes are disclosed to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ReadSink {
    /// An ordinary in-kernel read (only the in-bounds obligation applies).
    #[default]
    Internal,
    /// The bytes are copied out to **userspace** (`copy_to_user`): reading
    /// never-written source bytes is a kernel information leak (`NoInfoLeak`).
    User,
}

/// One abstract memory effect of an API call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Effect {
    /// Allocates a fresh region of `size` bytes with the given alignment; the call's
    /// result value **is** the pointer to it.
    Alloc {
        /// The allocation's byte size.
        size: SizeExpr,
        /// The guaranteed alignment of the returned pointer, in bytes.
        align: u32,
        /// `true` for an **externally-backed** mapping (`ioremap` MMIO): the region is
        /// live and of known size like an allocation, but its bytes are *already
        /// initialized* by the device/hardware, so a register read is not an
        /// uninitialized-read bug. A plain allocator is `false` (its bytes are fresh).
        external: bool,
    },
    /// Frees the region pointed to by argument `ptr`.
    Free {
        /// The 0-based index of the argument holding the freed pointer.
        ptr: usize,
    },
    /// Bulk-writes `len` bytes to the region pointed to by argument `ptr`.
    Write {
        /// The 0-based index of the argument holding the written pointer.
        ptr: usize,
        /// How many bytes are written.
        len: SizeExpr,
        /// How the written bytes are initialized (ordinary vs. untrusted user data).
        fill: Fill,
        /// For a `fill=user` copy, the 0-based argument index of the USER source pointer
        /// (`from=arg<k>`), so the executor can detect a **double-fetch** (two reads of the
        /// same user address). `None` for a plain fill or when unspecified.
        from: Option<usize>,
    },
    /// Bulk-reads `len` bytes from the region pointed to by argument `ptr`.
    Read {
        /// The 0-based index of the argument holding the read pointer.
        ptr: usize,
        /// How many bytes are read.
        len: SizeExpr,
        /// Where the read bytes go (in-kernel vs. disclosed to userspace).
        sink: ReadSink,
    },
    /// Attaches a **provenance label** to the region pointed to by argument `ptr`. The
    /// label's granted capabilities are declared by a `prov` line (see [`Contracts`]).
    /// The archetype: a splice-inserted page enters a scatterlist labelled `foreign`.
    Label {
        /// The 0-based index of the argument whose region is labelled.
        ptr: usize,
        /// The provenance label name.
        label: String,
    },
    /// Requires that the region pointed to by argument `ptr` **grants** the named
    /// capability. Refuted (a capability violation) when the region's provenance label
    /// provably does not grant it — e.g. a `foreign` page used where `write` is required
    /// (the Copy-Fail write-to-a-read-only-page shape).
    Require {
        /// The 0-based index of the argument whose region must grant the capability.
        ptr: usize,
        /// The required capability name (matched against the label's `grants` set).
        cap: String,
    },
    /// **Propagates provenance**: the region at argument `dst` absorbs the provenance
    /// labels of the region at argument `src` (their union). Models a container taking in
    /// an element — `sg_set_page(sgl, page)`, a DMA buffer, an io_uring fixed buffer — so a
    /// `foreign` element makes the whole container only as writable as its least-writable
    /// member. General (not scatterlist-specific): any add-element / taint-transfer API.
    Propagate {
        /// The 0-based index of the argument whose region absorbs the labels.
        dst: usize,
        /// The 0-based index of the argument whose labels are absorbed.
        src: usize,
    },
    /// **Conditional capability**: *iff* arguments `a` and `b` point into the **same**
    /// region (an in-place operation, `src == dst`), that region must grant `cap`. The
    /// precise signature of the Copy-Fail write-to-a-read-only-page: an in-place crypto op
    /// (`aead_request_set_crypt(req, src, dst)` with `src == dst`) writing a `foreign` page.
    /// When `a` and `b` are *distinct* regions (the out-of-place / patched path) it does not
    /// fire — so the gate distinguishes the vulnerable in-place reuse from the safe copy,
    /// and never false-FAILs the patched code.
    RequireIfAlias {
        /// The 0-based index of the first argument (e.g. the crypto source).
        a: usize,
        /// The 0-based index of the second argument (e.g. the crypto destination).
        b: usize,
        /// The capability the aliased region must grant.
        cap: String,
    },
    /// **Conditional capability on two FIELDS of an object** — the inlined-request form of
    /// [`Effect::RequireIfAlias`]. At a call `op(req, …)`, the pointers stored at byte offsets
    /// `off_a` and `off_b` of the object `arg` are read back (via read-your-writes over the
    /// prior field stores) and, *iff* they alias the same region, that region must grant `cap`.
    /// This catches the Copy-Fail in-place write when the crypto API is `static inline`: the
    /// real optimized kernel has no `aead_request_set_crypt` call — `req->src` and `req->dst`
    /// are set by field stores, so the check must read them back from the request at the
    /// `crypto_aead_encrypt(req)` sink. General: any operation on a descriptor with in-place
    /// src/dst pointer fields.
    RequireIfAliasFields {
        /// The 0-based argument holding the object (e.g. the crypto request).
        arg: usize,
        /// Byte offset of the first pointer field (e.g. the request's `src`).
        off_a: u64,
        /// Byte offset of the second pointer field (e.g. the request's `dst`).
        off_b: u64,
        /// The capability the aliased field region must grant.
        cap: String,
    },
    /// **Entry seed** (whole-object cross-syscall provenance): applied not at a *call* to
    /// this API but at the **entry of the named function itself** — parameter `arg`'s object
    /// is labelled `label`. Models the fact that an object shared across syscalls (a socket)
    /// may carry provenance a *sibling* operation left on it: e.g. `_aead_recvmsg`'s socket
    /// may hold a `foreign` page spliced in by `af_alg_sendpage` in another syscall. Only the
    /// **in-place** sink (`require-if-alias`) then fires, so seeding never false-FAILs the
    /// out-of-place (patched) path.
    Seed {
        /// The 0-based parameter index to label at the function's entry.
        arg: usize,
        /// The provenance label name.
        label: String,
    },
    /// **Taint source**: argument `arg` (and its result value) becomes tainted with `label`
    /// — an untrusted input (`recv`/`argv`/a syscall scalar). Taint then flows through
    /// arithmetic, loads and calls to a [`Effect::TaintSink`]. (A bulk `copy_from_user`
    /// buffer is already a taint source via its `fill=user` region — this is for a scalar or
    /// return-value source the bulk-write effect does not cover.)
    TaintSource {
        /// The 0-based argument index whose value becomes tainted (`ret` for the result).
        arg: usize,
        /// The taint label name.
        label: String,
    },
    /// **Taint sink**: argument `arg` must **not** be tainted with `label`. A tainted value
    /// reaching it (a `user`-tainted `printf` format string, `memcpy` length, loop bound,
    /// `exec` arg) is refuted (`TaintedSink`). An untainted / sanitised value passes.
    TaintSink {
        /// The 0-based argument index that must be free of the taint label.
        arg: usize,
        /// The taint label the argument must not carry.
        label: String,
    },
    /// **Taint sanitiser**: clears `label` from argument `arg` (and its result) — a
    /// recognised validation/escape/clamp (`snprintf`-bounded, `min()`, a bounds check).
    TaintSanitize {
        /// The 0-based argument index whose taint is cleared (`ret` for the result).
        arg: usize,
        /// The taint label cleared.
        label: String,
    },
    /// **Typestate transition** (the generalised protocol tracker): the call moves the
    /// resource identified by argument `arg` into `state` within `protocol` — `close(f)`
    /// → `file.closed`, `verify(obj)` → `perm.checked`. Unconditional (the new state
    /// replaces any prior state for that protocol).
    TypestateSet {
        /// The 0-based argument index naming the resource (`ret` for the result handle).
        arg: usize,
        /// The protocol name (e.g. `file`, `perm`).
        protocol: String,
        /// The state the resource enters (e.g. `closed`, `checked`).
        state: String,
    },
    /// **Typestate obligation**: the call requires the resource at argument `arg` to be
    /// (`negate=false`) or **not** be (`negate=true`) in `state` within `protocol`. A
    /// violation (`TypestateViolation`) when the resource is definitely in the forbidden
    /// state — a `read` of a `file.closed` handle (`require-not`), a privileged op on a
    /// resource not `perm.checked` (`require`).
    TypestateRequire {
        /// The 0-based argument index naming the resource.
        arg: usize,
        /// The protocol name.
        protocol: String,
        /// The required (or forbidden) state.
        state: String,
        /// When `true`, the resource must **not** be in `state`; when `false`, it must be.
        negate: bool,
    },
    /// **Protocol-wide yield** (TOCTOU G2): a call that yields (a blocking call, a second
    /// syscall entry, dropping a lock) transitions *every* resource of `protocol` currently
    /// in state `from` to state `to` — e.g. `schedule()` moves every `file.checked` to
    /// `file.stale`, so a subsequent use of a stale check is a time-of-check-to-time-of-use
    /// race. Not tied to an argument (it affects all resources of the protocol).
    TypestateYield {
        /// The protocol whose resources are transitioned.
        protocol: String,
        /// The state a resource must be in to be affected.
        from: String,
        /// The state such resources move to.
        to: String,
    },
    /// **Reference-count increment / decrement** (G8): the call raises (`inc`) or lowers
    /// (`dec`) the refcount of the resource at argument `arg` within `protocol`. A `dec`
    /// that takes the count **below zero** is an underflow (a premature free → UAF). `inc`
    /// is `false`, `dec` is `true` in [`Effect::Refcount::dec`].
    Refcount {
        /// The 0-based argument index naming the counted resource.
        arg: usize,
        /// The refcount protocol name (e.g. `kref`).
        protocol: String,
        /// `true` for a decrement (`put`), `false` for an increment (`get`).
        dec: bool,
        /// For an increment, whether it is a **checked** get (`refcount-inc-checked`, the
        /// `*_not_zero` / `*_unless_zero` variants) that cannot resurrect a zeroed object, so it
        /// does not race a concurrent final `put`. Ignored for a decrement.
        checked: bool,
    },
    /// **Memory barrier** (weak-memory, subsystem 4): the call is a memory barrier —
    /// `kind` 0 = full (`smp_mb`, orders W→R), 1 = write (`smp_wmb`, orders W→W), 2 = read
    /// (`smp_rmb`, orders R→R). Recorded in the interleaving trace so the operational
    /// weak-memory model drains the store buffers accordingly.
    Barrier {
        /// 0 = full (`smp_mb`), 1 = write (`smp_wmb`), 2 = read (`smp_rmb`).
        kind: u8,
        /// `Some(arg)` when the call also **accesses** the location at that argument (a
        /// `smp_store_release`/`smp_load_acquire`: `kind` picks write vs. read). `None` for a
        /// standalone fence (`smp_mb`/`smp_wmb`/`smp_rmb`), which orders but touches no location.
        access: Option<usize>,
    },
    /// **Thread spawn** (weak-memory / happens-before, subsystem 4): the call creates a thread
    /// running the function named by argument `arg` (a function pointer — `pthread_create`'s
    /// start routine, `kthread_run`'s threadfn). A happens-before edge: the child sees the
    /// parent's prior writes and cannot run before this point.
    Spawn {
        /// The 0-based argument index holding the child's function pointer.
        arg: usize,
    },
    /// **Thread join** (happens-before): the call waits for the threads this thread spawned to
    /// finish (`pthread_join`/`kthread_stop`), so the parent's later accesses happen after them.
    Join,
    /// **Compare-and-swap** on argument `arg` (`cmpxchg`/`atomic_cmpxchg`/`try_cmpxchg`) — a
    /// lock-free update whose success only checks the value. If another thread modifies the same
    /// location concurrently (A→B→A), the CAS can succeed on a stale premise: the **ABA problem**.
    Cas {
        /// The 0-based argument index of the CAS location pointer.
        arg: usize,
    },
    /// **Leak-state declaration** (K): a resource left in `state` of `protocol` at a function
    /// **return** (without being released or escaping via the return value) is a resource
    /// leak. Not applied at a call — it registers `(protocol, state)` as a leak state checked
    /// at every return.
    TypestateLeak {
        /// The protocol whose lingering state is a leak.
        protocol: String,
        /// The state that, if still held at return, is a leak.
        state: String,
    },
    /// **Unconditional lock acquisition** on the lock at argument `arg`. Drives the AA
    /// self-deadlock check, the lockset race pass and the ABBA lock-order edges. Only for
    /// primitives that *always* take the lock — a `*_trylock` may fail and must not carry
    /// this effect. Releases need no effect: the executor drops any held lock's base handed
    /// to a subsequent call (which soundly covers matched unlocks and unlock wrappers).
    /// `spin=true` marks a **spinning** acquire that enters atomic context (preemption off),
    /// so a later [`Effect::Blocking`] call while it is held is a sleep-in-atomic deadlock;
    /// a `mutex`/semaphore acquire sleeps itself and is *not* spin.
    LockAcquire {
        /// The 0-based argument index of the lock pointer.
        arg: usize,
        /// Whether the acquire spins (enters atomic / preemption-off context).
        spin: bool,
    },
    /// The call **may sleep** (block): illegal in atomic context (a held spinning lock).
    Blocking,
    /// **Disables IRQs** (or soft-IRQs) — code after it runs protected against an interrupt
    /// handler on the same CPU, modelled as holding a synthetic `@irqoff` lock.
    IrqDisable,
    /// **Re-enables IRQs** — leaves the `@irqoff` protection of [`Effect::IrqDisable`].
    IrqEnable,
    /// Enters an **RCU read-side critical section**: shared reads inside it are race-free by
    /// the RCU contract, so the data-race pass excludes them.
    RcuReadLock,
    /// Leaves an RCU read-side critical section.
    RcuReadUnlock,
    /// The call returns a pointer to **per-CPU** data — thread-local by construction, so
    /// accesses through the result are excluded from the data-race pass.
    PercpuPtr,
    /// A **cross-syscall container lookup**: the result is an object fetched from the
    /// persistent container at argument `arg` (idr/xarray/radix-tree), so a free/use of it
    /// in two independent syscall entries composes on the same root.
    ContainerLookup {
        /// The 0-based argument index of the container.
        arg: usize,
    },
    /// A lookup rooted at a **synthetic global** (`fget`'s `current->files` file table):
    /// the call has no container argument, so its result is named after `root` — a
    /// persistent shared root across syscalls.
    GlobalLookup {
        /// The synthetic global root name (e.g. `@files`).
        root: String,
    },
}

/// A contract for one API family: the set of names it applies to, and its effects.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ApiContract {
    /// The function names this contract applies to.
    pub names: Vec<String>,
    /// The API's memory effects, applied in order at each recognized call.
    pub effects: Vec<Effect>,
}

impl ApiContract {
    /// The single allocation effect, if this contract allocates (the frontend binds the
    /// call result to the fresh pointer).
    pub fn alloc(&self) -> Option<(&SizeExpr, u32)> {
        self.effects.iter().find_map(|e| match e {
            Effect::Alloc { size, align, .. } => Some((size, *align)),
            _ => None,
        })
    }
}

/// A registry of API contracts, indexed by function name, plus the **provenance
/// lattice**: which capabilities each provenance label grants. An *unlabelled* region
/// grants **every** capability (the sound default — a `Require` only fails when a label
/// explicitly withholds the capability), so the whole mechanism is opt-in and cannot
/// introduce a false FAIL on code that names no labels.
#[derive(Debug, Default, Clone)]
pub struct Contracts {
    by_name: HashMap<String, usize>,
    contracts: Vec<ApiContract>,
    grants: HashMap<String, HashSet<String>>,
}

impl Contracts {
    /// The compiled-in default contracts (allocators, deallocators, user-copies).
    pub fn defaults() -> Contracts {
        let mut c = Contracts::default();
        for (src, text) in DEFAULT_FILES {
            // A malformed *built-in* file is a build-time bug: fail loudly.
            c.parse_str(text, src)
                .unwrap_or_else(|e| panic!("built-in contract file {src}: {e}"));
        }
        c
    }

    /// Load every `*.contract` file under `dir` and layer them on top of `self`
    /// (a later block for the same name overrides an earlier one). For user-supplied
    /// API coverage via `--contracts <dir>`.
    pub fn load_dir(&mut self, dir: &Path) -> Result<(), String> {
        let mut files: Vec<_> = std::fs::read_dir(dir)
            .map_err(|e| format!("{}: {e}", dir.display()))?
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().and_then(|x| x.to_str()) == Some("contract"))
            .collect();
        files.sort();
        for path in files {
            let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
            self.parse_str(&text, &path.display().to_string())?;
        }
        Ok(())
    }

    /// The contract for `name`, if any.
    pub fn lookup(&self, name: &str) -> Option<&ApiContract> {
        self.by_name.get(name).map(|&i| &self.contracts[i])
    }

    /// Whether a region labelled `label` grants capability `cap`. An unknown/unlabelled
    /// label grants everything (the sound default).
    pub fn grants(&self, label: &str, cap: &str) -> bool {
        match self.grants.get(label) {
            Some(set) => set.contains(cap),
            None => true,
        }
    }

    /// The provenance lattice (label → granted capabilities), for consumers that intern
    /// it (e.g. the frontend attaching it to the module).
    pub fn lattice(&self) -> &HashMap<String, HashSet<String>> {
        &self.grants
    }

    /// Iterate every registered contract block (to collect the label/capability names its
    /// `label`/`require` effects mention, e.g. for interning).
    pub fn iter(&self) -> std::slice::Iter<'_, ApiContract> {
        self.contracts.iter()
    }

    /// Number of registered contract blocks (one per API family).
    pub fn len(&self) -> usize {
        self.contracts.len()
    }

    /// Whether no contracts are registered.
    pub fn is_empty(&self) -> bool {
        self.contracts.is_empty()
    }

    /// Parse one contract file's `text` (named `src` for diagnostics) into `self`.
    pub fn parse_str(&mut self, text: &str, src: &str) -> Result<(), String> {
        let mut pending: Option<ApiContract> = None;
        for (lineno, raw) in text.lines().enumerate() {
            let line = strip_comment(raw).trim();
            if line.is_empty() {
                continue;
            }
            let at = || format!("{src}:{}", lineno + 1);
            // A top-level provenance declaration: `prov <label> grants=<c1,c2,...>`.
            if let Some(decl) = line.strip_prefix("prov ") {
                self.flush(pending.take());
                let words: Vec<&str> = decl.split_whitespace().collect();
                let label = words
                    .first()
                    .filter(|w| !w.contains('='))
                    .ok_or_else(|| format!("{}: `prov` needs a label name", at()))?;
                let caps = kv(&words, "grants")
                    .ok_or_else(|| format!("{}: `prov` needs `grants=...`", at()))?;
                let set = caps
                    .split(',')
                    .filter(|c| !c.is_empty())
                    .map(str::to_string)
                    .collect();
                self.grants.insert(label.to_string(), set);
                continue;
            }
            if let Some(inner) = line.strip_prefix('[') {
                // A new block header flushes the previous block.
                self.flush(pending.take());
                let inner = inner
                    .strip_suffix(']')
                    .ok_or_else(|| format!("{}: header missing closing ']'", at()))?;
                let names: Vec<String> = inner.split_whitespace().map(str::to_string).collect();
                if names.is_empty() {
                    return Err(format!("{}: empty API name list", at()));
                }
                pending = Some(ApiContract { names, effects: Vec::new() });
            } else {
                let contract = pending
                    .as_mut()
                    .ok_or_else(|| format!("{}: effect before any [names] header", at()))?;
                let effect = parse_effect(line).map_err(|e| format!("{}: {e}", at()))?;
                contract.effects.push(effect);
            }
        }
        self.flush(pending.take());
        Ok(())
    }

    fn flush(&mut self, block: Option<ApiContract>) {
        let Some(block) = block else { return };
        let idx = self.contracts.len();
        for name in &block.names {
            self.by_name.insert(name.clone(), idx);
        }
        self.contracts.push(block);
    }
}

/// Drop a `#` comment (anything from the first `#` to end of line).
fn strip_comment(line: &str) -> &str {
    match line.find('#') {
        Some(i) => &line[..i],
        None => line,
    }
}

mod parse;
pub use parse::RET_ARG;
pub(crate) use parse::*;

/// The compiled-in default contracts, as a process-global (built once). The single source of
/// truth for the frontend, the executor, and the interner — so provenance label ids agree.
pub fn contracts() -> &'static Contracts {
    static CONTRACTS: std::sync::OnceLock<Contracts> = std::sync::OnceLock::new();
    CONTRACTS.get_or_init(Contracts::defaults)
}

/// Interns provenance label and capability names (a shared namespace) to stable `u32` ids, and
/// precomputes the id-keyed grant relation. `ProvLabel`/`CapRequire` instructions and
/// `Module::prov_grants` speak in these ids; a consumer (the executor) resolves a label name to
/// its id here so both sides agree. Built once from [`contracts`] (deterministic: names sorted
/// before assigning ids).
pub struct ProvInterner {
    ids: HashMap<String, u32>,
    grants: HashMap<u32, HashSet<u32>>,
}

impl ProvInterner {
    /// The id of a provenance label/capability name, or `None` if no contract mentions it.
    pub fn id(&self, name: &str) -> Option<u32> {
        self.ids.get(name).copied()
    }

    /// The id-keyed grant relation (label id → capability ids it confers).
    pub fn grants(&self) -> &HashMap<u32, HashSet<u32>> {
        &self.grants
    }
}

/// The process-global provenance interner (see [`ProvInterner`]).
pub fn prov_interner() -> &'static ProvInterner {
    static INTERNER: std::sync::OnceLock<ProvInterner> = std::sync::OnceLock::new();
    INTERNER.get_or_init(|| {
        let c = contracts();
        // Every label/capability name: the lattice keys (labels) and values (capabilities),
        // plus any name a `label`/`require`/taint/typestate/refcount effect mentions.
        let mut names: Vec<&str> = Vec::new();
        for (label, caps) in c.lattice() {
            names.push(label);
            names.extend(caps.iter().map(String::as_str));
        }
        for contract in c.iter() {
            for effect in &contract.effects {
                match effect {
                    Effect::Label { label, .. } => names.push(label),
                    Effect::Require { cap, .. } => names.push(cap),
                    Effect::TaintSource { label, .. }
                    | Effect::TaintSink { label, .. }
                    | Effect::TaintSanitize { label, .. } => names.push(label),
                    Effect::TypestateSet { protocol, state, .. }
                    | Effect::TypestateRequire { protocol, state, .. }
                    | Effect::TypestateLeak { protocol, state } => {
                        names.push(protocol);
                        names.push(state);
                    }
                    Effect::TypestateYield { protocol, from, to } => {
                        names.push(protocol);
                        names.push(from);
                        names.push(to);
                    }
                    Effect::Refcount { protocol, .. } => names.push(protocol),
                    Effect::Seed { label, .. } => names.push(label),
                    _ => {}
                }
            }
        }
        names.sort_unstable();
        names.dedup();
        let ids: HashMap<String, u32> =
            names.iter().enumerate().map(|(i, n)| (n.to_string(), i as u32)).collect();
        let grants = c
            .lattice()
            .iter()
            .filter_map(|(label, caps)| {
                let lid = *ids.get(label)?;
                let cset = caps.iter().filter_map(|c| ids.get(c).copied()).collect();
                Some((lid, cset))
            })
            .collect();
        ProvInterner { ids, grants }
    })
}

/// The built-in contract files, embedded so the binary is self-contained.
const DEFAULT_FILES: &[(&str, &str)] = &[
    ("alloc.contract", include_str!("../data/alloc.contract")),
    ("mmio.contract", include_str!("../data/mmio.contract")),
    ("free.contract", include_str!("../data/free.contract")),
    ("user_copy.contract", include_str!("../data/user_copy.contract")),
    ("provenance.contract", include_str!("../data/provenance.contract")),
    ("taint.contract", include_str!("../data/taint.contract")),
    ("typestate.contract", include_str!("../data/typestate.contract")),
    ("barrier.contract", include_str!("../data/barrier.contract")),
    ("thread.contract", include_str!("../data/thread.contract")),
    ("lifetime.contract", include_str!("../data/lifetime.contract")),
    ("rcu.contract", include_str!("../data/rcu.contract")),
    ("kernel_sync.contract", include_str!("../data/kernel_sync.contract")),
];

#[cfg(test)]
#[path = "contracts_tests.rs"]
mod tests;
