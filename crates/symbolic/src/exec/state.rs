use super::*;

/// Where a loaded value comes from, per the store log (most-recent-first scan).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LoadOrigin {
    /// A prior store definitely determines the value (`Must` alias).
    Stored,
    /// A prior store *might* determine it (`May` alias) — value is unknown.
    Uncertain,
    /// No store reaches this location (every record is `No` alias): the bytes
    /// are whatever the region held at allocation. For a freshly-allocated
    /// region that is *uninitialized* memory.
    Unwritten,
}

/// A recorded store: "`size` bytes equal to `value` were written through
/// `target`". Most-recent-last.
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct StoreRecord {
    pub(crate) target: SymPointer,
    pub(crate) value: SymValue,
    pub(crate) size: u64,
}

#[derive(Clone)]
pub(crate) struct PathState {
    pub(crate) env: FxHashMap<RegId, SymValue>,
    pub(crate) regions: Vec<SymRegion>,
    pub(crate) pathcond: Vec<ExprId>,
    pub(crate) facts: Vec<ExprId>,
    /// The symbolic store, in program order (for read-your-writes).
    pub(crate) heap: Vec<StoreRecord>,
    /// **Read-consistency** cache for *unwritten* locations: the value first materialized
    /// for a load from `(region, concrete byte offset, access width)` that no store aliases,
    /// so two reads of the same never-written field agree (the correct memory semantics —
    /// unwritten memory holds one fixed unknown value). Populated only for concrete offsets;
    /// consulted only in `load_value`'s unwritten fallback (a store always wins first).
    /// Cleared on every heap havoc (an opaque call may have written the location), so it can
    /// never return a stale post-write value — sound.
    pub(crate) unwritten_reads: FxHashMap<(usize, u128, u32), SymValue>,
    /// **Materialised-field region identity**: the region a `RefWitness` materialised for a
    /// raw-pointer field at `(base region, concrete offset)`, so two loads of the *same* field
    /// yield the *same* tracked region (an in-place `src == dst` through field loads is then
    /// recognised). Keyed by the base's identity — a materialised region or an opaque
    /// provenance id — and the field offset. Cleared on every heap havoc (a call may have
    /// reassigned the field) — sound.
    pub(crate) ref_regions: FxHashMap<(RefBase, u128), usize>,
    /// Provenance labels attached to an **opaque pointer** by its provenance identity
    /// (`Prov::Unknown`'s id — see there), which flows through `gep`/copy so a field address
    /// off a labelled object carries the object's labels. A raw-pointer parameter is opaque
    /// provenance, not a region, so it has no `prov_labels` of its own. Decoupled from the
    /// region/safety model entirely — an opaque label affects **only** the provenance checks
    /// (`CapRequire`/`CapRequireIfAlias`), never null-deref, bounds, liveness, or permissions —
    /// so it cannot introduce a false PASS. Persistent (a fact about the SSA value, not memory),
    /// so not cleared on havoc.
    pub(crate) opaque_labels: FxHashMap<u32, FxHashSet<u32>>,
    /// **Non-null opaque-provenance ids** (from a `SizeSpec::NonNull` / LLVM `nonnull`
    /// pointer parameter): an opaque pointer whose provenance id is here is guaranteed
    /// non-null, so `NoNullDeref` is discharged through it (and anything derived by
    /// `gep`/copy, which carries the id) — while bounds/liveness stay unknown (a `nonnull`
    /// pointer may still dangle). Seeded at entry, meet-joined at merges. A fact about the
    /// value, not memory (not cleared on havoc).
    pub(crate) nonnull_provs: FxHashSet<u32>,
    /// **Borrow-stack per region** for the opt-in Rust aliasing model (`--aliasing-model`):
    /// `region id → the live borrow tags (retag-dst registers), innermost last`. A `&mut`
    /// reborrow pushes a tag (invalidating siblings by popping above its parent); a write
    /// through a tag pops the tags above it. Accessing through a tag no longer on its region's
    /// stack is a **use-after-invalidation** (`NoAliasingViolation`). `None` = the stack is
    /// *poisoned* (paths disagreed at a merge, or a parent was already gone) — checks are then
    /// skipped for that region (sound: no detection, never a false FAIL). Empty unless the model
    /// is on.
    pub(crate) region_borrows: FxHashMap<usize, Option<Vec<RegId>>>,
    /// **Scalar taint labels** per SSA register (the directional taint lattice, G6-family J/F/D):
    /// interned taint-label ids a register's value carries, sourced by a `taint-source` contract
    /// or a load from a labelled region, propagated through arithmetic/casts, checked by a
    /// `taint-sink` (`Inst::TaintCheck`) and cleared by a `taint-sanitize`. Pointer/region taint
    /// reuses `prov_labels`; this map is the scalar complement. Meet-joined at merges (a value is
    /// "definitely tainted" only if tainted on every incoming path — no false FAIL under a
    /// partly-tainted phi). A fact about the SSA value, not memory (not cleared on havoc).
    pub(crate) tainted: FxHashMap<RegId, FxHashSet<u32>>,
    /// **Typestate per resource per protocol** (the generalised protocol tracker, roadmap #4):
    /// `(resource identity, protocol id) → current state id`. Advanced by `Inst::TypestateSet`
    /// transitions and checked by `Inst::TypestateRequire` obligations (both contract-driven).
    /// Generalises the lifetime/lock/taint typestates to any contract-defined finite-state
    /// protocol. Meet-joined at merges (a resource is "definitely in state S" only if it is S
    /// on every incoming path — so a require refutes with no false FAIL under a partial state).
    /// A fact about the resource, not memory (not cleared on havoc).
    pub(crate) typestates: FxHashMap<(ResKey, u32), u32>,
    /// **Reference counts per resource per protocol** (G8): `(resource, protocol) → count`.
    /// Raised by an `inc` and lowered by a `dec` (`Inst::Refcount`); a `dec` below zero is an
    /// underflow (premature free → UAF). Meet-joined at merges (kept only if all incoming
    /// paths agree on the count — so an underflow refutes only when definite; no false FAIL).
    pub(crate) refcounts: FxHashMap<(ResKey, u32), i64>,
    /// **RCU read-side nesting depth** on this path (data-race hardening): a shared *read* while
    /// this is > 0 is inside an RCU read-side critical section and race-free by the RCU contract,
    /// so excluded from the data-race pass. Meet-joined (min) at merges — an access counts as
    /// RCU-protected only if it is on every incoming path.
    pub(crate) rcu_depth: u32,
    /// **IRQ-disabled nesting depth** on this path (G9): raised by `spin_lock_irqsave`/
    /// `local_irq_disable`/`local_bh_disable`, lowered by the matching restore. An access made
    /// while this is > 0 holds a synthetic `@irqoff` lock, so a location protected against IRQs
    /// in one place but not another is flagged by the data-race pass. Meet-joined (min).
    pub(crate) irq_off: u32,
    /// **Per-CPU pointer identities** on this path (data-race hardening): opaque-pointer ids
    /// returned by a per-CPU accessor (`this_cpu_ptr`/…). Accesses through them are thread-local
    /// (not shared), so excluded from the data-race pass. Meet-joined at merges.
    pub(crate) percpu: FxHashSet<u32>,
    /// **Resolved function-pointer values**: a register holding a function address
    /// devirtualised from a constant ops-struct load (see `global_fnptrs`) maps to
    /// its target `FuncId`, so an indirect call through that register is analysed
    /// with the callee's summary rather than an opaque havoc. Persistent (a fact
    /// about the SSA value, not memory).
    pub(crate) fn_ptrs: FxHashMap<RegId, FuncId>,
    /// **Locks held** on this path, by the identity of the lock pointer's base object
    /// (`spin_lock`/`mutex_lock`/… acquired and not yet released). Re-acquiring a base
    /// already here is an AA self-deadlock. Structural per-path state (not memory), so
    /// not cleared on a heap havoc; joined by meet at control-flow merges.
    pub(crate) locks_held: FxHashSet<RefBase>,
    /// **Spinning locks held** on this path (the atomic-context subset of `locks_held`:
    /// `spin_lock`/`read_lock`/`write_lock` families, not sleepable `mutex`/`down`). A
    /// blocking call while this is non-empty is a sleep-in-atomic bug. Meet-joined at merges
    /// like `locks_held`, and conservatively dropped when the lock base is passed to any call.
    pub(crate) spin_held: FxHashSet<RefBase>,
    /// **Lock class held per lock base** on this path — the static cross-function name
    /// (see `lockclass`) of every lock currently held, keyed by its runtime base. Used to
    /// emit lock-order edges (held-class → newly-acquired-class) for ABBA cycle detection.
    /// Meet-joined at merges (only a lock held on every incoming path stays), and dropped
    /// alongside `locks_held`/`spin_held` when the base is passed to any call.
    pub(crate) held_classes: FxHashMap<RefBase, String>,
    /// **User-memory addresses fetched** on this path, by `(source base, concrete byte
    /// offset)` — one entry per `copy_from_user`/`get_user` from a concrete user address.
    /// Re-fetching an address already here is a **double-fetch** (a TOCTOU on adversary-
    /// controlled user memory). Structural per-path state (not cleared on a heap havoc);
    /// joined by meet at merges, so a re-fetch is flagged only when the first fetch is
    /// definite on every incoming path — sound (a partial fetch never fabricates one).
    pub(crate) user_fetches: FxHashSet<(RefBase, u128)>,
    /// **Bases freed by an attributed freeing call** (`Summary.frees_arg`) on this path —
    /// so a second freeing-wrapper call on the same pointer is a definite double-free
    /// (which the coarse `frees` region havoc cannot attribute). Joined by meet at merges
    /// (only a base freed on *every* incoming path counts). Structural, not memory.
    pub(crate) freed_bases: FxHashSet<RefBase>,
    /// Whether this path is *exact*: no over-approximation (loop-header havoc,
    /// opaque call, or non-determined load) has been introduced. A symbolic
    /// **refutation** (sound `FAIL` + counterexample) is only emitted on an
    /// exact path, where the path condition characterizes genuinely reachable
    /// states, so a violating model is a real execution. Proofs (`PASS`) do not
    /// need this — over-approximation is sound for proving.
    pub(crate) exact: bool,
}

/// One incoming control-flow edge into a block, queued during the reverse-
/// postorder walk: the predecessor's post-state, the edge's guard (the branch
/// condition under which it is taken; `None` for an unconditional `Br`), and the
/// block-parameter arguments it supplies.
pub(crate) struct EdgeState {
    pub(crate) pred_state: PathState,
    pub(crate) guard: Option<ExprId>,
    pub(crate) args: Vec<Operand>,
}

/// Per-obligation aggregation across paths.
pub(crate) struct MemAgg {
    pub(crate) all_proven: bool,
    /// A counterexample from any path that definitely violated the obligation.
    pub(crate) refutation: Option<Model>,
    pub(crate) predicate: String,
    pub(crate) residual: String,
}

/// Per scalar-check aggregation across paths.
pub(crate) struct ScalarAgg {
    /// Proved on every path so far.
    pub(crate) all_proven: bool,
    /// A counterexample from any path that definitely violated the check.
    pub(crate) refutation: Option<Model>,
}

/// The outcome of deciding a safety goal on one path.
pub(crate) enum Decision {
    /// Proved to hold.
    Proven,
    /// Neither proved nor (soundly) refuted.
    Unknown,
    /// Violated on this exact path, witnessed by the model.
    Refuted(Model),
}

/// How aggressively a goal may be refuted (see [`Explorer::try_refute`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RefuteMode {
    /// Never refute (prove-only).
    Off,
    /// Refute only a goal that is *always* violated on the path.
    Definite,
    /// Refute a goal violated by *some* reaching input (the operation executes,
    /// so any such input is a real runtime violation).
    Possible,
}

pub(crate) struct Explorer<'f> {
    pub(crate) ctx: ExprCtx,
    pub(crate) fresh: u32,
    /// A monotone counter for opaque-pointer provenance ids (see `Prov::Unknown`); separate
    /// from `fresh` so symbol numbering — and hence witnesses/determinism — is unchanged.
    pub(crate) prov_ids: u32,
    /// Bug-finding mode: relax the memory-refutation gate so a spatial violation
    /// whose offset/size depend only on genuine inputs (parameters) is reported
    /// even on a globally-inexact path (e.g. after an init loop). Off by default
    /// (verification stays strict — refute only on an exact path). See `decide`.
    pub(crate) bug_finding: bool,
    /// Whether this function is exported (externally reachable). In bug-finding mode
    /// only an exported function's `arg…` parameters count as genuine adversarial
    /// inputs (see `goal_is_genuine`); an internal function's are caller-constrained.
    pub(crate) exported: bool,
    /// Honour `RefWitness { assumed }` (a raw pointer field valid under the opt-in).
    pub(crate) assume_valid_params: bool,
    /// Pointee byte size of a register, from the struct type of the `gep` that indexes it
    /// (`Module::reg_ptr_hints`). Used to **size** a loop-carried pointer's region at the loop
    /// header under `--assume-valid-loop-ptrs`, so accesses through a moving iterator get real
    /// bounds instead of an unsized (always-UNKNOWN) region. Empty for typeless frontends.
    pub(crate) reg_ptr_hints: &'f HashMap<RegId, PtrHint>,
    /// **Closed-world devirtualisation** for this function: register → the name of the single
    /// function it provably points to (a heap/param `obj->ops->fn()` resolved by the whole-program
    /// points-to). An indirect call through such a register is analysed with that callee's summary
    /// instead of an opaque havoc. Call-target resolution **only**: the loaded pointer keeps its
    /// real provenance, so its null/uninit/bounds checks are unaffected (no masking). Empty unless
    /// `--closed-world` whole-program — the store-completeness that makes a singleton exact.
    pub(crate) devirt: &'f HashMap<RegId, String>,
    /// Set when this function is a **MMIO dispatch handler** (`Module::mmio_handlers`): its
    /// `(addr, size)` parameters are constrained by the memory core's dispatch guarantee
    /// (`size ∈ {1,2,4,8}`, and `addr + size ≤ region_size` when the inner `Some` gives the
    /// region byte size). `None` for an ordinary function. Genuine precision, not an assumption.
    pub(crate) mmio_region: Option<csolver_ir::MmioHandler>,
    pub(crate) visits: usize,
    pub(crate) truncated: bool,
    /// Successors whose incoming edge a **visited** predecessor pruned as bit-precisely
    /// infeasible, and the blocks actually visited. A block that was pruned into but never
    /// visited has *every* live path to it proven unreachable, so it cannot execute — its
    /// obligations are then vacuously satisfied (see `SymbolicReport::dead_blocks`). Kept apart
    /// from "never even considered" (a block with no visited predecessor), which is left
    /// UNKNOWN: that case cannot distinguish transitively-dead code from a back-edge-only
    /// entry, and claiming it proven could be a false PASS.
    pub(crate) pruned_succs: FxHashSet<BlockId>,
    /// Blocks the merged exploration actually entered.
    pub(crate) visited_blocks: FxHashSet<BlockId>,
    pub(crate) limits: ExecLimits,
    /// The interleaving-trace length bound, **derived from the function** (its basic-block count) —
    /// a trace can hold at most this many ordered events. Replaces a fixed magic length: a bigger
    /// function is allowed a proportionally longer trace (better weak-memory recall), while the trace
    /// stays bounded by the CFG size (the interleaving search's own state budget bounds the cost).
    pub(crate) race_trace_cap: usize,
    /// When exploration must stop (from `limits.time_budget`); `None` ⇒ no clock.
    pub(crate) deadline: Option<std::time::Instant>,
    /// Scalar `SafetyCheck` aggregation, keyed by (block, idx).
    pub(crate) scalar: HashMap<(BlockId, usize), ScalarAgg>,
    pub(crate) mem: HashMap<(BlockId, usize, SafetyProperty), MemAgg>,
    pub(crate) assumptions: HashSet<&'static str>,
    /// Sound interval invariants (the source of loop invariants).
    pub(crate) analysis: IntervalAnalysis,
    /// Relational (zone) invariants — difference constraints between registers
    /// that the per-register interval domain cannot express.
    pub(crate) zones: ZoneAnalysis,
    /// Equality-exit induction variables (`while i != n`), whose `start ≤ i ≤ n`
    /// bound the interval domain cannot derive from a `!=` guard.
    pub(crate) inductions: InductionAnalysis,
    pub(crate) dominators: Dominators,
    /// Block ids that are loop headers.
    pub(crate) headers: HashSet<BlockId>,
    /// Per loop header: registers the loop body may redefine (havoc set).
    pub(crate) loop_modified: HashMap<BlockId, Vec<RegId>>,
    /// Per loop header: whether the loop body may free memory.
    pub(crate) loop_frees: HashMap<BlockId, bool>,
    /// Per loop header: the blocks forming the loop body (for pattern analyses).
    pub(crate) loop_bodies: HashMap<BlockId, Vec<BlockId>>,
    /// Interprocedural summaries, by callee id (empty = havoc all calls).
    pub(crate) summaries: HashMap<FuncId, Summary>,
    /// Whole-program summaries by callee **name**, for resolving a cross-file
    /// `Callee::Symbol(name)` call that has no in-module id — so a caller sees a
    /// remote callee's effects (writes/frees/return) instead of an opaque havoc.
    /// Empty in the ordinary per-module path (every such call stays opaque).
    pub(crate) name_summaries: HashMap<String, Summary>,
    /// The provenance lattice (label id → granted capability ids), from the module's
    /// contracts. An [`Inst::CapRequire`] checks it; a label absent here grants all
    /// capabilities (sound default). Empty ⇒ the capability mechanism is inert.
    pub(crate) prov_grants: HashMap<u32, HashSet<u32>>,
    /// A deterministic synthetic field layout per region: the byte offset assigned
    /// to each `(region, field index)` the first time it is accessed, and the
    /// running frontier per region. Fields are packed sequentially so distinct
    /// fields occupy disjoint ranges (an exact field-sensitive heap), while the
    /// same field always reuses its offset (so a store then load round-trips). The
    /// real layout is irrelevant — only `offset + size <= region size` is asserted.
    pub(crate) field_offsets: HashMap<(usize, u32), u64>,
    pub(crate) field_frontier: HashMap<usize, u64>,
    /// Per-register classification of how a scalar-used-as-pointer was computed
    /// (diagnostic; tags the `ScalarAsPtr` provenance residual at scale).
    pub(crate) scalar_ptr_cause: HashMap<RegId, ScalarPtrCause>,
    /// Referenced global definitions: symbol name → (region id, alignment).
    /// The regions are created once at state initialization (sorted by name for
    /// determinism) and are `Live` forever — globals are never freed.
    pub(crate) global_rids: HashMap<String, (usize, u64)>,
    /// **Devirtualisation tables** keyed by the *region id* of a constant
    /// ops-struct/vtable global: byte offset → target function. A load of a
    /// pointer field at a matching offset resolves the loaded function pointer,
    /// so an indirect call through it uses the callee's summary (see `step_call`).
    pub(crate) global_fnptrs: HashMap<usize, HashMap<u64, FuncId>>,
    /// **Prove-result cache** over the function's single `ExprCtx`: a memo from
    /// `(assumptions, goal)` to the proof method (or `None`). Sound because the
    /// `ExprCtx` is append-only — an `ExprId` denotes the same formula for the
    /// whole discharge — so `prove_implies_method` is a pure function of the key.
    /// Repeated identical bounds/alias queries (loops, many accesses under one
    /// path condition) then skip re-bit-blasting. The `linear-no-overflow` side
    /// effect is re-applied on a hit.
    pub(crate) prove_cache: FxHashMap<(Box<[ExprId]>, ExprId), Option<ProofMethod>>,
    /// Memoized **variable set** (sorted `Sym` ids) of an expression, keyed by its interned id
    /// (immutable, so the cache is stable). Powers the relevance pre-filter in `branch_infeasible`,
    /// which skips the full path-condition query when a branch condition shares no variable with it.
    pub(crate) sym_memo: FxHashMap<ExprId, std::rc::Rc<[ExprId]>>,
    /// Static **lock-class map** for this function: register → the cross-function name
    /// of the lock it designates (see `lockclass`). Consulted at each lock-acquire to
    /// name the acquired lock for ABBA lock-order edges.
    pub(crate) lock_classes: HashMap<RegId, String>,
    /// **Lock-order edges** collected on this function: `(held-class, then-acquired-class)`
    /// pairs observed on some path. Streamed out for whole-program cycle detection (an
    /// A→B here plus a B→A elsewhere is a potential ABBA deadlock).
    pub(crate) lock_edges: HashSet<(String, String)>,
    /// **Shared-memory access records** for the lockset data-race check (G1): per access to a
    /// *shareable* location (a global, or an object reached through a parameter — not a stack
    /// local), the location's class, whether it is a write, and the set of lock *classes* held
    /// at the access. Streamed whole-program: a location whose accesses share no common lock,
    /// include a write, and span ≥2 functions is a candidate race (the Eraser lockset signal).
    /// `(access-class, is_write, sorted lock-classes held)`.
    pub(crate) race_accesses: HashSet<(String, bool, Vec<String>)>,
    /// Registers whose value is derived from a load (see [`load_derived_regs`]): a read through
    /// such a pointer is **address-dependent** and recorded as a non-reordering `DepRead`.
    pub(crate) load_derived: HashSet<RegId>,
    /// **Ordered event trace** for the two-thread interleaving check (subsystem 4): the
    /// sequence of lock acquires/releases and shared reads/writes in execution order, as
    /// `(kind, class)` with kind `0`=acquire, `1`=release, `2`=read, `3`=write. Consumed by
    /// `csolver_verifier::interleave` to find atomicity violations (a split-critical-section
    /// read-modify-write a foreign write can interrupt) with an interleaving witness.
    pub(crate) race_trace: Vec<(u8, String)>,
    /// **Shared-borrow registers** (opt-in `--aliasing-model`): pointer registers derived —
    /// through casts / field / index projections / copies — from a genuine shared `&T` borrow
    /// (a `RefWitness { writable: false, assumed: false }`). A `Store` through one is a write
    /// through a shared reference, an unambiguous Rust aliasing (borrow-stack) violation. Empty
    /// unless the aliasing model is on (see [`shared_borrow_regs`]).
    pub(crate) shared_borrow_regs: HashSet<RegId>,
    /// Static borrow-tag derivation for the aliasing model (empty unless it is on). See
    /// [`BorrowInfo`] / [`borrow_info`].
    pub(crate) borrow_info: BorrowInfo,
    pub(crate) f: &'f Function,
}
