# Detecting Copy-Fail and its family — what's missing and how to generalize

## Where it stands (confirmed)

The write-capability machinery is **complete**: `SafetyProperty::WriteCapability`, the
`CapRequire` / `CapRequireIfAlias` / `CapRequireIfAliasFields` obligations, `ProvLabel`
+ the `prov_grants` lattice, and a contract language (`prov <label> grants=…`,
`label arg foreign`, `require-if-alias`). On the vulnerable `algif_aead` the scan even
**raises the exact obligation** at `aead_recvmsg#0` — *"an in-place operation's aliased
field region grants the required capability."* It **PASSes** only because the aliased
region is **unlabelled** (sound-default: unlabelled ⇒ grants everything ⇒ never false-FAIL).

So detection is gated on exactly one thing: **does a restrictive label reach the write
target?** Two concrete reasons it doesn't here:

1. **Stale label source.** `provenance.contract` labels `af_alg_sendpage arg1 foreign`,
   but `af_alg_sendpage` was **removed** (~6.5); in v6.12 the page enters via
   `af_alg_sendmsg` + `MSG_SPLICE_PAGES`. The seed label never fires.
2. **Cross-syscall propagation gap.** Even the contract's `af_alg_get_rsgl arg3 foreign`
   / `aead_recvmsg` entries don't reach the aliased region: the `foreign` page is
   labelled in *sendmsg* and must persist on the socket's `ctx->tsgl` into a *later
   recvmsg* — a stateful, cross-syscall flow the current static labelling doesn't carry.

Two sub-problems, then: **(A) label sources** and **(B) getting labels to the check.**

## (A) Label sources — ranked by how many *other* bugs they also catch

1. **IR-intrinsic read-only — broadest, ~free, no contracts.** Honour what the IR
   already states: LLVM `readonly`/`writeonly` params, `constant` globals, DWARF
   `const T*` pointees → mark those regions non-writable. A write through them refutes
   the existing `valid_write` / `write_capability` obligation. Instantly a kernel-wide
   detector for the **write-through-const / write-to-RO-global** family — a large, real
   class — with zero per-API work. *Start here.*

2. **Origin/provenance axioms — the general engine, small seed set.** A handful of
   *origin* contracts (not one-per-bug) that label a region by where its pages came
   from, then let the **existing effect-summary inference propagate them program-wide**:
   - user memory: `copy_from_user`, `get_user_pages` without `FOLL_WRITE`, READ iov → `user`/read-only;
   - foreign/spliced pages: `MSG_SPLICE_PAGES`, `splice`/`vmsplice`, page-cache pages → `foreign`;
   - read-only mappings: pages from a VMA lacking `VM_WRITE`.
   One mechanism subsumes **Copy-Fail + write-to-user + write-to-foreign-page +
   write-to-RO-mapping**. Highest leverage for "also finds similar bugs."

3. **Aliasing-driven permission mismatch — structural, label-free sub-class.** The
   Copy-Fail *core* is: a write target provably **aliases** a region that also arrives
   via a read-only path in the same op. CSolver already detects the in-place alias; feed
   "did either aliased side arrive read-only-typed" into the obligation and it fires
   without any explicit label. Generalises to **any in-place-op-on-a-read-only-source**.

4. (Speculative) capability from allocation type / `const` struct fields — type-confusion writes.

## (B) Propagation — reaching the check, incl. cross-syscall

- Near-term: a **conservative label at the read side** — mark `ctx->tsgl` elements
  potentially-`foreign` when read in recvmsg (the contract tries this; fix it to fire on
  the current `af_alg_sendmsg` path). Sound (over-approximate), makes the obligation
  refutable now.
- General: treat an **ops-object as a stateful provenance carrier** — a per-`struct
  proto_ops` summary so a label set by one handler persists on the shared object into
  another. This is the durable fix and helps every cross-handler stateful class.

## Recommendation

1. **(A1) IR-intrinsic read-only** — cheapest, broadest, immediately useful.
2. **(A2) origin/provenance axioms** riding the existing propagation — the general
   engine that covers Copy-Fail *and* its neighbours.
3. **(A3) aliasing mismatch** as a label-free booster for in-place-op bugs.
4. Refresh the stale contract to the `MSG_SPLICE_PAGES` entry + fix the recvmsg label
   link → the experiment's `aead_recvmsg#0` obligation flips **PASS→FAIL** (end-to-end
   proof), then rely on A1/A2 for breadth.

## Update 2026-07-11 — A1 landed; copy-fail real-IR gap pinpointed empirically

**A1 done (`e60b587`)**: a write into a read-only `constant`/.rodata GLOBAL is now
**refuted** (FAIL), not UNKNOWN — kernel-wide, no per-scan code, differential-SOUND.
This is the first write-capability *source*.

**Copy-fail on the real vulnerable v6.12 IR — precisely diagnosed by minimal
reproduction.** The mechanism (A2 labels + A3 in-place-alias gate + B cross-syscall
seed) is **complete and fires on every faithful shape** — proven by minimal `.ll`
probes: a `foreign` page stored in-place into a request's src/dst fields is refused
**even across an intervening opaque-call havoc, through an interior pointer, and with an
opaque (heap) request** (`alloc_req()`), not just a stack `alloca`. The label also
**does reach** the real AEAD request (cross-syscall seed + taint-on-read: the request
object carries `foreign`).

What does *not* connect on the real optimized IR: `req->src` (off 64) and `req->dst`
(off 72) read back as **two distinct, fresh, unlabelled values** — so the in-place gate
cannot see `src == dst` and (soundly) does not fire. Every synthetic where the SAME SSA
value reaches both fields fires; the real IR does not present that identity at the
pointer level. Either the src/dst are set by a helper whose per-field store the analysis
does not forward to those exact `(opaque-base, offset)` slots, or — more likely — the
CVE's aliasing is at the **page** level (two distinct scatterlist objects describing the
same pages), *below* the sgl-pointer-identity granularity the `require-if-alias` gate
checks.

**Why it was not forced:** making the gate fire when the aliasing is unknown/absent
would false-FAIL the patched *out-of-place* path — the exact unsoundness the design
forbids. So detection here needs a genuine, sound capability, one of:
1. **Per-field store effects** in the request-build helpers' contracts (`arg0->src :=
   arg1`, `arg0->dst := arg2`), so the analysis recovers the value written to each field
   even when the helper is a call — general, contract-expressible.
2. **Page-granularity aliasing** for the capability gate: refuse an in-place op when
   src and dst scatterlists provably cover the same pages (not just the same pointer).
3. Analyse a **lower-optimisation** build (`-O1`) where the in-place identity survives as
   visible SSA — a pragmatic corpus choice for the regression fixture.

**Tested option 3 (`-O1` rebuild of the vulnerable module):** copy-fail still does **not**
fire (coverage rises to 45.7% PASS as the IR is more analysable, but the only finding is
an unrelated `sockptr_is_kernel [ValidRead]`; no `write_capability` FAIL). So the
in-place `req->src == req->dst` pointer identity is absent even at `-O1` — strong evidence
the CVE's aliasing is at the **page** level (distinct scatterlist objects over the same
pages), which a pointer-identity gate cannot catch by construction. **Option 2
(page-granularity aliasing) is therefore the real requirement**, or option 1 (per-field
store-effect contracts) combined with page-level reasoning. This is a substantial, sound
analysis feature — deliberately *not* faked with a heuristic that would false-FAIL the
patched out-of-place path.

## Update 2026-07-12 — "page-granular aliasing" is NOT the binding constraint

Traced the vulnerable module at `-O1` (readable IR) to the exact `require-if-alias`
site: `aead_request_set_crypt(req, src=%144, dst=%146)` is a *visible call*, and

- `src = load %rsgl_src` (a local pointer slot),
- `dst = load (areq->first_rsgl.sgl.sgt.sgl)` (a heap field of the RX request).

At the gate, `alias_lacks_cap(pa, pb)` sees `pa = Unknown(Load 36)`, `pb =
Unknown(Load 45)` — **distinct opaque ids, both unlabelled** (`labA = labB = 0`), so
`lacks = false`. Two independent facts, both upstream of aliasing:

1. **The gate is already object-granular.** `alias_lacks_cap` treats two pointers as
   aliasing when they share the same region *or* the same opaque base id (any offset,
   offset-satisfiable for opaque) — a strictly stronger test than pointer identity.
   Adding "page granularity" changes nothing here: `src` and `dst` have *different*
   bases, not the same base at a different offset.
2. **The real gap is value-flow, not aliasing.** `src` and `dst` are the *same* sgl in
   the in-place case, but the analysis cannot see it because (a) the intermediate pointer
   slot `%rsgl_src` is not promoted to SSA, so `src` stays an opaque load; (b) even
   promoted, `src` and `dst` become two loads of the same heap field, which need
   **heap load-consistency** (same `(base, offset)` load ⇒ same value) to be recognised
   as equal; and (c) the `foreign` label is applied to one SSA load of the request and
   lost across the alloca round-trip, so it never reaches `dst` (**label persistence on
   the region**, not on a value).

So closing this needs a **value-flow chain** — mem2reg promotion of multi-store pointer
slots + heap load-consistency + region-level label persistence — each soundness-critical
(a rushed version false-FAILs the patched out-of-place path). It is deliberately NOT the
single "page-granular aliasing" feature, and was not built as a rushed risky chain; this
note records the precise, ordered work so it can be done properly and oracle-guarded.

## Update 2026-07-12 (2) — value-flow gap CLOSED; the CVE sink is the AAD copy

**Opaque read-consistency landed (`6a9493b`)** — read-after-read consistency, which
existed only for region bases, now covers **opaque object ids** too. Two loads of the
same `(opaque-base, concrete offset)` return the same value, so `req->src`/`req->dst`
read off an opaque request (alloca round-trip + interior-field loads — the real crypto
worker's shape) are now recognised as aliasing. Proven by a regression test on that exact
shape (in-place refused, out-of-place not). Sound and general (differential-SOUND). This
was the object-granular value-flow gap — **not** "page-granular aliasing," which the gate
never needed.

**Why the real CVE still does not fire — definitively traced.** In the vulnerable v6.12
`-O1` IR, `aead_request_set_crypt(req, src, dst)` is called with
`src = areq->tsgl` (field 5, the **TX** scatterlist) and `dst = areq->first_rsgl`
(field 2, the **RX** scatterlist) — two *different* fields, i.e. the main crypto is
legitimately **out-of-place** (TX→RX). Read-consistency correctly does NOT alias them
(no false FAIL). Matching the fix commit exactly — *"mostly reverts … except for the
copying of the associated data"* — CVE-2026-31431 is the in-place copy of the
**associated data (AAD)**, a *different* operation from the main src/dst crypto that the
contract's `require-if-alias` gates. The contract targets the wrong sink.

**The remaining, correctly-scoped step** is therefore a **contract change** (data, no scan
code): put a capability gate on the AAD-copy sink — `crypto_aead_copy_sgl` /
the NULL-cipher AAD copy — that fires when its destination is a `foreign` page, gated so
the patched out-of-place AAD copy does not fire. This needs the AAD-copy semantics modelled
and validated on a positive/negative pair, but it is the right level: no aliasing/value-flow
feature closes it, because the main-crypto aliasing the previous gate checked is genuinely
absent here.

## Validation (soundness-first, mandatory)

Extend the **C differential oracle** with positive controls for the write-capability
class — a deliberate write-through-`const`, a write into a `copy_from_user` source, and
an in-place op on a `foreign` page — so the detector is oracle-guarded (no false FAIL)
exactly like the existing 8 bug classes. Add the built vulnerable `algif_aead` module
(saved in `logs/`) as a regression fixture: it must FAIL once A1/A2 land and PASS after
the upstream fix `a664bf3d603d`.
