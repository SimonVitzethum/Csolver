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
            Effect::Alloc { size, align } => Some((size, *align)),
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

fn parse_effect(line: &str) -> Result<Effect, String> {
    let mut it = line.split_whitespace();
    let kind = it.next().ok_or("empty effect")?;
    let rest: Vec<&str> = it.collect();
    match kind {
        "alloc" => {
            let size = parse_kv_size(&rest, "size")?;
            let align = parse_kv_u32(&rest, "align")?;
            Ok(Effect::Alloc { size, align })
        }
        "free" => Ok(Effect::Free { ptr: parse_arg(rest.first().copied().unwrap_or(""))? }),
        "write" => {
            let ptr = parse_arg(rest.first().copied().unwrap_or(""))?;
            let len = parse_kv_size(&rest, "len")?;
            let fill = match kv(&rest, "fill") {
                None | Some("undef") => Fill::Undef,
                Some("user") => Fill::User,
                Some(other) => return Err(format!("unknown fill `{other}`")),
            };
            let from = match kv(&rest, "from") {
                Some(s) => Some(parse_arg(s)?),
                None => None,
            };
            Ok(Effect::Write { ptr, len, fill, from })
        }
        "read" => {
            let ptr = parse_arg(rest.first().copied().unwrap_or(""))?;
            let len = parse_kv_size(&rest, "len")?;
            let sink = match kv(&rest, "sink") {
                None | Some("internal") => ReadSink::Internal,
                Some("user") => ReadSink::User,
                Some(other) => return Err(format!("unknown sink `{other}`")),
            };
            Ok(Effect::Read { ptr, len, sink })
        }
        // `label arg<k> <labelname>` and `require arg<k> <capname>` (positional).
        "label" => {
            let ptr = parse_arg(rest.first().copied().unwrap_or(""))?;
            let label = rest.get(1).copied().ok_or("`label` needs a label name")?.to_string();
            Ok(Effect::Label { ptr, label })
        }
        "require" => {
            let ptr = parse_arg(rest.first().copied().unwrap_or(""))?;
            let cap = rest.get(1).copied().ok_or("`require` needs a capability name")?.to_string();
            Ok(Effect::Require { ptr, cap })
        }
        // `propagate arg<dst> from arg<src>`.
        "propagate" => {
            let dst = parse_arg(rest.first().copied().unwrap_or(""))?;
            if rest.get(1) != Some(&"from") {
                return Err("`propagate` syntax is `propagate arg<dst> from arg<src>`".into());
            }
            let src = parse_arg(rest.get(2).copied().unwrap_or(""))?;
            Ok(Effect::Propagate { dst, src })
        }
        // `require-if-alias arg<a> arg<b> <cap>`.
        "require-if-alias" => {
            let a = parse_arg(rest.first().copied().unwrap_or(""))?;
            let b = parse_arg(rest.get(1).copied().unwrap_or(""))?;
            let cap = rest.get(2).copied().ok_or("`require-if-alias` needs a capability")?.to_string();
            Ok(Effect::RequireIfAlias { a, b, cap })
        }
        // `seed arg<k> <label>`.
        "seed" => {
            let arg = parse_arg(rest.first().copied().unwrap_or(""))?;
            let label = rest.get(1).copied().ok_or("`seed` needs a label name")?.to_string();
            Ok(Effect::Seed { arg, label })
        }
        // `require-if-alias-fields arg<k> <off_a> <off_b> <cap>` (offsets are byte offsets).
        "require-if-alias-fields" => {
            let arg = parse_arg(rest.first().copied().unwrap_or(""))?;
            let off_a = rest.get(1).and_then(|s| s.parse().ok()).ok_or("needs off_a")?;
            let off_b = rest.get(2).and_then(|s| s.parse().ok()).ok_or("needs off_b")?;
            let cap = rest.get(3).copied().ok_or("needs a capability")?.to_string();
            Ok(Effect::RequireIfAliasFields { arg, off_a, off_b, cap })
        }
        // `taint-source arg<k>|ret <label>`, `taint-sink arg<k> <label>`,
        // `taint-sanitize arg<k>|ret <label>`.
        "taint-source" => {
            let arg = parse_arg_or_ret(rest.first().copied().unwrap_or(""))?;
            let label = rest.get(1).copied().ok_or("`taint-source` needs a label name")?.to_string();
            Ok(Effect::TaintSource { arg, label })
        }
        "taint-sink" => {
            let arg = parse_arg(rest.first().copied().unwrap_or(""))?;
            let label = rest.get(1).copied().ok_or("`taint-sink` needs a label name")?.to_string();
            Ok(Effect::TaintSink { arg, label })
        }
        "taint-sanitize" => {
            let arg = parse_arg_or_ret(rest.first().copied().unwrap_or(""))?;
            let label = rest.get(1).copied().ok_or("`taint-sanitize` needs a label name")?.to_string();
            Ok(Effect::TaintSanitize { arg, label })
        }
        // `typestate-set arg<k>|ret <protocol> <state>` and
        // `typestate-require[-not] arg<k> <protocol> <state>`.
        "typestate-set" => {
            let arg = parse_arg_or_ret(rest.first().copied().unwrap_or(""))?;
            let protocol = rest.get(1).copied().ok_or("`typestate-set` needs a protocol")?.to_string();
            let state = rest.get(2).copied().ok_or("`typestate-set` needs a state")?.to_string();
            Ok(Effect::TypestateSet { arg, protocol, state })
        }
        "typestate-require" | "typestate-require-not" => {
            let arg = parse_arg(rest.first().copied().unwrap_or(""))?;
            let protocol = rest.get(1).copied().ok_or("`typestate-require` needs a protocol")?.to_string();
            let state = rest.get(2).copied().ok_or("`typestate-require` needs a state")?.to_string();
            Ok(Effect::TypestateRequire { arg, protocol, state, negate: kind == "typestate-require-not" })
        }
        other => Err(format!("unknown effect `{other}`")),
    }
}

/// Look up a `key=value` token in the remaining words.
fn kv<'a>(rest: &[&'a str], key: &str) -> Option<&'a str> {
    rest.iter().find_map(|w| w.strip_prefix(key)?.strip_prefix('='))
}

fn parse_kv_u32(rest: &[&str], key: &str) -> Result<u32, String> {
    kv(rest, key)
        .ok_or_else(|| format!("missing `{key}=`"))?
        .parse()
        .map_err(|_| format!("`{key}=` expects an integer"))
}

fn parse_kv_size(rest: &[&str], key: &str) -> Result<SizeExpr, String> {
    parse_size(kv(rest, key).ok_or_else(|| format!("missing `{key}=`"))?)
}

/// `arg3` → 3.
fn parse_arg(tok: &str) -> Result<usize, String> {
    tok.strip_prefix("arg")
        .and_then(|n| n.parse().ok())
        .ok_or_else(|| format!("expected `arg<k>`, got `{tok}`"))
}

/// The taint-target sentinel for a call's **return value** (`ret`), used by
/// `taint-source`/`taint-sanitize` in place of an `arg<k>` index.
pub const RET_ARG: usize = usize::MAX;

/// Parse a taint target: `arg<k>` or the literal `ret` (the call's result value).
fn parse_arg_or_ret(tok: &str) -> Result<usize, String> {
    if tok == "ret" {
        Ok(RET_ARG)
    } else {
        parse_arg(tok)
    }
}

/// `arg0`, `arg0*arg1`, or a decimal integer.
fn parse_size(tok: &str) -> Result<SizeExpr, String> {
    if let Some((a, b)) = tok.split_once('*') {
        return Ok(SizeExpr::Product(parse_arg(a)?, parse_arg(b)?));
    }
    if tok.starts_with("arg") {
        return Ok(SizeExpr::Arg(parse_arg(tok)?));
    }
    tok.parse::<u64>()
        .map(SizeExpr::Const)
        .map_err(|_| format!("expected a size (`arg<k>`, `arg<k>*arg<j>`, or an integer), got `{tok}`"))
}

/// The built-in contract files, embedded so the binary is self-contained.
const DEFAULT_FILES: &[(&str, &str)] = &[
    ("alloc.contract", include_str!("../data/alloc.contract")),
    ("free.contract", include_str!("../data/free.contract")),
    ("user_copy.contract", include_str!("../data/user_copy.contract")),
    ("provenance.contract", include_str!("../data/provenance.contract")),
    ("taint.contract", include_str!("../data/taint.contract")),
    ("typestate.contract", include_str!("../data/typestate.contract")),
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn defaults_cover_the_former_hardcoded_apis() {
        let c = Contracts::defaults();
        // Allocators (formerly `alloc_size`).
        assert_eq!(c.lookup("kmalloc").and_then(|c| c.alloc()), Some((&SizeExpr::Arg(0), 16)));
        assert_eq!(
            c.lookup("kmalloc_array").and_then(|c| c.alloc()),
            Some((&SizeExpr::Product(0, 1), 16))
        );
        assert_eq!(c.lookup("reallocarray").and_then(|c| c.alloc()), Some((&SizeExpr::Product(1, 2), 16)));
        // Deallocators (formerly `dealloc_ptr_arg`).
        assert_eq!(c.lookup("kfree").unwrap().effects, vec![Effect::Free { ptr: 0 }]);
        assert_eq!(c.lookup("kmem_cache_free").unwrap().effects, vec![Effect::Free { ptr: 1 }]);
        // User-copies (formerly `user_copy_kernel_arg`).
        assert_eq!(
            c.lookup("copy_from_user").unwrap().effects,
            vec![
                Effect::Write { ptr: 0, len: SizeExpr::Arg(2), fill: Fill::User, from: Some(1) },
                Effect::TaintSource { arg: 0, label: "user".into() },
            ]
        );
        assert_eq!(
            c.lookup("copy_to_user").unwrap().effects,
            vec![Effect::Read { ptr: 1, len: SizeExpr::Arg(2), sink: ReadSink::User }]
        );
        // An unknown API has no contract.
        assert!(c.lookup("definitely_not_an_api").is_none());
    }

    #[test]
    fn parses_all_size_forms_and_reports_errors() {
        let mut c = Contracts::default();
        c.parse_str("[a b]\nalloc size=arg0*arg1 align=8\n[d]\nwrite arg0 len=64 fill=user\n", "t")
            .unwrap();
        assert_eq!(c.lookup("a").and_then(|c| c.alloc()), Some((&SizeExpr::Product(0, 1), 8)));
        assert_eq!(c.lookup("b").and_then(|c| c.alloc()), Some((&SizeExpr::Product(0, 1), 8)));
        assert_eq!(
            c.lookup("d").unwrap().effects,
            vec![Effect::Write { ptr: 0, len: SizeExpr::Const(64), fill: Fill::User, from: None }]
        );
        // An effect before any header is an error.
        assert!(Contracts::default().parse_str("free arg0\n", "t").is_err());
        // An unknown effect is an error.
        assert!(Contracts::default().parse_str("[x]\nteleport arg0\n", "t").is_err());
    }

    #[test]
    fn provenance_lattice_labels_and_requirements() {
        let mut c = Contracts::default();
        c.parse_str(
            "prov foreign grants=read\nprov kernel grants=read,write\n\
             [mark_foreign]\nlabel arg0 foreign\n\
             [needs_writable]\nrequire arg0 write\n",
            "t",
        )
        .unwrap();
        // The lattice: `foreign` grants read but not write; `kernel` grants both.
        assert!(c.grants("foreign", "read"));
        assert!(!c.grants("foreign", "write"));
        assert!(c.grants("kernel", "write"));
        // An unlabelled region grants everything (sound default).
        assert!(c.grants("anything-unknown", "write"));
        // The effects.
        assert_eq!(
            c.lookup("mark_foreign").unwrap().effects,
            vec![Effect::Label { ptr: 0, label: "foreign".into() }]
        );
        assert_eq!(
            c.lookup("needs_writable").unwrap().effects,
            vec![Effect::Require { ptr: 0, cap: "write".into() }]
        );
    }

    #[test]
    fn taint_effects_parse() {
        let mut c = Contracts::default();
        c.parse_str(
            "[src]\ntaint-source arg1 user\n\
             [snk]\ntaint-sink arg0 user\n\
             [san]\ntaint-sanitize ret user\n",
            "t",
        )
        .unwrap();
        assert_eq!(
            c.lookup("src").unwrap().effects,
            vec![Effect::TaintSource { arg: 1, label: "user".into() }]
        );
        assert_eq!(
            c.lookup("snk").unwrap().effects,
            vec![Effect::TaintSink { arg: 0, label: "user".into() }]
        );
        // `ret` maps to the return-value sentinel.
        assert_eq!(
            c.lookup("san").unwrap().effects,
            vec![Effect::TaintSanitize { arg: RET_ARG, label: "user".into() }]
        );
    }

    #[test]
    fn typestate_effects_parse() {
        let mut c = Contracts::default();
        c.parse_str(
            "[open_h]\ntypestate-set ret file open\n\
             [close_h]\ntypestate-require-not arg0 file closed\ntypestate-set arg0 file closed\n\
             [use_h]\ntypestate-require arg0 perm checked\n",
            "t",
        )
        .unwrap();
        assert_eq!(
            c.lookup("open_h").unwrap().effects,
            vec![Effect::TypestateSet { arg: RET_ARG, protocol: "file".into(), state: "open".into() }]
        );
        assert_eq!(
            c.lookup("close_h").unwrap().effects,
            vec![
                Effect::TypestateRequire { arg: 0, protocol: "file".into(), state: "closed".into(), negate: true },
                Effect::TypestateSet { arg: 0, protocol: "file".into(), state: "closed".into() },
            ]
        );
        assert_eq!(
            c.lookup("use_h").unwrap().effects,
            vec![Effect::TypestateRequire { arg: 0, protocol: "perm".into(), state: "checked".into(), negate: false }]
        );
    }

    #[test]
    fn propagate_effect_parses() {
        let mut c = Contracts::default();
        c.parse_str("[sg_set_page]\npropagate arg0 from arg1\n", "t").unwrap();
        assert_eq!(
            c.lookup("sg_set_page").unwrap().effects,
            vec![Effect::Propagate { dst: 0, src: 1 }]
        );
        // Bad syntax (missing `from`) is an error.
        assert!(Contracts::default().parse_str("[x]\npropagate arg0 arg1\n", "t").is_err());
    }

    #[test]
    fn require_if_alias_parses() {
        let mut c = Contracts::default();
        c.parse_str("[aead_request_set_crypt]\nrequire-if-alias arg1 arg2 write\n", "t").unwrap();
        assert_eq!(
            c.lookup("aead_request_set_crypt").unwrap().effects,
            vec![Effect::RequireIfAlias { a: 1, b: 2, cap: "write".into() }]
        );
    }

    #[test]
    fn comments_and_blank_lines_are_ignored() {
        let mut c = Contracts::default();
        c.parse_str("# header\n\n[m]   # the allocator\nalloc size=arg0 align=16 # 16-byte\n", "t")
            .unwrap();
        assert_eq!(c.lookup("m").and_then(|c| c.alloc()), Some((&SizeExpr::Arg(0), 16)));
    }
}
