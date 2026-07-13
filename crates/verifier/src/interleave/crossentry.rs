use super::*;

/// A witnessed **cross-entry (cross-syscall) use-after-free / double-free**: one attacker-reachable
/// entry frees an object reachable from a shared *persistent* root (a global — an fd table, a
/// device pointer, …) without clearing that root, and a *separate* entry, with no common caller,
/// later dereferences (or frees) the same root. Unlike the cross-*thread* search this is a
/// **sequential** composition — the entries need not overlap in time (locks between them do not
/// order them); the attacker simply invokes the freeing syscall (`close`) and then the using one
/// (`read`/`ioctl`). The dangling shared root is what carries the freed pointer between them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CrossEntryWitness {
    /// The dangling global-rooted object's class.
    pub location: String,
    /// The entries: the one that frees, and the one that later uses (or the second free).
    pub entries: (String, String),
    /// `true` if the second entry also frees it (cross-entry double-free), else a use-after-free.
    pub double_free: bool,
}

/// Whether a class is rooted at a **global** — the only state that persists between independent
/// syscall entries. A parameter-derived object does not survive to another entry (no common
/// caller passes it), so it is excluded. Matches `g:name@off` and any `deref:` chased from one.
pub(crate) fn is_global_rooted(class: &str) -> bool {
    let mut core = class;
    while let Some(rest) = core.strip_prefix("deref:") {
        core = rest;
    }
    core.starts_with("g:")
}

/// The **root slot** of a dereferenced global class: `deref:g:obj@0` → `g:obj@0`. A write to this
/// slot in the freeing entry means it reassigned/cleared the global (no dangling) — we then skip.
pub(crate) fn root_slot(class: &str) -> &str {
    class.strip_prefix("deref:").unwrap_or(class)
}

/// The abstract lifetime of a global-rooted object in the cross-entry **sequence-closure** model.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum RootLife {
    /// Allocated / valid (the initial state, and after a reassign/re-open).
    Live,
    /// Freed but the global slot still points at it — a dangling handle carried between syscalls.
    Dangling,
}

/// The effect of one event on a given `root` object: **free** (→Dangling), **clear** (a reassign of
/// the root slot → Live, the intervening re-open/re-check), or **use** (a deref — an error while
/// Dangling). `None` = the event does not touch this root. A refcount put is a free (a release may
/// drop the last reference); a write *through* the object is a use, a write *to the slot* is a clear.
pub(crate) fn root_effect(e: &Event, root: &str) -> Option<RootEff> {
    let slot = root_slot(root);
    match e {
        Event::Free(x) | Event::RefPut(x) if x == root => Some(RootEff::Free),
        // A write to the root SLOT (checked first) reassigns the global → clears the dangling.
        Event::Write(x) | Event::Rmw(x) if x == slot => Some(RootEff::Clear),
        // A write THROUGH the object (its own deref class) is a use.
        Event::Write(x) | Event::Rmw(x) if x == root => Some(RootEff::Use),
        Event::Read(x) | Event::DepRead(x) | Event::RefGet(x) if x == root => Some(RootEff::Use),
        _ => None,
    }
}

pub(crate) enum RootEff {
    Free,
    Clear,
    Use,
}

/// Simulate one entry's ordered effect on `root` from `start`, returning the output state and
/// whether — **in program order** — a use-after-free (use while Dangling) or a double-free (free
/// while Dangling) occurs. Order-sensitivity is what lets an entry that re-checks/re-opens *before*
/// using (`if (!x) x = open(); use(x)`) not be flagged, unlike the old order-insensitive fold.
pub(crate) fn simulate_root(events: &[Event], root: &str, start: RootLife) -> (RootLife, bool, bool) {
    let mut st = start;
    let (mut uaf, mut double_free) = (false, false);
    for e in events {
        match root_effect(e, root) {
            Some(RootEff::Free) => {
                if st == RootLife::Dangling {
                    double_free = true;
                }
                st = RootLife::Dangling;
            }
            Some(RootEff::Clear) => st = RootLife::Live,
            Some(RootEff::Use) => uaf |= st == RootLife::Dangling,
            None => {}
        }
    }
    (st, uaf, double_free)
}

/// Whole-program **cross-entry use-after-free / double-free** search — a **sequence-closure** over
/// entry compositions (not just pairs). Each global-rooted object is an abstract state machine
/// (`Live`/`Dangling`); an entry's ordered effect frees (→Dangling), reassigns (→Live), or uses it.
/// A fixpoint computes every state the object can be in when a syscall STARTS (over all attacker
/// sequences); an entry that then uses (UAF) or re-frees (double-free) it while Dangling is a bug.
/// This (a) catches multi-syscall chains where the dangling state is only reachable after several
/// entries and the double-free-by-calling-the-same-syscall-twice case, and (b) removes the false
/// positive where the using entry re-validates the handle before use (an intervening re-open). The
/// global-root restriction keeps only persistent shared state (a param object cannot survive to an
/// unrelated entry). Still a bug-finding candidate (no data-flow guard modelling).
pub fn find_cross_entry_uaf(entries: &[Thread]) -> Vec<CrossEntryWitness> {
    use std::collections::BTreeSet;
    // Every global-rooted object class freed/used anywhere is a candidate root.
    let mut roots: BTreeSet<String> = BTreeSet::new();
    for t in entries {
        for e in &t.events {
            let cls = match e {
                Event::Free(x) | Event::RefPut(x) | Event::Read(x) | Event::DepRead(x)
                | Event::RefGet(x) | Event::Write(x) | Event::Rmw(x) => Some(x),
                _ => None,
            };
            if let Some(c) = cls {
                if is_global_rooted(c) {
                    roots.insert(c.clone());
                }
            }
        }
    }
    let mut out = Vec::new();
    let mut seen: std::collections::HashSet<(String, bool)> = std::collections::HashSet::new();
    for root in &roots {
        // The entries that leave the object Dangling (free it without reassigning the slot). If none,
        // the object is never freed → no cross-entry UAF/double-free.
        let freers: Vec<usize> = entries
            .iter()
            .enumerate()
            .filter(|(_, t)| simulate_root(&t.events, root, RootLife::Live).0 == RootLife::Dangling)
            .map(|(i, _)| i)
            .collect();
        if freers.is_empty() {
            continue;
        }
        for (j, t) in entries.iter().enumerate() {
            // A cross-entry bug needs a *different* entry to have left the object dangling before
            // `j` runs (the attacker invokes that syscall, then `j`). The same syscall twice is
            // excluded — a re-invocation on the same freed handle is normally rejected by the fd/
            // handle layer (`EBADF`), so it is not treated as a cross-entry double-free here.
            let Some(&i) = freers.iter().find(|&&f| f != j) else {
                continue;
            };
            // Simulate `j` starting Dangling: a use before it re-validates is a UAF; a second free
            // is a double-free. The order-sensitivity means a `j` that re-opens the handle first
            // (Clear → Live) is NOT flagged — the precision the pairwise fold lacked.
            let (_, uaf, double_free) = simulate_root(&t.events, root, RootLife::Dangling);
            if uaf && seen.insert((root.clone(), false)) {
                out.push(CrossEntryWitness {
                    location: root.clone(),
                    entries: (entries[i].name.clone(), t.name.clone()),
                    double_free: false,
                });
            }
            if double_free && seen.insert((root.clone(), true)) {
                out.push(CrossEntryWitness {
                    location: root.clone(),
                    entries: (entries[i].name.clone(), t.name.clone()),
                    double_free: true,
                });
            }
        }
    }
    out.sort_by(|a, b| a.location.cmp(&b.location));
    out
}

/// A witnessed **cross-entry (cross-syscall) typestate violation**: one entry drives a global-
/// rooted object into a protocol state (e.g. `closed`/`freed`) and another, independently reachable
/// entry uses it while forbidding that state (a `require-not`). Invoking the first syscall then the
/// second is a use-after-close / use-after-free across the object's persistent global handle — the
/// typestate analogue of [`CrossEntryWitness`], carrying the full protocol/state provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CrossEntryTypestateWitness {
    /// The global-rooted object's class.
    pub location: String,
    /// The interned protocol id (shared module-wide, so it matches across entries).
    pub protocol: u32,
    /// The interned forbidden-state id.
    pub state: u32,
    /// The entries: the one that sets the forbidden state, and the one that uses it.
    pub entries: (String, String),
}

/// Parse a `Typestate` event payload `k\u{1f}class\u{1f}proto\u{1f}state` → `(k, class, proto,
/// state)`. `None` on a malformed payload.
pub(crate) fn parse_typestate(payload: &str) -> Option<(u8, &str, u32, u32)> {
    let mut it = payload.split('\u{1f}');
    let k: u8 = it.next()?.parse().ok()?;
    let class = it.next()?;
    let proto: u32 = it.next()?.parse().ok()?;
    let state: u32 = it.next()?.parse().ok()?;
    Some((k, class, proto, state))
}

/// Whole-program **cross-entry typestate** search: a `set` of a `(global-object, protocol, state)`
/// in one entry paired with a `require-not` of the same triple in a *different* entry — invoking the
/// setter then the user is a cross-syscall use-after-state (use-after-close / use-after-free on the
/// object's persistent global handle). Restricted to global-rooted objects (streamed as such), so a
/// parameter-local resource never fires. A bug-finding heuristic — it does
/// not model an ordering guard (a re-open/re-check) the second syscall might perform.
pub fn find_cross_entry_typestate(entries: &[Thread]) -> Vec<CrossEntryTypestateWitness> {
    // Per entry: the (class, proto, state) it sets, and the ones it requires-not (the use side).
    type Triple = (String, u32, u32);
    let (sets, reqnots): (Vec<Vec<Triple>>, Vec<Vec<Triple>>) = entries
        .iter()
        .map(|t| {
            let (mut s, mut r) = (Vec::new(), Vec::new());
            for e in &t.events {
                if let Event::Typestate(p) = e {
                    if let Some((k, class, proto, state)) = parse_typestate(p) {
                        match k {
                            0 => s.push((class.to_string(), proto, state)),
                            2 => r.push((class.to_string(), proto, state)),
                            _ => {}
                        }
                    }
                }
            }
            (s, r)
        })
        .unzip();
    let mut out = Vec::new();
    let mut seen: std::collections::HashSet<Triple> = std::collections::HashSet::new();
    for i in 0..entries.len() {
        for j in 0..entries.len() {
            if i == j {
                continue;
            }
            for set in &sets[i] {
                if reqnots[j].contains(set) && seen.insert(set.clone()) {
                    out.push(CrossEntryTypestateWitness {
                        location: set.0.clone(),
                        protocol: set.1,
                        state: set.2,
                        entries: (entries[i].name.clone(), entries[j].name.clone()),
                    });
                }
            }
        }
    }
    out.sort_by(|a, b| a.location.cmp(&b.location));
    out
}
