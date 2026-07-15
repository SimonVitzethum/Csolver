use super::*;

pub(crate) fn parse_effect(line: &str) -> Result<Effect, String> {
    let mut it = line.split_whitespace();
    let kind = it.next().ok_or("empty effect")?;
    let rest: Vec<&str> = it.collect();
    match kind {
        "alloc" => {
            let size = parse_kv_size(&rest, "size")?;
            let align = parse_kv_u32(&rest, "align")?;
            Ok(Effect::Alloc { size, align, external: false })
        }
        // `ioremap`-style MMIO mapping: an allocation of known size whose bytes are already
        // initialized by hardware (a register read is not an uninitialized-read bug).
        "mmio" => {
            let size = parse_kv_size(&rest, "size")?;
            let align = parse_kv_u32(&rest, "align")?;
            Ok(Effect::Alloc { size, align, external: true })
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
            let ptr = parse_arg_or_ret(rest.first().copied().unwrap_or(""))?;
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
        // `typestate-yield <protocol> <from> <to>` (protocol-wide, no argument).
        "typestate-yield" => {
            let protocol = rest.first().copied().ok_or("`typestate-yield` needs a protocol")?.to_string();
            let from = rest.get(1).copied().ok_or("`typestate-yield` needs a from-state")?.to_string();
            let to = rest.get(2).copied().ok_or("`typestate-yield` needs a to-state")?.to_string();
            Ok(Effect::TypestateYield { protocol, from, to })
        }
        // `refcount-inc arg<k> <protocol>` / `refcount-inc-checked …` / `refcount-dec …`.
        "refcount-inc" | "refcount-inc-checked" | "refcount-dec" => {
            let arg = parse_arg(rest.first().copied().unwrap_or(""))?;
            let protocol = rest.get(1).copied().ok_or("`refcount` needs a protocol")?.to_string();
            Ok(Effect::Refcount {
                arg,
                protocol,
                dec: kind == "refcount-dec",
                checked: kind == "refcount-inc-checked",
            })
        }
        // `spawn arg<k>` (child function pointer) and `join` (no arguments).
        "spawn" => Ok(Effect::Spawn { arg: parse_arg(rest.first().copied().unwrap_or(""))? }),
        "join" => Ok(Effect::Join),
        // `cas arg<k>` — a compare-and-swap on the location pointed to by arg k.
        "cas" => Ok(Effect::Cas { arg: parse_arg(rest.first().copied().unwrap_or(""))? }),
        // `barrier [full|write|read] [arg<k>]` — a full (default), write, or read memory
        // barrier, optionally also accessing the location at arg k (a `smp_store_release` /
        // `smp_load_acquire`: the flag write/read the fence orders, so the message-passing
        // handoff is modelled, not just the ordering). `write` ⇒ the access is a write
        // (release store), `read` ⇒ a read (acquire load).
        "barrier" => {
            let kind = match rest.first().copied() {
                None | Some("full") => 0,
                Some("write") => 1,
                Some("read") => 2,
                Some(other) => return Err(format!("unknown barrier kind `{other}`")),
            };
            let access = match rest.get(1).copied() {
                None => None,
                Some(tok) => Some(parse_arg(tok)?),
            };
            Ok(Effect::Barrier { kind, access })
        }
        // `lock-acquire arg<k> [spin]` — an unconditional lock acquire; `spin` marks
        // atomic (preemption-off) context. `blocking`, `irq-disable`/`irq-enable`,
        // `rcu-read-lock`/`rcu-read-unlock` and `percpu-ptr` take no arguments.
        "lock-acquire" => {
            let arg = parse_arg(rest.first().copied().unwrap_or(""))?;
            let spin = match rest.get(1).copied() {
                None => false,
                Some("spin") => true,
                Some(other) => return Err(format!("unknown lock-acquire flag `{other}`")),
            };
            Ok(Effect::LockAcquire { arg, spin })
        }
        "blocking" => Ok(Effect::Blocking),
        "irq-disable" => Ok(Effect::IrqDisable),
        "irq-enable" => Ok(Effect::IrqEnable),
        "rcu-read-lock" => Ok(Effect::RcuReadLock),
        "rcu-read-unlock" => Ok(Effect::RcuReadUnlock),
        "percpu-ptr" => Ok(Effect::PercpuPtr),
        // `container-lookup arg<k>` and `global-lookup <root>` — cross-syscall lookup naming.
        "container-lookup" => {
            Ok(Effect::ContainerLookup { arg: parse_arg(rest.first().copied().unwrap_or(""))? })
        }
        "global-lookup" => {
            let root = rest.first().copied().ok_or("`global-lookup` needs a root name")?.to_string();
            Ok(Effect::GlobalLookup { root })
        }
        // `typestate-leak <protocol> <state>` (registers a leak state; checked at returns).
        "typestate-leak" => {
            let protocol = rest.first().copied().ok_or("`typestate-leak` needs a protocol")?.to_string();
            let state = rest.get(1).copied().ok_or("`typestate-leak` needs a state")?.to_string();
            Ok(Effect::TypestateLeak { protocol, state })
        }
        other => Err(format!("unknown effect `{other}`")),
    }
}

/// Look up a `key=value` token in the remaining words.
pub(crate) fn kv<'a>(rest: &[&'a str], key: &str) -> Option<&'a str> {
    rest.iter().find_map(|w| w.strip_prefix(key)?.strip_prefix('='))
}

pub(crate) fn parse_kv_u32(rest: &[&str], key: &str) -> Result<u32, String> {
    kv(rest, key)
        .ok_or_else(|| format!("missing `{key}=`"))?
        .parse()
        .map_err(|_| format!("`{key}=` expects an integer"))
}

pub(crate) fn parse_kv_size(rest: &[&str], key: &str) -> Result<SizeExpr, String> {
    parse_size(kv(rest, key).ok_or_else(|| format!("missing `{key}=`"))?)
}

/// `arg3` → 3.
pub(crate) fn parse_arg(tok: &str) -> Result<usize, String> {
    tok.strip_prefix("arg")
        .and_then(|n| n.parse().ok())
        .ok_or_else(|| format!("expected `arg<k>`, got `{tok}`"))
}

/// The taint-target sentinel for a call's **return value** (`ret`), used by
/// `taint-source`/`taint-sanitize` in place of an `arg<k>` index.
pub const RET_ARG: usize = usize::MAX;

/// Parse a taint target: `arg<k>` or the literal `ret` (the call's result value).
pub(crate) fn parse_arg_or_ret(tok: &str) -> Result<usize, String> {
    if tok == "ret" {
        Ok(RET_ARG)
    } else {
        parse_arg(tok)
    }
}

/// `arg0`, `arg0*arg1`, or a decimal integer.
pub(crate) fn parse_size(tok: &str) -> Result<SizeExpr, String> {
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
