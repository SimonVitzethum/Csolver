//! Recovering pointee types from LLVM debug-info metadata (`!DI…`).
//!
//! LLVM's opaque `ptr` type erases *what* a pointer points to — so a reference
//! parameter carries no size, and accesses through it cannot be bounds-checked
//! (the dominant `UNKNOWN` on debug IR). But when the module is compiled with
//! debug info (`-g` / `-C debuginfo=2`, standard across rustc, clang, swiftc),
//! the type is still present as *metadata*: the DWARF type graph embedded in the
//! textual IR. This module reads it back.
//!
//! The chain, per function parameter:
//! ```text
//! define … !dbg !N                          ; N = the DISubprogram
//! !V = !DILocalVariable(arg: k, scope: !N, type: !T)
//! !T = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut T", baseType: !P, …)
//! !P = !DICompositeType(… size: <bits>)     ; the pointee, sized in bits
//! ```
//!
//! ## Soundness — validity is language-specific
//!
//! A pointee *size* alone does not make a pointer valid: a C `T*` may dangle. A
//! contract (a live, dereferenceable region) is synthesized **only** for pointer
//! kinds the source language guarantees valid:
//!
//! - a Rust reference — `DW_TAG_pointer_type` whose name begins `&` (`&T` /
//!   `&mut T`; `&mut` ⇒ writable);
//! - a C++ reference — `DW_TAG_reference_type` (`T&`).
//!
//! A raw pointer (`*const T`, C/C++ `T*`, `DW_TAG_pointer_type` not named `&`) is
//! deliberately *not* contracted: its validity is the programmer's obligation,
//! and assuming it would be a false-PASS hole. So the recovery is sound across
//! languages, granting a contract exactly where the type system already does.

use std::collections::HashMap;

/// A parsed subset of the debug-info type graph, keyed by metadata id.
#[derive(Debug, Clone, Default)]
pub(crate) struct DebugInfo {
    nodes: HashMap<u32, DiNode>,
    /// `(subprogram id, 1-based arg index) -> parameter's type node id`.
    params: HashMap<(u32, u32), u32>,
}

#[derive(Debug, Clone)]
enum DiNode {
    /// A `DW_TAG_pointer_type`: its pointee and whether it is a valid reference
    /// (`&T`/`&mut T`, by the leading `&` in the name) and if so writable.
    Pointer { base: u32, reference: bool, writable: bool },
    /// A `DW_TAG_reference_type` (C++ `T&`): always a valid reference.
    Reference { base: u32, writable: bool },
    /// A struct/union (`DICompositeType`): its `elements` metadata-list id (the
    /// members) and byte size.
    Composite { elements: Option<u32>, size_bytes: Option<u64> },
    /// A struct member (`DIDerivedType(tag: DW_TAG_member)`): its byte offset in
    /// the enclosing struct and its type.
    Member { offset_bytes: u64, base: u32 },
    /// A `!{…}` metadata tuple (a struct's element list): the member node ids.
    Tuple(Vec<u32>),
    /// Any other sized type node (basic type / typedef|qualifier chain): its byte
    /// size and, for a typedef/qualifier, the underlying type to follow.
    Sized { size_bytes: Option<u64>, follows: Option<u32> },
}

/// A pointer parameter's recovered contract: pointee byte size + write access.
pub(crate) struct RefContract {
    pub size: u64,
    pub writable: bool,
}

impl DebugInfo {
    /// The recovered contract for parameter `arg` (1-based) of the function
    /// whose `DISubprogram` id is `subprogram`, when that parameter is a *valid
    /// reference* of statically-known pointee size. `None` for a raw pointer, an
    /// unknown-size pointee, or missing debug info.
    pub(crate) fn param_ref(&self, subprogram: u32, arg: u32) -> Option<RefContract> {
        let ty = *self.params.get(&(subprogram, arg))?;
        let (base, writable) = match self.nodes.get(&ty)? {
            DiNode::Pointer { base, reference: true, writable } => (*base, *writable),
            DiNode::Reference { base, writable } => (*base, *writable),
            _ => return None, // a raw pointer / non-reference: not contracted.
        };
        Some(RefContract { size: self.sized_bytes(base)?, writable })
    }

    /// Follow typedef/qualifier chains to a concrete byte size (a bounded walk).
    fn sized_bytes(&self, mut id: u32) -> Option<u64> {
        for _ in 0..16 {
            match self.nodes.get(&id)? {
                DiNode::Sized { size_bytes: Some(n), .. } => return Some(*n),
                DiNode::Sized { size_bytes: None, follows: Some(next) } => id = *next,
                DiNode::Composite { size_bytes: Some(n), .. } => return Some(*n),
                // A pointer/reference *pointee* that is itself a pointer is 8
                // bytes (a thin pointer's storage), the sound size for it.
                DiNode::Pointer { .. } | DiNode::Reference { .. } => return Some(8),
                _ => return None,
            }
        }
        None
    }

    /// The **pointee** type node of a reference parameter — the struct a `&mut
    /// StructT` param points at — so field loads through it can resolve members.
    pub(crate) fn param_pointee(&self, subprogram: u32, arg: u32) -> Option<u32> {
        let ty = *self.params.get(&(subprogram, arg))?;
        match self.nodes.get(&ty)? {
            DiNode::Pointer { base, reference: true, .. } | DiNode::Reference { base, .. } => {
                Some(*base)
            }
            _ => None,
        }
    }

    /// The recovered contract for the member of struct type `struct_id` at byte
    /// `offset`, when that member is a *valid reference* (`&T`/`&mut T`/`T&`) —
    /// so a `load ptr, gep(struct, offset)` yields a known valid reference. The
    /// enclosing struct type may itself be behind a typedef/qualifier chain.
    pub(crate) fn member_ref(&self, struct_id: u32, offset: u64) -> Option<RefContract> {
        let elements = self.composite_elements(struct_id)?;
        let DiNode::Tuple(members) = self.nodes.get(&elements)? else { return None };
        for &m in members {
            if let Some(DiNode::Member { offset_bytes, base }) = self.nodes.get(&m) {
                if *offset_bytes == offset {
                    let (pointee, writable) = match self.nodes.get(base)? {
                        DiNode::Pointer { base, reference: true, writable } => (*base, *writable),
                        DiNode::Reference { base, writable } => (*base, *writable),
                        _ => return None,
                    };
                    return Some(RefContract { size: self.sized_bytes(pointee)?, writable });
                }
            }
        }
        None
    }

    /// The elements-list id of a composite type, following typedef/qualifier
    /// chains to reach the `DICompositeType`.
    fn composite_elements(&self, mut id: u32) -> Option<u32> {
        for _ in 0..16 {
            match self.nodes.get(&id)? {
                DiNode::Composite { elements, .. } => return *elements,
                DiNode::Sized { follows: Some(next), .. } => id = *next,
                _ => return None,
            }
        }
        None
    }
}

/// Parse the debug-info metadata graph out of a textual `.ll` module. Lines that
/// are not `!DI…` definitions (or that do not parse) are ignored — debug info is
/// advisory, never required.
pub(crate) fn parse(src: &str) -> DebugInfo {
    let mut di = DebugInfo::default();
    for line in src.lines() {
        let line = line.trim_start();
        // A metadata definition: `!123 = !DI…(…)`.
        let Some(rest) = line.strip_prefix('!') else { continue };
        let Some((id_str, body)) = rest.split_once(" = ") else { continue };
        let Ok(id) = id_str.parse::<u32>() else { continue };

        if let Some(args) = tag_body(body, "!DILocalVariable(") {
            // `arg: k, scope: !N, type: !T` — only parameters (those with `arg:`).
            if let (Some(arg), Some(scope), Some(ty)) =
                (field_int(args, "arg:"), field_ref(args, "scope:"), field_ref(args, "type:"))
            {
                di.params.insert((scope, arg as u32), ty);
            }
        } else if let Some(args) = tag_body(body, "!DIDerivedType(") {
            insert_derived(&mut di, id, args);
        } else if let Some(args) = tag_body(body, "!DICompositeType(") {
            // A struct/union: its byte size and members-list (`elements: !L`).
            di.nodes.insert(
                id,
                DiNode::Composite {
                    elements: field_ref(args, "elements:"),
                    size_bytes: bits_to_bytes(args),
                },
            );
        } else if let Some(args) = tag_body(body, "!DIBasicType(") {
            di.nodes.insert(id, DiNode::Sized { size_bytes: bits_to_bytes(args), follows: None });
        } else if let Some(members) = tuple_refs(body) {
            // A `!{!a, !b, …}` metadata tuple — a struct's element list.
            di.nodes.insert(id, DiNode::Tuple(members));
        }
    }
    di
}

/// Parse a bare metadata tuple `!{!a, !b, …}` into its element ids, or `None` if
/// `body` is not a tuple (or holds non-`!N` entries, in which case those slots
/// are simply skipped — a `null` member is harmless).
fn tuple_refs(body: &str) -> Option<Vec<u32>> {
    let inner = body.strip_prefix("!{")?.strip_suffix('}')?;
    Some(
        inner
            .split(',')
            .filter_map(|e| e.trim().strip_prefix('!')?.parse::<u32>().ok())
            .collect(),
    )
}

/// A `DW_TAG_pointer_type` / `reference_type` / typedef|qualifier under
/// `!DIDerivedType(tag: …, …)`.
fn insert_derived(di: &mut DebugInfo, id: u32, args: &str) {
    let tag = field_word(args, "tag:");
    let base = field_ref(args, "baseType:");
    match tag {
        Some("DW_TAG_pointer_type") => {
            let name = field_str(args, "name:");
            // A Rust reference's DWARF name begins `&` (`&T` / `&mut T`); a raw
            // pointer is `*const …`/`*mut …` or unnamed.
            let reference = name.is_some_and(|n| n.starts_with('&'));
            let writable = name.is_some_and(|n| n.starts_with("&mut"));
            if let Some(base) = base {
                di.nodes.insert(id, DiNode::Pointer { base, reference, writable });
            }
        }
        Some("DW_TAG_reference_type") => {
            if let Some(base) = base {
                di.nodes.insert(id, DiNode::Reference { base, writable: true });
            }
        }
        // A struct member: its byte offset (`offset:` is in bits) and type.
        Some("DW_TAG_member") => {
            if let Some(base) = base {
                let offset_bytes = field_int(args, "offset:").unwrap_or(0).max(0) as u64 / 8;
                di.nodes.insert(id, DiNode::Member { offset_bytes, base });
            }
        }
        // A typedef / `const`/`volatile` qualifier: transparent to the size,
        // follow its base. A pointer-sized derived type carries its own size.
        _ => {
            di.nodes.insert(
                id,
                DiNode::Sized { size_bytes: bits_to_bytes(args), follows: base },
            );
        }
    }
}

/// The argument list inside `!DIXxx( … )`, if `body` starts with `open`.
fn tag_body<'a>(body: &'a str, open: &str) -> Option<&'a str> {
    body.strip_prefix(open)?.strip_suffix(')')
}

/// `field: N` — an integer field.
fn field_int(args: &str, field: &str) -> Option<i64> {
    field_raw(args, field)?.parse().ok()
}

/// `field: !N` — a metadata reference field.
fn field_ref(args: &str, field: &str) -> Option<u32> {
    field_raw(args, field)?.strip_prefix('!')?.parse().ok()
}

/// `field: word` — a bare-word field (e.g. `tag: DW_TAG_pointer_type`).
fn field_word<'a>(args: &'a str, field: &str) -> Option<&'a str> {
    field_raw(args, field)
}

/// `field: "quoted"` — a string field, unquoted.
fn field_str<'a>(args: &'a str, field: &str) -> Option<&'a str> {
    let v = find_field(args, field)?;
    let v = v.strip_prefix('"')?;
    Some(&v[..v.find('"')?])
}

/// A `size:` field (in bits) converted to whole bytes.
fn bits_to_bytes(args: &str) -> Option<u64> {
    let bits: u64 = field_raw(args, "size:")?.parse().ok()?;
    Some(bits / 8)
}

/// The raw token of `field:` — up to the next comma or end, trimmed. Handles a
/// `"quoted, with commas"` value by not splitting inside the quotes.
fn field_raw<'a>(args: &'a str, field: &str) -> Option<&'a str> {
    let v = find_field(args, field)?;
    if let Some(after) = v.strip_prefix('"') {
        // up to and including the closing quote
        let end = after.find('"')? + 2;
        return Some(v[..end].trim());
    }
    let end = v.find(',').unwrap_or(v.len());
    Some(v[..end].trim())
}

/// The substring just after `field` (a `key:` occurring at a token boundary).
fn find_field<'a>(args: &'a str, field: &str) -> Option<&'a str> {
    let mut from = 0;
    while let Some(rel) = args[from..].find(field) {
        let at = from + rel;
        // Require a boundary before the key so `type:` does not match inside
        // `templateParams:` etc.
        let before_ok = at == 0 || matches!(args.as_bytes()[at - 1], b' ' | b'(' | b',');
        if before_ok {
            return Some(args[at + field.len()..].trim_start());
        }
        from = at + field.len();
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    const SRC: &str = r#"
define float @f(ptr align 8 %self) !dbg !7 {
start:
  ret float 0.0
}
!7 = distinct !DISubprogram(name: "f", scope: !9)
!42 = !DILocalVariable(name: "self", arg: 1, scope: !7, file: !8, line: 104, type: !39)
!39 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut lib::Rand32", baseType: !9, size: 64, align: 64)
!9 = !DICompositeType(tag: DW_TAG_structure_type, name: "Rand32", size: 128, align: 64)
!40 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "*const u8", baseType: !41, size: 64)
!41 = !DIBasicType(name: "u8", size: 8, encoding: DW_ATE_unsigned)
!50 = !DILocalVariable(name: "p", arg: 2, scope: !7, type: !40)
"#;

    #[test]
    fn recovers_rust_mut_reference_pointee_size() {
        let di = parse(SRC);
        let c = di.param_ref(7, 1).expect("&mut Rand32 param");
        assert_eq!(c.size, 16, "Rand32 is 128 bits = 16 bytes");
        assert!(c.writable, "&mut is writable");
    }

    #[test]
    fn raw_pointer_param_is_not_contracted() {
        let di = parse(SRC);
        // `*const u8` (arg 2) is a raw pointer — validity not guaranteed, so no
        // contract (recovering one would be a false-PASS hole).
        assert!(di.param_ref(7, 2).is_none());
    }

    const STRUCT_SRC: &str = r#"
!7 = distinct !DISubprogram(name: "f")
!42 = !DILocalVariable(name: "self", arg: 1, scope: !7, type: !39)
!39 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut Wrap", baseType: !9, size: 64)
!9 = !DICompositeType(tag: DW_TAG_structure_type, name: "Wrap", size: 128, elements: !12)
!12 = !{!13, !15}
!13 = !DIDerivedType(tag: DW_TAG_member, name: "tag", baseType: !14, size: 64, offset: 0)
!14 = !DIBasicType(name: "u64", size: 64)
!15 = !DIDerivedType(tag: DW_TAG_member, name: "inner", baseType: !16, size: 64, offset: 64)
!16 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&u8", baseType: !17, size: 64)
!17 = !DIBasicType(name: "u8", size: 8)
"#;

    #[test]
    fn resolves_reference_struct_member_at_offset() {
        let di = parse(STRUCT_SRC);
        let s = di.param_pointee(7, 1).expect("&mut Wrap pointee");
        // Member `inner: &u8` is at byte offset 8 (bit offset 64).
        let c = di.member_ref(s, 8).expect("reference member at offset 8");
        assert_eq!(c.size, 1, "&u8 pointee is 1 byte");
        assert!(!c.writable, "&u8 is read-only");
        // Member `tag: u64` at offset 0 is not a reference → no contract.
        assert!(di.member_ref(s, 0).is_none());
    }
}
