//! A focused DWARF (v4/v5, 32-bit) reader that recovers, per function, the
//! **pointee byte size of each pointer parameter** — enough to give a binary's
//! pointer parameters a typed size (the analysis's `assume_valid_params` path),
//! which the machine code alone cannot supply. Not a general DWARF library: only
//! the `DW_TAG_subprogram` → `DW_TAG_formal_parameter` → `DW_TAG_pointer_type` →
//! pointee-size path, over the forms `clang -g` emits. Anything unrecognised is
//! skipped and yields no hint (sound — a missing hint only lowers precision).

#![allow(non_upper_case_globals)] // DWARF `DW_TAG_*` / `DW_AT_*` spec names

use crate::Image;
use std::collections::HashMap;

// --- DWARF constants (subset) ---------------------------------------------
const DW_TAG_subprogram: u64 = 0x2e;
const DW_TAG_formal_parameter: u64 = 0x05;
const DW_TAG_pointer_type: u64 = 0x0f;
const DW_TAG_typedef: u64 = 0x16;
const DW_TAG_const_type: u64 = 0x26;
const DW_TAG_volatile_type: u64 = 0x35;
const DW_TAG_restrict_type: u64 = 0x37;

const DW_AT_name: u64 = 0x03;
const DW_AT_byte_size: u64 = 0x0b;
const DW_AT_type: u64 = 0x49;
const DW_AT_str_offsets_base: u64 = 0x72;

/// For each function name, the pointee byte size of each parameter (parallel to
/// the parameter list; `None` for a non-pointer parameter or an unresolved one).
pub fn parameter_pointee_sizes(image: &Image, file: &[u8]) -> HashMap<String, Vec<Option<u64>>> {
    let (Some(info), Some(abbrev)) = (
        image.section_bytes_by_name(".debug_info", file),
        image.section_bytes_by_name(".debug_abbrev", file),
    ) else {
        return HashMap::new();
    };
    let str_offsets = image.section_bytes_by_name(".debug_str_offsets", file).unwrap_or(&[]);
    let debug_str = image.section_bytes_by_name(".debug_str", file).unwrap_or(&[]);
    // In a relocatable object the `.debug_str_offsets` slots are ZERO in the file and
    // the real string offset is the relocation ADDEND (against `.debug_str`). Map each
    // patched slot offset → addend, so `resolve_strx` uses it instead of the raw 0.
    let str_reloc = section_addends(image, ".debug_str_offsets");
    let mut out = HashMap::new();
    let mut cu_start = 0usize;
    // Walk each compilation unit; a malformed one aborts just that unit.
    while cu_start + 4 <= info.len() {
        match parse_cu(info, abbrev, str_offsets, debug_str, &str_reloc, cu_start, &mut out) {
            Some(next) if next > cu_start => cu_start = next,
            _ => break,
        }
    }
    out
}

/// `slot offset → addend` for the relocations patching the named section (the DWARF
/// string-offset slots are relocated in a `.o`; empty for a linked image).
pub(crate) fn section_addends(image: &Image, name: &str) -> HashMap<u64, i64> {
    let Some(idx) = image.sections.iter().position(|s| s.name == name) else {
        return HashMap::new();
    };
    image
        .relocations
        .iter()
        .filter(|(patched, _)| *patched == idx)
        .flat_map(|(_, rs)| rs.iter())
        .map(|r| (r.offset, r.addend))
        .collect()
}

/// One abbreviation: its tag, whether it has children, and its `(attr, form,
/// implicit_const)` list.
struct Abbrev {
    tag: u64,
    has_children: bool,
    attrs: Vec<(u64, u64, i64)>,
}

fn parse_abbrev_table(data: &[u8], mut p: usize) -> HashMap<u64, Abbrev> {
    let mut table = HashMap::new();
    while let Some((code, np)) = uleb(data, p) {
        p = np;
        if code == 0 {
            break; // end of this abbrev table
        }
        let Some((tag, np)) = uleb(data, p) else { break };
        p = np;
        let Some(&has_children) = data.get(p) else { break };
        p += 1;
        let mut attrs = Vec::new();
        loop {
            let Some((attr, np)) = uleb(data, p) else { return table };
            let Some((form, np2)) = uleb(data, np) else { return table };
            p = np2;
            if attr == 0 && form == 0 {
                break; // end of this abbrev's attribute list
            }
            let mut implicit = 0i64;
            if form == 0x21 {
                // DW_FORM_implicit_const: an SLEB value stored in the abbrev.
                let Some((v, np3)) = sleb(data, p) else { return table };
                implicit = v;
                p = np3;
            }
            attrs.push((attr, form, implicit));
        }
        table.insert(code, Abbrev { tag, has_children: has_children != 0, attrs });
    }
    table
}

/// A DIE's collected data, keyed by its `.debug_info` offset.
#[derive(Default, Clone)]
struct DieInfo {
    tag: u64,
    type_ref: Option<usize>,
    byte_size: Option<u64>,
    name_strx: Option<u64>,
}

/// Parse one compilation unit starting at `cu_start`; fill `out` with its functions.
/// Returns the offset of the next unit (or `None` on a malformed header).
#[allow(clippy::too_many_arguments)]
fn parse_cu(
    info: &[u8],
    abbrev: &[u8],
    str_offsets: &[u8],
    debug_str: &[u8],
    str_reloc: &HashMap<u64, i64>,
    cu_start: usize,
    out: &mut HashMap<String, Vec<Option<u64>>>,
) -> Option<usize> {
    let unit_len = u32_at(info, cu_start)? as usize;
    if unit_len == 0 || unit_len >= 0xffff_fff0 {
        return None; // 64-bit DWARF / reserved — not supported
    }
    let cu_end = cu_start.checked_add(4)?.checked_add(unit_len)?;
    let mut p = cu_start + 4;
    let version = u16_at(info, p)?;
    p += 2;
    // v5: unit_type(1) + address_size(1) + abbrev_offset(4). v2..4: abbrev_offset(4) + address_size(1).
    let abbrev_off = if version >= 5 {
        p += 2; // unit_type + address_size
        let off = u32_at(info, p)? as usize;
        p += 4;
        off
    } else {
        let off = u32_at(info, p)? as usize;
        p += 4 + 1; // abbrev_offset + address_size
        off
    };
    let table = parse_abbrev_table(abbrev, abbrev_off);

    // Pass 1: collect every DIE (offset → info), the parent-tag stack, and per
    // subprogram its name and ordered parameter type-refs. `str_offsets_base`
    // (from the CU root DIE) is needed to resolve `DW_FORM_strx` names.
    let mut dies: HashMap<usize, DieInfo> = HashMap::new();
    let mut str_off_base: u64 = 8; // default header size for 32-bit .debug_str_offsets
    let mut stack: Vec<u64> = Vec::new(); // tags of open (has-children) DIEs
    // (subprogram DIE offset in order) → (name_strx, [param type_refs]).
    let mut subs: Vec<(Option<u64>, Vec<Option<usize>>)> = Vec::new();
    let mut sub_of: HashMap<usize, usize> = HashMap::new(); // subprogram offset → index into subs

    while p < cu_end && p < info.len() {
        let die_off = p;
        let (code, np) = uleb(info, p)?;
        p = np;
        if code == 0 {
            stack.pop(); // null DIE: end of the current children list
            continue;
        }
        let Some(ab) = table.get(&code) else { return Some(cu_end) };
        let mut die = DieInfo { tag: ab.tag, ..Default::default() };
        for &(attr, form, implicit) in &ab.attrs {
            let (val, np) = read_form(info, p, form, implicit)?;
            p = np;
            match attr {
                DW_AT_type => die.type_ref = val.as_ref(cu_start),
                DW_AT_byte_size => die.byte_size = val.as_uint(),
                DW_AT_name => die.name_strx = val.as_strx(),
                DW_AT_str_offsets_base => {
                    // In a `.o` this attribute (a sec_offset) is itself relocated, so it
                    // reads as 0; keep the standard 32-bit header size (8). A linked image
                    // has the applied value.
                    if let Some(b) = val.as_uint().filter(|b| *b > 0) {
                        str_off_base = b;
                    }
                }
                _ => {}
            }
        }
        let parent = stack.last().copied();
        if ab.tag == DW_TAG_subprogram {
            sub_of.insert(die_off, subs.len());
            subs.push((die.name_strx, Vec::new()));
        } else if ab.tag == DW_TAG_formal_parameter && parent == Some(DW_TAG_subprogram) {
            // Attach to the nearest enclosing subprogram (the most recent one pushed).
            if let Some((_, params)) = subs.last_mut() {
                params.push(die.type_ref);
            }
        }
        dies.insert(die_off, die);
        if ab.has_children {
            stack.push(ab.tag);
        }
    }

    // Pass 2: resolve each subprogram's name and its parameters' pointee sizes.
    for (name_strx, params) in subs {
        let Some(idx) = name_strx else { continue };
        let Some(name) = resolve_strx(str_offsets, debug_str, str_reloc, str_off_base, idx) else {
            continue;
        };
        let sizes: Vec<Option<u64>> =
            params.iter().map(|t| pointer_pointee_size(&dies, *t)).collect();
        // Only record when at least one parameter is a typed pointer (else no hint).
        if sizes.iter().any(Option::is_some) {
            out.entry(name).or_insert(sizes);
        }
    }
    Some(cu_end)
}

/// The pointee byte size if `type_ref` is (a chain of typedef/cv-qualifiers over) a
/// `DW_TAG_pointer_type` whose pointee has a known `DW_AT_byte_size`; else `None`.
fn pointer_pointee_size(dies: &HashMap<usize, DieInfo>, type_ref: Option<usize>) -> Option<u64> {
    let ptr = strip_typedefs(dies, type_ref)?;
    let d = dies.get(&ptr)?;
    if d.tag != DW_TAG_pointer_type {
        return None;
    }
    let pointee = strip_typedefs(dies, d.type_ref)?;
    resolve_byte_size(dies, Some(pointee), 0)
}

/// Follow typedef / const / volatile / restrict wrappers to the underlying type DIE.
fn strip_typedefs(dies: &HashMap<usize, DieInfo>, mut r: Option<usize>) -> Option<usize> {
    for _ in 0..16 {
        let off = r?;
        let d = dies.get(&off)?;
        if matches!(
            d.tag,
            DW_TAG_typedef | DW_TAG_const_type | DW_TAG_volatile_type | DW_TAG_restrict_type
        ) {
            r = d.type_ref;
        } else {
            return Some(off);
        }
    }
    None
}

/// The byte size of a type, following cv/typedef wrappers (depth-guarded).
fn resolve_byte_size(dies: &HashMap<usize, DieInfo>, r: Option<usize>, depth: u32) -> Option<u64> {
    if depth > 16 {
        return None;
    }
    let off = strip_typedefs(dies, r)?;
    let d = dies.get(&off)?;
    if let Some(s) = d.byte_size {
        return Some(s);
    }
    // A pointer pointee that is itself a pointer is 8 bytes on LP64.
    if d.tag == DW_TAG_pointer_type {
        return Some(8);
    }
    None
}

/// Resolve a `DW_FORM_strx` index to its string (v5 indexed strings). The slot at
/// `base + index*4` in `.debug_str_offsets` holds the `.debug_str` offset — read from
/// the relocation ADDEND for that slot in a `.o` (the file bytes are zero there), else
/// from the raw value in a linked image.
fn resolve_strx(
    str_offsets: &[u8],
    debug_str: &[u8],
    str_reloc: &HashMap<u64, i64>,
    base: u64,
    index: u64,
) -> Option<String> {
    let slot = base + index.checked_mul(4)?;
    let str_off = match str_reloc.get(&slot) {
        Some(&addend) => usize::try_from(addend).ok()?,
        None => u32_at(str_offsets, usize::try_from(slot).ok()?)? as usize,
    };
    read_cstr(debug_str, str_off)
}

/// A decoded attribute value (only the shapes we consult).
enum FormVal {
    Uint(u64),
    /// A CU-relative reference (`DW_FORM_ref*`).
    RefCu(u64),
    /// A `.debug_info`-absolute reference (`DW_FORM_ref_addr`).
    RefAddr(u64),
    /// A `DW_FORM_strx*` string index.
    StrX(u64),
    Other,
}

impl FormVal {
    fn as_uint(&self) -> Option<u64> {
        match self {
            FormVal::Uint(v) => Some(*v),
            _ => None,
        }
    }
    fn as_strx(&self) -> Option<u64> {
        match self {
            FormVal::StrX(v) => Some(*v),
            _ => None,
        }
    }
    fn as_ref(&self, cu_start: usize) -> Option<usize> {
        match self {
            FormVal::RefCu(v) => usize::try_from(cu_start as u64 + *v).ok(),
            FormVal::RefAddr(v) => usize::try_from(*v).ok(),
            _ => None,
        }
    }
}

/// Read one attribute value of the given form at `p`, returning `(value, next)`.
/// Unrecognised-but-sized forms return `Other` after advancing correctly; a form
/// whose size cannot be determined returns `None` (aborts the unit — sound).
fn read_form(data: &[u8], p: usize, form: u64, implicit: i64) -> Option<(FormVal, usize)> {
    Some(match form {
        0x01 => (FormVal::Other, p + 8), // addr (LP64)
        0x0b | 0x0c => (FormVal::Uint(*data.get(p)? as u64), p + 1), // data1 / flag
        0x05 => (FormVal::Uint(u16_at(data, p)? as u64), p + 2),     // data2
        0x06 => (FormVal::Uint(u32_at(data, p)? as u64), p + 4),     // data4
        0x07 => (FormVal::Uint(u64_at(data, p)?), p + 8),            // data8
        0x1e => (FormVal::Other, p + 16),                            // data16
        0x08 => {
            // string (inline, NUL-terminated)
            let end = data[p..].iter().position(|&b| b == 0)? + p + 1;
            (FormVal::Other, end)
        }
        0x0e | 0x1f => (FormVal::Other, p + 4), // strp / line_strp (32-bit)
        0x10 => (FormVal::RefAddr(u32_at(data, p)? as u64), p + 4), // ref_addr (32-bit)
        0x11 => (FormVal::RefCu(*data.get(p)? as u64), p + 1),      // ref1
        0x12 => (FormVal::RefCu(u16_at(data, p)? as u64), p + 2),   // ref2
        0x13 => (FormVal::RefCu(u32_at(data, p)? as u64), p + 4),   // ref4
        0x14 => (FormVal::RefCu(u64_at(data, p)?), p + 8),          // ref8
        0x15 => {
            let (v, np) = uleb(data, p)?;
            (FormVal::RefCu(v), np) // ref_udata
        }
        0x17 => (FormVal::Uint(u32_at(data, p)? as u64), p + 4), // sec_offset (32-bit)
        0x18 => {
            // exprloc: ULEB length + that many bytes
            let (len, np) = uleb(data, p)?;
            (FormVal::Other, np + usize::try_from(len).ok()?)
        }
        0x19 => (FormVal::Other, p), // flag_present (0 bytes)
        0x21 => (FormVal::Uint(implicit.max(0) as u64), p), // implicit_const (in abbrev)
        0x0d => {
            let (v, np) = sleb(data, p)?;
            (FormVal::Uint(v.max(0) as u64), np) // sdata
        }
        0x0f | 0x22 | 0x23 => {
            let (v, np) = uleb(data, p)?;
            (FormVal::Uint(v), np) // udata / loclistx / rnglistx
        }
        0x1b => {
            let (_, np) = uleb(data, p)?;
            (FormVal::Other, np) // addrx
        }
        0x25 => (FormVal::StrX(*data.get(p)? as u64), p + 1), // strx1
        0x26 => (FormVal::StrX(u16_at(data, p)? as u64), p + 2), // strx2
        0x27 => (FormVal::StrX(u24_at(data, p)? as u64), p + 3), // strx3
        0x28 => (FormVal::StrX(u32_at(data, p)? as u64), p + 4), // strx4
        0x1a => {
            let (v, np) = uleb(data, p)?;
            (FormVal::StrX(v), np) // strx
        }
        0x29..=0x2c => {
            // addrx1..4
            (FormVal::Other, p + (form as usize - 0x28))
        }
        0x0a => (FormVal::Other, p + 1 + *data.get(p)? as usize), // block1
        0x03 => (FormVal::Other, p + 2 + u16_at(data, p)? as usize), // block2
        0x04 => (FormVal::Other, p + 4 + u32_at(data, p)? as usize), // block4
        0x09 => {
            let (len, np) = uleb(data, p)?; // block
            (FormVal::Other, np + usize::try_from(len).ok()?)
        }
        0x20 => (FormVal::Uint(u64_at(data, p)?), p + 8), // ref_sig8
        _ => return None,                                 // unknown form → abort the unit (sound)
    })
}

// --- primitive readers -----------------------------------------------------

fn uleb(data: &[u8], mut p: usize) -> Option<(u64, usize)> {
    let mut result = 0u64;
    let mut shift = 0u32;
    loop {
        let b = *data.get(p)?;
        p += 1;
        if shift < 64 {
            result |= ((b & 0x7f) as u64) << shift;
        }
        shift += 7;
        if b & 0x80 == 0 {
            return Some((result, p));
        }
        if shift > 70 {
            return None;
        }
    }
}

fn sleb(data: &[u8], mut p: usize) -> Option<(i64, usize)> {
    let mut result = 0i64;
    let mut shift = 0u32;
    loop {
        let b = *data.get(p)?;
        p += 1;
        if shift < 64 {
            result |= ((b & 0x7f) as i64) << shift;
        }
        shift += 7;
        if b & 0x80 == 0 {
            if shift < 64 && b & 0x40 != 0 {
                result |= -(1i64 << shift);
            }
            return Some((result, p));
        }
        if shift > 70 {
            return None;
        }
    }
}

fn u16_at(d: &[u8], p: usize) -> Option<u16> {
    Some(u16::from_le_bytes(d.get(p..p + 2)?.try_into().ok()?))
}
fn u24_at(d: &[u8], p: usize) -> Option<u32> {
    let b = d.get(p..p + 3)?;
    Some(u32::from_le_bytes([b[0], b[1], b[2], 0]))
}
fn u32_at(d: &[u8], p: usize) -> Option<u32> {
    Some(u32::from_le_bytes(d.get(p..p + 4)?.try_into().ok()?))
}
fn u64_at(d: &[u8], p: usize) -> Option<u64> {
    Some(u64::from_le_bytes(d.get(p..p + 8)?.try_into().ok()?))
}
fn read_cstr(d: &[u8], p: usize) -> Option<String> {
    let end = d.get(p..)?.iter().position(|&b| b == 0)? + p;
    Some(String::from_utf8_lossy(&d[p..end]).into_owned())
}
