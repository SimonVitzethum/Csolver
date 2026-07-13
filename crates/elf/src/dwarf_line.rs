//! A focused DWARF `.debug_line` reader: recover `(instruction address → source line)`
//! rows so a finding on a compiled binary can name the source line, the way the MIR path
//! carries spans. Runs the line-number state machine (DWARF v4/v5); the directory/file
//! tables are skipped via `header_length` (only line numbers are recovered, not names),
//! which sidesteps the v4↔v5 table-format differences. Addresses in a relocatable object
//! come from the `DW_LNE_set_address` operand plus its relocation addend.
//!
//! Bounds-checked; a malformed section yields an empty table, never a panic.

use super::*;
use crate::dwarf::section_addends;

/// `(address, line)` rows from `.debug_line`, sorted by address. An access at address A
/// is attributed to the row with the greatest address ≤ A (`line_at`).
pub fn line_rows(image: &Image, file: &[u8]) -> Vec<(u64, u32)> {
    let Some(data) = image.section_bytes_by_name(".debug_line", file) else { return Vec::new() };
    // In a relocatable object the set_address operands are 0 in the file; the real
    // address is the relocation addend at that offset (keyed by section-relative offset).
    let addends = section_addends(image, ".debug_line");
    let mut rows: Vec<(u64, u32)> = Vec::new();
    let mut unit = 0usize;
    while unit + 4 <= data.len() {
        match parse_unit(data, unit, &addends, &mut rows) {
            Some(next) if next > unit => unit = next,
            _ => break,
        }
    }
    rows.sort_by_key(|&(a, _)| a);
    rows.dedup();
    rows
}

/// The source line for address `addr` (the row with the greatest address ≤ `addr`).
pub fn line_at(rows: &[(u64, u32)], addr: u64) -> Option<u32> {
    let i = rows.partition_point(|&(a, _)| a <= addr);
    (i > 0).then(|| rows[i - 1].1)
}

/// Parse one line-program unit; returns the offset of the next unit.
fn parse_unit(data: &[u8], base: usize, addends: &std::collections::HashMap<u64, i64>, rows: &mut Vec<(u64, u32)>) -> Option<usize> {
    let unit_len = u32::from_le_bytes(data.get(base..base + 4)?.try_into().ok()?) as usize;
    if unit_len == 0xffff_ffff {
        return None; // 64-bit DWARF not handled
    }
    let end = base.checked_add(4)?.checked_add(unit_len)?;
    if end > data.len() {
        return None;
    }
    let mut p = base + 4;
    let version = u16::from_le_bytes(data.get(p..p + 2)?.try_into().ok()?);
    p += 2;
    if version >= 5 {
        p += 2; // address_size (1) + segment_selector_size (1)
    }
    let header_len = u32::from_le_bytes(data.get(p..p + 4)?.try_into().ok()?) as usize;
    p += 4;
    let program_start = p + header_len; // the file/dir tables are skipped wholesale
    let min_inst_len = *data.get(p)? as u64;
    p += 1;
    if version >= 4 {
        p += 1; // maximum_operations_per_instruction
    }
    p += 1; // default_is_stmt
    let line_base = *data.get(p)? as i8 as i64;
    p += 1;
    let line_range = *data.get(p)? as i64;
    p += 1;
    let opcode_base = *data.get(p)?;
    p += 1;
    // standard_opcode_lengths[opcode_base - 1] — the operand count of each standard op.
    let std_lengths: Vec<u8> = (1..opcode_base).map(|i| *data.get(p + i as usize - 1).unwrap_or(&0)).collect();

    if line_range == 0 || program_start > end {
        return Some(end);
    }
    run_program(data, program_start, end, addends, min_inst_len, line_base, line_range, opcode_base, &std_lengths, rows);
    Some(end)
}

/// The line-number state machine.
#[allow(clippy::too_many_arguments)]
fn run_program(
    data: &[u8],
    start: usize,
    end: usize,
    addends: &std::collections::HashMap<u64, i64>,
    min_inst_len: u64,
    line_base: i64,
    line_range: i64,
    opcode_base: u8,
    std_lengths: &[u8],
    rows: &mut Vec<(u64, u32)>,
) {
    let mut addr: u64 = 0;
    let mut line: i64 = 1;
    let mut p = start;
    while p < end {
        let op = data[p];
        p += 1;
        if op == 0 {
            // Extended opcode: len (LEB), sub-opcode, operand.
            let (len, np) = uleb(data, p);
            p = np;
            let sub_end = p + len as usize;
            if len == 0 || sub_end > end {
                break;
            }
            let sub = data[p];
            match sub {
                0x01 => line = 1, // DW_LNE_end_sequence: reset (row already emitted by copy)
                0x02 => {
                    // DW_LNE_set_address: an 8-byte address. In a relocatable object it is
                    // 0 in the file and the real address is the relocation addend at this
                    // section offset; in a linked image the file bytes are the address.
                    if let Some(b) = data.get(p + 1..p + 9) {
                        let raw = u64::from_le_bytes(b.try_into().unwrap_or([0; 8]));
                        let sec_off = (p + 1) as u64;
                        addr = addends.get(&sec_off).map(|&a| a as u64).unwrap_or(raw);
                    }
                }
                _ => {}
            }
            p = sub_end;
        } else if op < opcode_base {
            // Standard opcode.
            match op {
                0x01 => rows.push((addr, line.max(0) as u32)), // DW_LNS_copy
                0x02 => {
                    let (adv, np) = uleb(data, p);
                    p = np;
                    addr = addr.wrapping_add(adv * min_inst_len);
                    continue;
                }
                0x03 => {
                    let (adv, np) = sleb(data, p);
                    p = np;
                    line += adv;
                    continue;
                }
                0x08 => {
                    // DW_LNS_const_add_pc: advance by the special-opcode 255 address delta.
                    let adj = (255 - opcode_base) as u64 / line_range as u64;
                    addr = addr.wrapping_add(adj * min_inst_len);
                }
                0x09 => {
                    // DW_LNS_fixed_advance_pc: a 2-byte operand.
                    if let Some(b) = data.get(p..p + 2) {
                        addr = addr.wrapping_add(u16::from_le_bytes([b[0], b[1]]) as u64);
                    }
                    p += 2;
                    continue;
                }
                _ => {
                    // Skip the operands of any other standard opcode (each a ULEB).
                    for _ in 0..std_lengths.get(op as usize - 1).copied().unwrap_or(0) {
                        p = uleb(data, p).1;
                    }
                }
            }
        } else {
            // Special opcode: advance address and line, emit a row.
            let adjusted = (op - opcode_base) as i64;
            addr = addr.wrapping_add((adjusted / line_range) as u64 * min_inst_len);
            line += line_base + (adjusted % line_range);
            rows.push((addr, line.max(0) as u32));
        }
    }
}

/// Read an unsigned LEB128; returns `(value, next offset)`.
fn uleb(data: &[u8], mut p: usize) -> (u64, usize) {
    let (mut result, mut shift) = (0u64, 0u32);
    while let Some(&b) = data.get(p) {
        p += 1;
        result |= ((b & 0x7f) as u64) << shift;
        if b & 0x80 == 0 {
            break;
        }
        shift += 7;
        if shift >= 64 {
            break;
        }
    }
    (result, p)
}

/// Read a signed LEB128; returns `(value, next offset)`.
fn sleb(data: &[u8], mut p: usize) -> (i64, usize) {
    let (mut result, mut shift) = (0i64, 0u32);
    let mut byte = 0u8;
    while let Some(&b) = data.get(p) {
        p += 1;
        byte = b;
        result |= ((b & 0x7f) as i64) << shift;
        shift += 7;
        if b & 0x80 == 0 {
            break;
        }
        if shift >= 64 {
            break;
        }
    }
    if shift < 64 && byte & 0x40 != 0 {
        result |= -1i64 << shift;
    }
    (result, p)
}

#[cfg(test)]
#[path = "dwarf_line_tests.rs"]
mod tests;
