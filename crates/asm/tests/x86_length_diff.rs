//! **Differential length test for the x86-64 decoder** against an llvm-objdump
//! ground truth (`data/x86_length_corpus.txt`, ~1k real instructions from clang
//! `-O0..-O3` output across ISA extensions, plus a hand-written SSE/AVX/bit-manip
//! set; regenerate with `data/regen.sh`).
//!
//! ## Why length
//! The decoder drives **recursive descent** and the **unmodeled-instruction bridge**
//! (`bridge_unmodeled` reads `decode_instruction(...).length` to know how many bytes an
//! unknown instruction occupies). If that length is wrong by even one byte, the byte
//! stream desyncs and every following instruction is mis-decoded — a path to a **false
//! PASS**, the one outcome a verifier must never produce. So the invariant this test
//! pins is: **whenever the decoder decodes an instruction, its `length` equals the true
//! byte length.** Declining to decode (an `Err`) is sound (the bridge then also declines
//! and the function drops to `UNKNOWN`), so it is reported as a coverage figure, never a
//! failure.
//!
//! The corpus is committed as data (hex bytes + length + mnemonic), so the test is
//! self-contained and deterministic — no LLVM tools are needed at test time.

use csolver_asm::x86::decode_instruction;

const CORPUS: &str = include_str!("data/x86_length_corpus.txt");

/// Parse a hex-byte string (`"48 89"` style already stripped to `"4889"`); `None` on any
/// non-hex — a malformed corpus line is skipped, never a panic.
fn hex_bytes(s: &str) -> Option<Vec<u8>> {
    if !s.len().is_multiple_of(2) {
        return None;
    }
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok())
        .collect()
}

#[test]
fn x86_decoder_length_matches_llvm_ground_truth() {
    let (mut total, mut decoded, mut mismatches) = (0usize, 0usize, Vec::new());
    for line in CORPUS.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let mut parts = line.split('|');
        let (Some(hex), Some(len), Some(mn)) = (parts.next(), parts.next(), parts.next()) else {
            continue;
        };
        let (Some(bytes), Ok(want)) = (hex_bytes(hex), len.parse::<usize>()) else {
            continue;
        };
        total += 1;
        if let Ok(d) = decode_instruction(&bytes, 0) {
            decoded += 1;
            if d.length != want {
                mismatches.push(format!(
                    "{hex} ({mn}): decoded length {} but true length is {want}",
                    d.length
                ));
            }
        }
    }

    // Coverage is informational; length-soundness is the hard invariant.
    eprintln!(
        "x86 length diff: {decoded}/{total} decoded ({:.0}% coverage), {} length mismatch(es)",
        100.0 * decoded as f64 / total as f64,
        mismatches.len()
    );
    assert!(total > 500, "corpus should be substantial (got {total})");
    assert!(
        mismatches.is_empty(),
        "decoder length must match the true instruction length (a wrong length desyncs \
         recursive descent → potential false PASS):\n{}",
        mismatches.join("\n")
    );
}
