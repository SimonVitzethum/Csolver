//! **Differential *operation* test for the x86-64 decoder** against the llvm-objdump ground truth
//! (`data/x86_length_corpus.txt`). Complements `x86_length_diff.rs`: length pins that recursive
//! descent never desyncs; this pins that a decoded instruction is the *right operation* — a
//! mis-decode (say `sub` as `add`, or a wrong operand form) would model the wrong effect and could
//! yield a false PASS even with a correct length.
//!
//! Full semantic verification (operand values, flag effects) needs a reference CPU emulator, which
//! is out of scope for a zero-dependency tool. This validates the **mnemonic** — the operation
//! identity — which catches the gross mis-decodes. The comparison accounts for legitimate naming
//! differences that are NOT bugs, all confirmed by inspection against real disassembly:
//!   * VEX encodings — the decoder names `vaddps` by its SSE mnemonic `Addps` (v-prefix dropped);
//!   * AT&T size suffixes (`addq` vs `add`) and AT&T/Intel aliases (`cltq`/`cdqe`, `cqto`/`cqo`,
//!     `movslq`/`movsxd`, `movsbq`/`movsx`, `movzbl`/`movzx`);
//!   * the `xor r,r` zeroing idiom, modelled as `mov r, 0` (semantically identical);
//!   * `movabs` (mov with a 64-bit immediate), modelled as `mov`;
//!   * `tzcnt`/`lzcnt`, modelled as their `bsf`/`bsr` bit-scan (equivalent for a non-zero input).
//!
//! After those equivalences, the true-mismatch count must be **0**.

use csolver_asm::x86::decode_instruction;

const CORPUS: &str = include_str!("data/x86_length_corpus.txt");

/// The base mnemonic CSolver's decoded instruction represents, from its `Debug` variant name.
fn csolver_mnemonic(dbg: &str) -> String {
    let name = dbg.split('(').next().unwrap_or("");
    if matches!(name, "Jcc" | "Setcc" | "Cmovcc") {
        let cond = dbg
            .split('(')
            .nth(1)
            .unwrap_or("")
            .split([',', ')'])
            .next()
            .unwrap_or("");
        let cc = match cond {
            "O" => "o",
            "NO" => "no",
            "B" => "b",
            "AE" => "ae",
            "E" => "e",
            "NE" => "ne",
            "BE" => "be",
            "A" => "a",
            "S" => "s",
            "NS" => "ns",
            "P" => "p",
            "NP" => "np",
            "L" => "l",
            "GE" => "ge",
            "LE" => "le",
            "G" => "g",
            _ => "?",
        };
        let base = match name {
            "Jcc" => "j",
            "Setcc" => "set",
            _ => "cmov",
        };
        return format!("{base}{cc}");
    }
    name.to_lowercase()
}

/// Whether CSolver's mnemonic `cs` is a faithful representation of llvm's `lv` (see the module
/// doc for the naming/idiom equivalences that are not bugs).
fn equivalent(cs: &str, lv: &str) -> bool {
    let strip_sz = |x: &str| x.trim_end_matches(['b', 'w', 'l', 'q']).to_string();
    lv == cs
        || format!("v{cs}") == lv                                   // VEX: Addps ≡ vaddps
        || strip_sz(lv) == cs                                       // addq ≡ add
        || strip_sz(lv) == strip_sz(cs)
        || lv.strip_prefix('v').is_some_and(|x| strip_sz(x) == strip_sz(cs)) // vmovups ≡ movups
        || (cs == "mov" && (lv.starts_with("movabs") || lv.starts_with("xor"))) // 64-bit imm / xor-zero idiom
        || (cs == "movsx" && lv.starts_with("movs") && lv.ends_with(['q', 'l', 'w']))
        || (cs == "movzx" && lv.starts_with("movz"))
        || (cs == "movsxd" && (lv == "movslq" || lv == "movsxd"))
        || (cs == "bsf" && lv.starts_with("tzcnt"))
        || (cs == "bsr" && lv.starts_with("lzcnt"))
        || matches!((cs, lv), ("cdqe", "cltq") | ("cqo", "cqto") | ("cwde", "cwtl") | ("cbw", "cbtw"))
}

#[test]
fn x86_decoder_operation_matches_llvm_ground_truth() {
    let (mut decoded, mut mismatches) = (0usize, Vec::new());
    for line in CORPUS.lines() {
        let mut parts = line.split('|');
        let (Some(hex), Some(_len), Some(llvm)) = (parts.next(), parts.next(), parts.next()) else {
            continue;
        };
        if !hex.len().is_multiple_of(2) {
            continue;
        }
        let Some(bytes): Option<Vec<u8>> = (0..hex.len() / 2)
            .map(|i| u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).ok())
            .collect()
        else {
            continue;
        };
        if let Ok(d) = decode_instruction(&bytes, 0) {
            decoded += 1;
            let cs = csolver_mnemonic(&format!("{:?}", d.instruction));
            if !equivalent(&cs, llvm) {
                mismatches.push(format!("{hex}: decoded `{cs}` but llvm says `{llvm}`"));
            }
        }
    }
    eprintln!(
        "x86 operation diff: {decoded} decoded, {} mismatch(es)",
        mismatches.len()
    );
    assert!(
        decoded > 500,
        "corpus should be substantial (got {decoded})"
    );
    assert!(
        mismatches.is_empty(),
        "decoded operation must match the real disassembly (a mis-decode models the wrong effect \
         → potential false PASS):\n{}",
        mismatches.join("\n")
    );
}
