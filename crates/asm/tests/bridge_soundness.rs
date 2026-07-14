//! Soundness of the unmodeled-instruction bridge (`bridge_unmodeled`).
//!
//! The bridge keeps a function analysable when it hits an instruction the MSIR lowerer
//! does not model, by emitting an opaque call + a general-purpose-register havoc. That is
//! sound **only** for instructions that touch no memory: an instruction that reads or writes
//! memory must NOT be havoc-bridged, because the havoc drops the access — and a dropped,
//! unchecked load/store through an invalid pointer while the rest of the function verifies
//! is a **false PASS**. So a memory-touching unmodeled instruction declines the bridge and
//! the whole function drops to `UNKNOWN` (no decoded module), while a register-only
//! unmodeled instruction is still bridged (recall preserved).

use csolver_asm::x86::decode_function;

fn decoded_insts(m: &csolver_ir::Module) -> Option<usize> {
    m.functions
        .first()
        .map(|f| f.blocks.iter().map(|b| b.insts.len()).sum())
}

#[test]
fn memory_touching_unmodeled_instruction_is_not_havoc_bridged() {
    // `vmovups (%rdi), %xmm0 ; ret` — an unmodeled vector LOAD through %rdi. Havoc-bridging it
    // would silently drop the read of *(%rdi); instead the function must decline to decode.
    let mem_load = [0xc5u8, 0xf8, 0x10, 0x07, 0xc3];
    assert_eq!(
        decoded_insts(&decode_function("mem_load", &mem_load)),
        None,
        "a memory-touching unmodeled instruction must drop the function, not havoc it \
         (dropping the access silently could yield a false PASS)"
    );

    // `vaddps %xmm1, %xmm2, %xmm3 ; ret` — an unmodeled but REGISTER-ONLY vector op: safe to
    // bridge (the havoc over-approximates its register effect; no memory access is skipped).
    let reg_only = [0xc5u8, 0xe8, 0x58, 0xd9, 0xc3];
    assert!(
        decoded_insts(&decode_function("reg_only", &reg_only)).is_some(),
        "a register-only unmodeled instruction is still bridged (recall preserved)"
    );
}
