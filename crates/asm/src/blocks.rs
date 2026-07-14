//! Architecture-independent control-flow-graph assembly: turn a linear list of
//! decoded instructions (each with its byte span, MSIR, and control-flow effect)
//! into MSIR basic blocks. Both the x86-64 and AArch64 decoders share this.

use csolver_core::Error as CoreError;
use csolver_ir::{BasicBlock, BlockId, Operand, RegId, Terminator};
use std::collections::{BTreeMap, BTreeSet, HashSet};

/// The control-flow effect of an instruction.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Ctrl {
    /// Falls through to the next instruction.
    Fall,
    /// A return.
    Ret,
    /// An unconditional jump to a byte offset.
    Jmp(usize),
    /// A conditional jump to a byte offset (else falls through); the `RegId`
    /// holds the branch condition.
    Jcc(usize, RegId),
}

/// One decoded instruction: its MSIR, its byte span, and its control-flow effect.
pub(crate) struct DecodedInsn {
    pub offset: usize,
    pub next: usize,
    pub insts: Vec<csolver_ir::Inst>,
    pub ctrl: Ctrl,
}

/// Assemble decoded instructions into MSIR basic blocks. Block leaders are the
/// entry, every branch target, and the instruction after every branch/return. A
/// branch target that is not an instruction boundary makes the function fail to
/// build (the caller reports it `unanalyzed`) — sound: we never guess at a
/// mid-instruction or data target.
pub(crate) fn build_blocks(
    decoded: Vec<DecodedInsn>,
) -> csolver_core::Result<(Vec<BasicBlock>, BlockId)> {
    if decoded.is_empty() {
        // An empty body is a vacuously-safe single `ret` block.
        return Ok((
            vec![BasicBlock::new(BlockId(0), Terminator::Return(None))],
            BlockId(0),
        ));
    }
    let offsets: HashSet<usize> = decoded.iter().map(|d| d.offset).collect();

    let mut leaders: BTreeSet<usize> = BTreeSet::new();
    leaders.insert(decoded[0].offset);
    for d in &decoded {
        match d.ctrl {
            Ctrl::Jmp(t) | Ctrl::Jcc(t, _) => {
                if !offsets.contains(&t) {
                    return Err(CoreError::parse(
                        "asm: branch target is not an instruction boundary",
                    ));
                }
                leaders.insert(t);
                leaders.insert(d.next);
            }
            Ctrl::Ret => {
                leaders.insert(d.next);
            }
            Ctrl::Fall => {}
        }
    }
    let leaders: Vec<usize> = leaders
        .into_iter()
        .filter(|o| offsets.contains(o))
        .collect();
    let block_of: BTreeMap<usize, BlockId> = leaders
        .iter()
        .enumerate()
        .map(|(i, &o)| (o, BlockId(i as u32)))
        .collect();

    let mut blocks: Vec<BasicBlock> = leaders
        .iter()
        .map(|&o| BasicBlock::new(block_of[&o], Terminator::Return(None)))
        .collect();
    let mut cur = 0usize;
    for d in &decoded {
        while cur + 1 < leaders.len() && leaders[cur + 1] <= d.offset {
            cur += 1;
        }
        blocks[cur].insts.extend(d.insts.iter().cloned());
        // The block ends when the next instruction starts a new block, or there
        // is none.
        let is_block_end = !offsets.contains(&d.next) || block_of.contains_key(&d.next);
        if is_block_end {
            blocks[cur].term = terminator_for(d, &block_of)?;
        }
    }
    Ok((blocks, BlockId(0)))
}

/// The MSIR terminator for a block ending at `d`.
fn terminator_for(
    d: &DecodedInsn,
    block_of: &BTreeMap<usize, BlockId>,
) -> csolver_core::Result<Terminator> {
    let target = |off: usize| {
        block_of
            .get(&off)
            .copied()
            .ok_or_else(|| CoreError::parse("asm: dangling branch target"))
    };
    Ok(match d.ctrl {
        Ctrl::Ret => Terminator::Return(None),
        Ctrl::Jmp(t) => Terminator::Br {
            target: target(t)?,
            args: Vec::new(),
        },
        Ctrl::Jcc(t, cond) => Terminator::CondBr {
            cond: Operand::Reg(cond),
            then_blk: target(t)?,
            then_args: Vec::new(),
            else_blk: target(d.next)?,
            else_args: Vec::new(),
        },
        Ctrl::Fall => Terminator::Br {
            target: target(d.next)?,
            args: Vec::new(),
        },
    })
}
