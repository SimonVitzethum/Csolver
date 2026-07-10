# Kernel bug-finding sweep

Run CSolver's bug-finding mode (`--bugs`) over LLVM IR emitted from a real Linux
kernel build and collect the FAIL reports — each a potential memory-safety bug
(out-of-bounds, use-after-free, double-free, or a `copy_from_user` overflow) with a
concrete witness. Meant to run on a VPS: emitting and sweeping kernel IR is
resource-heavy (a full kernel is tens of millions of lines).

`run.sh` does **not** build the kernel. It consumes `.ll` files you produce first.

## 1. Produce kernel LLVM IR (on the VPS)

The kernel build system compiles with clang under `LLVM=1` and has a per-file `%.ll`
rule, so you can emit IR one translation unit at a time:

```sh
# in the kernel source tree
make LLVM=1 defconfig            # or your config of choice
make LLVM=1 prepare              # generated headers, so TUs compile

# one file:
make LLVM=1 fs/read_write.ll

# a whole subsystem (emit the .ll next to each .c, then collect them):
find fs -name '*.c' | sed 's/\.c$/.ll/' | xargs -n1 -P"$(nproc)" make LLVM=1 -k
mkdir -p /tmp/kll && find fs -name '*.ll' -exec cp --parents {} /tmp/kll \;
```

Notes:
- `-k` keeps going past files that fail to emit (some need config symbols enabled).
- Kernel IR is `-O2` by default; CSolver analyzes optimized IR. If a subsystem comes
  back mostly unanalyzed, try a lighter TU set first (`fs/`, `drivers/char/`, `net/`
  helpers) before the arch/asm-heavy cores.
- Start small: a few hundred files is plenty to shake out the pipeline and the
  first candidates. `mm/`, `fs/`, `net/core/`, and `drivers/` are good hunting.

## 2. Sweep

```sh
scaling/kernel/run.sh /tmp/kll               # sweep every *.ll there
TIMEOUT=120 JOBS=8 scaling/kernel/run.sh /tmp/kll
```

`TIMEOUT` is the per-file wall-clock cap (large TUs can be slow); `JOBS` is the
parallelism. Results land in `scaling/kernel/out/` (`fails.txt`, `errors.txt`,
`timeouts.txt`).

## 3. Read the results

- **bug candidates** — functions that FAIL under `--bugs`: CSolver found a reachable
  input that drives a memory violation, with a witness. This is a high-signal lead to
  **triage against the source**, not a proof of exploitability (bug-finding trades a
  small false-positive risk for recall — see the top-level `--bugs` docs). Confirm each
  by reading the function and, where possible, reproducing under KASAN.
- **parse/tool errors** — translation units with IR CSolver cannot yet lower (some
  construct in gap 3). The affected functions are skipped, not analyzed — a coverage
  gap, not a clean bill.
- **timeouts** — raise `TIMEOUT` to reach them, or leave them; a slow TU is usually a
  huge generated file.

## Whole-kernel cross-module scan

`run.sh` sweeps files independently (each `.ll` in isolation). For **cross-module**
analysis — a caller's argument validation flowing into a callee, which removes the
false positives a per-file view produces — use the `solver` CLI directly:

```sh
# link each directory into one module, derive attacker entries automatically,
# bug-finding mode; cap workers so a whole-kernel run stays under a RAM ceiling:
CSOLVER_JOBS=4 solver scan /tmp/kll --cross-file --auto-entries --bugs
```

`--cross-file` links each directory; `--auto-entries` treats every registered
ops-struct handler (plus syscall wrappers) as an attacker entry, so no hand-written
entry list is needed. `CSOLVER_JOBS` / `CSOLVER_MEM_RESERVE_MB` bound peak RSS without
changing any verdict (they only throttle concurrency).

To extract the whole-program interprocedural facts (summaries + pointer/scalar/field
contracts) for the entire tree in **bounded memory, without linking** — the streaming
path — use `solver facts /tmp/kll --closed-world`. It reports coverage and peak RSS;
the facts are bit-identical to the linked pipeline (proven by equivalence tests).

## What is and isn't modeled

CSolver proves/refutes **spatial and temporal** memory safety. It models the kernel
allocators (`kmalloc`/`kzalloc`/`kfree`/… → heap regions), `copy_from_user`/
`copy_to_user` (bulk bounds on the kernel buffer), inline asm (opaque havoc, so the
function stays analyzed), and `memcpy`/`memset` (refutable bulk bounds). It does **not**
model data races, integer-overflow-only UB, or locking. A FAIL is a memory-safety
lead; a clean sweep is not a proof (unsupported IR is skipped, and bug-finding is
recall-oriented, not complete).
