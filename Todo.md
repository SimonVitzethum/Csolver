# Todo — Schwächen & Risiken aus dem Code-Review (2026-07-13)

## Struktur / Wartbarkeit

- [ ] **`crates/symbolic/src/exec.rs` (8314 Zeilen) aufteilen.** Monolith trägt
  Speichermodell, Loop-Summaries, Taint, Typestate, Locks/RCU/IRQ, Refcounts und
  Provenance in einer Datei/einem Typ. Höchstes Review- und Regressionsrisiko.
  → Aufteilung in Submodule über einer schmaleren Executor-API.
- [ ] **`crates/asm/src/x86.rs` (5835 Zeilen) aufteilen** (Decoder-Tabellen,
  Lowering, Tests trennen).
- [ ] Weitere Dateien > 500 Zeilen modularisieren: `verifier/contracts.rs` (2825),
  `llvm/parser.rs` (2677), `elf/lib.rs` (2221), `cli/main.rs` (2016),
  `verifier/interleave.rs` (1982), `llvm/lower.rs` (1884), `symbolic/summary.rs`
  (1366), `mir/parser.rs` (1323), `testsuite/lib.rs` (1173), `verifier/lib.rs`
  (996), `mir/lower.rs` (964), `solver/sat.rs` (956), `contracts/lib.rs` (894),
  `absint/analysis.rs` (841), `llvm/lib.rs` (793), `ir/inst.rs` (727),
  `solver/bitblast.rs` (716), `absint/induction.rs` (607), `solver/expr.rs` (590),
  `asm/att.rs` (550), `ir/func.rs` (548), `llvm/debuginfo.rs` (510); Tests:
  `testsuite/tests/llvm_frontend.rs` (4642), `mir_frontend.rs` (1368).

## Technische Schuld

- [ ] **Kernel-Wissen als hartkodierte Namenslisten** statt Contracts:
  `LOCK_ACQUIRE`/`SPIN_ACQUIRE`/`BLOCKING`/`IRQ_DISABLE`/`IRQ_ENABLE`/`RCU_*`/
  `PERCPU_ACCESSOR` in `exec.rs`, Container-/fd-Table-Lookups in `lockclass.rs`.
  Migration ins `csolver-contracts`-System (wie bei den Allokator-Tabellen bereits
  geschehen), damit neue Kernel-APIs per `.contract`-Datei statt Codeänderung
  abgedeckt werden.
- [ ] Korrumpierter Doc-Kommentar `crates/llvm/src/parser.rs:48`
  („…plain sum ofgrep FAIL ~/fullscan.log" — versehentlich eingefügter Shell-Befehl).
- [ ] `FIXME` in `crates/asm/src/x86.rs` (~Z. 2959): MOVUPD-Variante fehlt.
- [ ] `Function::block()` / `block_mut()` sind lineare Suchen (`ir/func.rs`) und
  laufen in heißen Pfaden (Transferfunktionen) pro Aufruf → O(n²) bei großen
  Funktionen. Index-Tabelle (BlockId → Position) wäre billig.
- [ ] `Ctx` in `absint/relational.rs` klont die ganze `Function` (+ `Cfg`) —
  Borrow statt Clone.

## Bekannte Stubs / Präzisionsgrenzen (sound, aber offen)

- [ ] `csolver-smt` ist ein `NullSolver`; `solver::encode` gibt `Unsupported`
  zurück (bewusste pure-Rust-Entscheidung; externes Backend = Opt-in-Frage).
- [ ] Bit-Blaster: `udiv`/`sdiv`/`urem`/`srem` und symbolische Shift-Amounts
  werden nicht gebitblastet (Fallback auf linear/UNKNOWN).
- [ ] Textueller Intel-Syntax-x86- und AArch64-Assembler fehlen (nur AT&T bzw.
  ELF-Objekt); Inline-Asm nur opak.

## Prozess / Infrastruktur

- [ ] **Kein CI-Setup** (kein `.github/`): `cargo test --workspace` +
  `cargo clippy` als CI wäre ein 10-Minuten-Gewinn bei dieser Testdisziplin.
- [ ] Bus-Faktor 1: Soundness-Argumente leben in Kommentaren/`docs/`, nicht
  maschinengeprüft. Diskrepanz „formal verifier" vs. „informell argumentierte
  Soundness + Test-Orakel" dokumentiert halten.

## Erledigt

- [x] Datei-Refactor: alle Quelldateien möglichst < 500 Zeilen (siehe oben) —
  mechanische Aufteilung in Submodule, verhaltensneutral, Testsuite grün.
