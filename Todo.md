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

*(alle Punkte erledigt — siehe „Erledigt“)*

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
  Ausnahmen (Einzelfunktionen, nicht mechanisch teilbar): `asm/x86/lower.rs`
  (`decode_one`, ~890 Z.) und `asm/x86/opcode.rs` (`decode_typed_opcode`, ~615 Z.);
  mögliche spätere Verbesserung: den in sich geschlossenen `0x0f`-Arm von
  `decode_one` in eine `decode_two_byte`-Hilfsfunktion ausziehen.
- [x] **Kernel-Wissen als hartkodierte Namenslisten** → Contracts migriert:
  Die Lock-/Sleep-/IRQ-/RCU-/Percpu-/Lookup-Klassifikation lebt jetzt in
  `crates/contracts/data/kernel_sync.contract` (neue Effekte `lock-acquire`,
  `blocking`, `irq-disable`/`irq-enable`, `rcu-read-lock`/`-unlock`, `percpu-ptr`,
  `container-lookup`, `global-lookup`). Ein Collector (`csolver_symbolic::sync`)
  sammelt sie **vor dem Solving** in eine Namens-Tabelle, die der Executor pro Call
  abfragt; `exec/kernel_names.rs` und die Match-Listen in `lockclass.rs` sind
  gelöscht. Neue Kernel-APIs = eine Contract-Zeile statt Codeänderung
  (`sync::install()` erlaubt später per `--contracts` überlagerte Nutzer-Dateien).
- [x] Korrumpierter Doc-Kommentar (`llvm/parser/ast.rs`) repariert.
- [x] MOVUPD: eigene `Instruction::Movupd`-Variante statt des Movsd-Fehlmappings
  (8-Byte-Move stand für einen 16-Byte-Move); Store-Form `66 0F 11` ergänzt.
- [x] `Function::block()`/`block_mut()`: O(1)-Positions-Fastpath (Blöcke liegen
  bei allen Frontends an Position == id), linearer Scan nur noch als Fallback.
- [x] `Ctx` in `absint/relational.rs` borrowt `Function`/`Cfg`/Index statt zu
  klonen.
