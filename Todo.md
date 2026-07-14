# Todo — Schwächen & Risiken aus dem Code-Review (2026-07-13)

## Rust-Aliasing-Modell (Borrow-Stack, `--aliasing-model`) — Restarbeit

Der Opt-in-Detektor (`SafetyProperty::NoAliasingViolation`, sound, kein False-FAIL, nur auf
feasiblem Pfad refutiert) deckt jetzt **zwei** Klassen ab:

- [x] **Write-through-`&T`** (geteilte Referenz beschrieben).
- [x] **Use-after-invalidation von `&mut`** (6f4db67): der MIR-Parser erfasst `&mut` vs `&`,
  ein `&mut *_p`-Reborrow emittiert ein `csolver.retag.mut`-Marker-Intrinsic; der Executor
  führt einen **Per-Region-Borrow-Stack** mit **Ableitungsbaum** (Register-als-Tag) — ein
  Reborrow invalidiert Geschwister, ein Root-Reborrow alle vorigen, ein Write poppt darüber;
  Nutzung eines invalidierten Tags = Verletzung. Merge poisont bei Uneinigkeit (sound). Kein
  False-FAIL auf legitimen Reborrow-Ketten (getestet).

Weitere abgeschlossene Teile (1fb77cf):
- [x] **`&raw mut`/`&raw const`-Retags** (`&raw mut *_p` = unique, `&raw const` = shared).
- [x] **Two-Phase/fake/shallow-Unterdrückung**: `Rvalue::Ref(Place, RefKind)`; `Opaque` emittiert
  kein Retag (Two-Phase-Reservierung koexistiert legitim → sonst False-FAIL-Risiko). Sound.
- [x] **Shared-Read-Tags**: `&(*_p)` emittiert `csolver.retag.shared`; ein Shared-Retag fügt
  seinen Tag hinzu ohne Geschwister zu poppen (Under-Approx der SB-Lese-Effekte → nie False-FAIL);
  ein `&mut`-Write darunter poppt ihn → Read durch invalidierten Shared-Borrow = Verletzung.

Für ein **vollständiges** Stacked/Tree-Borrows fehlt noch (beides **KEIN** Soundness-Loch —
das Modell ist ohne sie sound, sie fügen nur Detection/Präzision hinzu):
- [ ] **Protectors** für Funktionsargumente (ein übergebenes `&mut` bleibt für die Call-Dauer
  eindeutig, Aliasing während des Calls ist UB). Genuin **interprozedural**: wir analysieren
  Funktionen einzeln, ein Call ist opak; `region_borrows` bleibt über Calls stale, aber sound
  (SSA-Tags bleiben gültig, eine ungesehene fremde Invalidierung = verpasster Bug, kein False-FAIL).
- [ ] **Tag am `SymPointer`** für Borrows, die der Register-Tag-Vorabpass nicht sieht (durch
  Speicher gespeichert+geladen, oder durch Phi/Block-Parameter geführt — Letztere werden aktuell
  beim Merge konservativ *poisont*). Rein Präzision; invasiv (31 Konstruktionsstellen, aus
  `PartialEq` auszuschließen wie `POrigin`), daher als eigener großer Schritt.

## Sound-Coverage-Lücken — Status & warum offen (2026-07-14 geprüft)

- [x] **Signed-mul-Overflow** — bereits abgedeckt (`arith_no_overflow` baut das
  nsw-Ziel via `ctx.sext` als Doppelbreiten-Produkt; getestet `mul nsw`→FAIL in
  `llvm_frontend/part_g.rs`). Audit/Kommentar waren veraltet, korrigiert.
- [ ] **Use-after-scope innerhalb einer Funktion.** Blockiert: MIR modelliert
  `&_local` gar nicht als Region (fällt auf `Const::Undef`, opak = sound). Es gibt
  **keine Stack-Region**, die ein `StorageDead(_n)` als tot markieren könnte
  (aktuell als Nop übersprungen). Voraussetzung = Stack-Locals als Regionen
  modellieren (Kern-Modelländerung, FP-Risiko: bisher opake `&local` würden neue
  Obligations tragen). Der LLVM-Pfad (`llvm.lifetime.end`) **ist** erledigt
  (eef91eb); der dangling-**return** von `&local` ebenfalls (ec8914a).
- [ ] **StackIntegrity / ValidStackFrame** — außerhalb des MSIR-Modells: gerettete
  Register / Rücksprungadresse / Canaries existieren im IR nicht (Prologe werden
  bei ELF-Dekodierung als Frame-Setup abstrahiert). Brauchte ein Byte-genaues
  Stack-Frame-Modell im Binär-Pfad. Kein kleiner sound Slice.
- [ ] **Type-Confusion / Strict-Aliasing / Union-Punning** — partiell abgedeckt
  (Provenance-Labels + objtype-Contracts, 3a992a1). Volles TBAA/Strict-Aliasing ist
  FP-anfällig (legitime `repr`-Reinterpretation vs. UB nur mit Typ-Lattice sound
  trennbar); bewusst nicht halb gebaut (soundness-first).

## WIM: LZX/LZMS-Dekompression (`crates/elf/src/wim.rs`)

- [ ] **LZX** (Default-Kompression realer `install.wim`). Aktuell sauberer
  `Error::unsupported` (sound). NICHT blind implementieren: ein inhaltlich falsch
  dekomprimierter Chunk **gleicher Länge** überlebt den Size-Guard → analysierte
  Garbage-Bytes könnten einen **False-PASS** eines nicht existierenden Binaries
  erzeugen (Kardinalsünde). Voraussetzung = ein **verifiziertes Testkorpus**
  (wimlib-/DISM-erzeugte LZX-WIM-Fixture) für Round-Trip-Tests. Format: LZX =
  LZ77 + Huffman (Main-/Length-/Aligned-Tree, 20-Elem-Pretrees, Delta-kodierte
  Baumlängen über Blockgrenzen, R0/R1/R2-Repeat-Offsets, E8-Call-Translation,
  Block-Typen verbatim/aligned/uncompressed), 16-bit-LE-Bitstrom. LZMS analog.

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
- [x] ~~Textueller Intel-Syntax-x86- und AArch64-Assembler fehlen~~ → beide
  ergänzt: `x86text` deckt jetzt **AT&T und Intel** x86-64 über ein uniformes
  Operand-Modell (`TextOp`, AT&T-interne Reihenfolge) ab, `arm64_text` das
  **textuelle AArch64** (mov/add/sub/and/orr/eor/shifts, ldr/str/ldp/stp,
  cmp/b/b.cond/cbz/cbnz, adrp+`:lo12:`). Jeder Speicheroperand (inkl.
  RIP-relativ / adrp-Symbol / skaliertem Index) wird zu `PtrOffset`+Load/Store
  extrahiert und trägt die `in_bounds`-Obligation (per CLI-Rauchtest verifiziert:
  OOB → FAIL). Arch+Syntax werden aus der Quelle auto-erkannt (`csolver_asm::detect`).
  Inline-Asm bleibt opak (per Contract abgedeckt, siehe [[contract-externalization]]).
- [x] `push`/`pop`/`call` (x86) und `bl`/`blr` (ARM) lassen die Funktion **nicht
  mehr droppen**: `call`/`bl` sind opake `Inst::Call` mit Fall-Through (Analyse
  läuft weiter, havoct caller-saved + rax/x0); `push`/`pop` modellieren bewusst
  keinen Speicherzugriff (der Callee-Save-Spill liegt immer auf gültigem Stack —
  ihn nicht zu modellieren ist sound und vermeidet, dass eine winzige Push-Region
  über `mov rbp,rsp` jeden `[rbp-k]`-Local fälschlich als OOB meldet). Ergebnis:
  rsp-relative Frames (optimiert) verifizieren präzise (PASS/FAIL), rbp-relative
  -O0-Frames sind ehrlich UNKNOWN statt falsch FAIL.
- [x] **Präzise Frame-Pointer-Modellierung**: Das Idiom `push rbp; mov rbp,rsp;
  sub rsp,N` baut jetzt **eine** Frame-Region mit unten beschränkter, oben offener
  Größe (`≥ N+16` via Maskierung eines freien Registers), rsp am Boden (Offset 0),
  rbp an der Oberkante (Offset N). Locals (`[rbp-k]`, `[rsp+j]`) → **PASS**;
  Caller-Args (`[rbp+16+]`) → UNKNOWN; echte Unterläufe → sound. Dazu im Executor:
  eine Stack-Region mit **symbolischer** (geratener) Größe ist eine `assumed`-Region
  (gilt auch für VLAs) — die vorhandene „kein falscher FAIL bei konstantem Offset"-
  Logik greift, und `is_fresh_alloc` refutiert Uninit-Reads solcher Regionen nicht
  (Caller-Args sind extern initialisiert). CLI-verifiziert: -O0-rbp-Frame → PASS,
  Stack-Args → UNKNOWN (kein falscher FAIL), adversariale OOB weiterhin FAIL.

## Prozess / Infrastruktur

- [x] ~~Kein CI-Setup~~ → `.github/workflows/ci.yml`: `cargo test --workspace`
  + `cargo clippy --all-targets -- -D warnings` auf Push/PR.
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
