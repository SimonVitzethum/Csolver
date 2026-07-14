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

Weitere abgeschlossene Teile (9231b06):
- [x] **Tag am `SymPointer`** (dynamisch): `SymPointer.borrow: Option<RegId>`, aus `PartialEq`
  ausgeschlossen wie `POrigin` (kein Verdikt/Merge gestört). Fließt mit dem Zeigerwert — durch
  Kopien, `gep`, **Speicher (store→load trägt den `SymValue`)** und **Phi** (Block-Param-Eval +
  Merge, Tag bleibt wenn beide Seiten gleich). Ersetzt den statischen Register-Vorabpass. Getestet:
  Borrow überlebt store→load-Round-Trip.
- [x] **Protectors**: ein `&mut`-**Referenz**-Parameter (nicht raw `*mut`) ist ein geschützter
  Root-Borrow — der MIR-Frontend prependet ein `csolver.retag.mut(param,param)` ans Entry;
  der Param nimmt am Borrow-Stack teil. End-to-end via Frontend getestet.
- [x] **Surfacing-Lücke gefixt**: `NoAliasingViolation` ist record-only (nur bei Verletzung),
  wurde nie aus `implied_checks` enumeriert → erreichte nie ein `verify_module`/CLI-Verdikt.
  discharge.rs fragt es jetzt pro Load/Store unter `--aliasing-model` explizit ab. **Das macht
  das gesamte Aliasing-Modell end-to-end über die CLI wirksam.**

Weitere abgeschlossene Teile (8a671fc):
- [x] **Two-Phase-Borrows exakt** als **shared** Reborrow modelliert (war: unterdrückt): ein
  Two-Phase-`&mut` ist während der Reservierung shared-artig (koexistiert) → `retag.shared`.
  Sound (Shared poppt keine Geschwister), aber ein echter aliasing-`&mut`-Write darunter
  invalidiert ihn weiterhin. `fake`/`shallow` bleiben Opaque.
- [x] **Interprozedurale Protektoren**: das Übergeben eines Borrows an einen Call reborrowt ihn
  (geschützte Nutzung) → ein Argument, dessen `&mut`-Tag bereits invalidiert war, ist eine
  Use-after-invalidation. Call-Handler prüft getaggte Zeiger-Argumente (als Read → kein
  False-FAIL); discharge.rs enumeriert `NoAliasingViolation` auch für Calls. Die volle
  Protektor-Garantie (Callee kann seinen `&mut`-Param nicht invalidieren) ist bereits durch den
  intraprozeduralen Parameter-Protektor abgedeckt, wenn der Callee analysiert wird.

Verbleibend (rein Detection, KEIN Soundness-Loch, geringer Wert):
- [x] **`UnsafeCell`/Interior Mutability exakt** (2bb39ae): `MType::InteriorMut` — der
  MIR-Parser erkennt `Cell`/`UnsafeCell`/`Mutex`/`Atomic*`, das Lowering unterdrückt Retags
  für deren Reborrows. War vorher schon sound (untagged Raw-Pointer), jetzt exakt getypt.

## Sound-Coverage-Lücken — Status & warum offen (2026-07-14 geprüft)

- [x] **Signed-mul-Overflow** — bereits abgedeckt (`arith_no_overflow` baut das
  nsw-Ziel via `ctx.sext` als Doppelbreiten-Produkt; getestet `mul nsw`→FAIL in
  `llvm_frontend/part_g.rs`). Audit/Kommentar waren veraltet, korrigiert.
- [x] **Use-after-scope innerhalb einer Funktion** (aef8779): ein address-taken Stack-Local
  bekannter Größe wird als **Stack-Region** modelliert (MIR-Parser erfasst `StorageLive/Dead`),
  `StorageDead(_x)` beendet die Lifetime → Deref danach = dangling. Region exakt dimensioniert
  (keine Bounds-FP) + initialisiert geseedet (keine Uninit-FP); Unbekannt-Größe bleibt opak
  (keine Perturbation). Der LLVM-`llvm.lifetime.end`-Pfad (eef91eb) und dangling-return (ec8914a)
  waren bereits da.
- [x] **Interprozedurale dangling-stack Escape** (29ff588): ein Callee, der auf jedem Pfad
  einen Zeiger in den eigenen Stack-Frame zurückgibt, summiert als `RetSummary::DanglingStack`
  (neuer `AbsVal::LocalStack`, konservativ gejoint → nie falsche Claim); am Call-Site wird der
  Rückgabewert als frische **freed** Region materialisiert, sodass ein Caller-Deref = definitive
  UAF über die normale Liveness-Maschinerie. Negativ-Kontrolle (Rückgabe eines Param-Zeigers)
  bleibt sicher. STILL OPEN: Escape über Out-Parameter-Store und Propagation durch einen Wrapper,
  der das dangling Callee-Resultat weiterreicht (Summary-Evaluator behandelt Call-Resultat opak).
- [x] **CFI-Slice: Call in Stack/Heap-Daten** (7d7b45f) — ein indirekter Call, dessen Ziel
  beweisbar in eine Stack- oder Heap-Region zeigt (Daten als Code ausführen = klassisches
  Jump-to-Shellcode), ist eine definitive `ValidIndirectTarget`-Verletzung. Stack/Heap sind nie
  legitim ausführbar → sound; devirtualisiert/Symbol/opak nicht geflaggt. Der sound-bare Teil
  des StackIntegrity-Punkts.
- [ ] **StackIntegrity / ValidStackFrame (Rücksprungadresse/Canary)** — der Store über das
  Frame-Ende ist bereits als InBounds-OOB gefangen und der Call-in-Daten-Fall jetzt oben; eine
  **dedizierte** RA-/Canary-Property bräuchte ein ABI-Rücksprungadress-Modell im Binär-Pfad, das
  RA-Slot von legitimem Caller-Arg-Zugriff sound trennt (aktuell UNKNOWN, um FP zu vermeiden).
  **Bewertung 2026-07-14: kein weiterer kleiner sound Slice; Rest durch InBounds subsumiert.**
- [ ] **Type-Confusion / Strict-Aliasing / Union-Punning** — partiell abgedeckt
  (Provenance-Labels + objtype-Contracts, 3a992a1). **Bewertung 2026-07-14: kein sound-barer
  Refutations-Slice ohne Typ-Lattice.** Eine TBAA-Verletzung (Load Typ T' von einem Store Typ T am
  selben Ort) ist nicht sound refutierbar, weil legitime `repr`-Reinterpretation (bytemuck, Union,
  `memcpy`-Roundtrip) genau dieselbe Form hat — nur ein Typ-Lattice + LLVM-`!tbaa`-Metadaten
  (Parser erfasst sie nicht) könnten beides trennen, und ein halber Bau wäre eine False-FAIL-Quelle.
  Bewusst zurückgestellt (soundness-first); die Provenance-basierte Teilabdeckung ist die sound
  Approximation.

## Windows-ISO-Pipeline (UDF + WIM LZX) — ERLEDIGT

- [x] **UDF-Filesystem-Reader** (b34d6f6, `crates/elf/src/udf.rs`): jedes Windows-Installations-ISO
  ist ein UDF-Hybrid (ISO-9660-Zweig = Stub). AVDP→VDS→FSD→Verzeichnisbaum. An echter Win11-25H2-ISO
  verifiziert (1064 Dateien, hunderte PE-Objekte + `install.wim`). CLI kombiniert ISO 9660 + UDF.
- [x] **WIM LZX** (4dfd91d, `crates/elf/src/lzx.rs`): **byte-exakt** — gegen 1475 echte `boot.wim`-
  Resourcen per gespeicherter SHA-1 verifiziert (0 Mismatches). Blocker (Testkorpus) gelöst: das
  Korpus sind die WIMs der ISO selbst, erreicht via den UDF-Reader.
- [ ] **LZMS** (selten, `/compress:recovery`) — **Bewertung 2026-07-14: blockiert auf Testkorpus.**
  Die Windows-ISO nutzt durchweg LZX, enthält also keine LZMS-Resource; ein LZMS-Decoder (LZ77 +
  Range-Coder + Delta-Modelle) wäre umfangreich UND nicht byte-exakt verifizierbar (genau die
  Disziplin, mit der LZX akzeptiert wurde: 1475 SHA-1-Abgleiche). Einen unverifizierbaren Decoder
  zu shippen widerspräche soundness-first; das aktuelle saubere `Unsupported` ist sound (nie Müll).
- [ ] **PDB** — **Bewertung 2026-07-14: blockiert auf Umgebung.** Separate `.pdb`-Datei (per GUID
  von der PE referenziert, nicht im Installations-ISO); braucht Windows-Buildumgebung + MSF/Stream-
  Parser zum Testen. Ohne Testartefakt nicht verifizierbar.

## Solver-Präzision (2026-07-14 Batch) — ERLEDIGT

- [x] **Interproc-Escape Wrapper-Propagation** (642ac4e): ein Wrapper `w(){ return leak() }` erbt
  `DanglingStack` über den Cross-Fn-Fixpunkt (finalize + summarize_module in Lockstep, Losslessness-
  Oracle hält). Nur DanglingStack komponiert (arg-unabhängig). Offen: Out-Parameter-Store-Escape.
- [x] **Symbolischer Barrel-Shifter** (ac41781): `Shl`/`LShr`/`AShr` mit symbolischem Amount jetzt
  exakt geblastet (log₂(w)-Stufen + OOB-Guard). Gegen Orakel verifiziert (4/6-Bit + w=64-Grenzen).
- [x] **release/acquire Flag-Access** (731d9b2): `smp_store_release`/`smp_load_acquire` emittieren
  den Flag-Write/Read zusätzlich zur Barriere → MP-Handoff modelliert (fehlende Acquire jetzt
  fangbar), release+acquire bleibt robust (kein FP). RMW-Atomic-Helfer bleiben bare Fences.
- [ ] **ABA value-aware & Refcount „last reference"** — **Bewertung 2026-07-14: nicht sound im
  aktuellen Trace-Modell.** Der Lockset-Trace trägt nur Location-*Klassen*, keine Werte/Tags. Ein
  echtes ABA braucht, dass der CAS-Wert tatsächlich zu A rekurriert, und der Standard-Fix (Generation-
  Counter) ist unsichtbar; „last reference"/Count-erreicht-0 braucht Refcount-*Wert*-Tracking. Eine
  Trace-only-Heuristik würde entweder Bugs verstecken (unsound) oder bedeutungslos feuern. Zurückgestellt
  auf wert-bewusste Modellierung (Frontend-Wertinfo); bleiben Kandidaten. Siehe [[open-todos]].

## Struktur / Wartbarkeit — ERLEDIGT

- [x] Datei-Refactor abgeschlossen (Commits d7815c2 … 2f09fce): `exec.rs` (8314),
  `x86.rs` (5835), `contracts.rs`, `llvm/parser.rs`, `elf/lib.rs`, `cli/main.rs`,
  `interleave.rs`, `llvm/lower.rs`, `summary.rs`, `mir/parser.rs` u.a. in Submodule
  gesplittet. Größte verbleibende Datei: `asm/x86/lower.rs` (~1022 Z., Einzelfunktion
  `decode_one`, nicht mechanisch teilbar). Fast alle anderen < 550 Zeilen.

## Technische Schuld

*(alle Punkte erledigt — siehe „Erledigt“)*

## Bekannte Stubs / Präzisionsgrenzen (sound, aber offen)

- [ ] `csolver-smt` ist ein `NullSolver`; `solver::encode` gibt `Unsupported`
  zurück (bewusste pure-Rust-Entscheidung; externes Backend = Opt-in-Frage).
- [x] Bit-Blaster: `udiv`/`sdiv`/`urem`/`srem` (107748c) + **symbolische Shift-Amounts**
  (ac41781, log₂(w)-Stufen-Barrel-Shifter) gebitblastet — beide gegen unabhängiges Orakel
  exhaustiv verifiziert. **Einzige nicht geblastete Konstruktion jetzt: Breite > `MAX_WIDTH`
  (64)** — sound (Fallback auf linear/UNKNOWN, nie Fehlkodierung).
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
