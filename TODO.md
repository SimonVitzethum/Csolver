# CSolver — offene Abdeckung (Coverage-TODO)

Code-fundierter Audit-Stand (2026-07-23). Zwei Sinne von „Abdeckung": **Bug-Klassen**
(welche Safety-Properties überhaupt *entschieden* werden) und **Decided-Rate** (wieviel %
der Funktionen PASS/FAIL statt UNKNOWN — die Provenance-Story, siehe
`docs/complete-pointer-provenance-plan.md` / `docs/unknown-under-3pct-roadmap.md`).

Kardinalregel: **nie ein false PASS**. Refutation (FAIL) nur auf feasiblem/exaktem Pfad;
unsound-im-Allgemeinen hinter benannter Annahme; beide Orakel (Miri + C-ASan/UBSan) pro Schritt.

---

## Autonome Session 3b (2026-07-27) — Coverage-Sektionen A–D

**Geschiffft (sound, beide Orakel: 0 false PASS / 0 false FAIL):**
- **[x] C — ≥3-Faktoren-Allokationsgröße-Overflow** (`size_overflow_goal` generalisiert auf n Faktoren):
  Produkt in **Summen-Breite** der Faktoren geprüft (Σwᵢ, sofern ≤ `MAX_WIDTH`), sonst `None` (sound —
  omittiert nur). Subsumiert den 2-Faktoren-Fall, deckt 3+ schmale Faktoren (`kmalloc_array`-artig). Der
  häufige all-`size_t`-3-Faktoren-Fall (Σ = 192 > 128) bleibt ungemodellt — dieselbe Wide-Int-Grenze.
  Tests: 2- und 3-Faktoren refutiert.
- **[x] C — Integer-UB im strikten `verify`-Pfad war BEREITS abgedeckt**: der `decide`-Gate refutiert
  `(state.exact && !internal_free_param) || (bug_finding && …)` — div0/shift/overflow refutieren auf
  exaktem Pfad auch ohne `--bugs`. „Erwägen"-Punkt erfüllt.
- **[x] B — Alignment-Refutation**: eine beweisbar **misaligned** Zugriff (Basis beweisbar ≥ `aalign`
  ausgerichtet, `aalign` echte 2er-Potenz-Anforderung, Offset beweisbar `≢ 0 (mod aalign)` auf exaktem
  Pfad) wird jetzt mit Witness refutiert statt UNKNOWN. Drei-wege (kein false PASS bei „nur nicht
  beweisbar aligned" → UNKNOWN). Tests: misaligned refutiert, aligned PASS, unbekannte Basis UNKNOWN.
- **[x] D — Contract-Korpus war BEREITS default-aktiv** (via `include_str!` compiled-in; `contracts()`
  → `Contracts::defaults`), also feuern Capability/Taint/Typestate **out-of-the-box** (TODO-Prämise
  stale). Korpus **konservativ erweitert**: Format-String-Taint-Sinks (sprintf/snprintf/syslog),
  erweitertes File-Protokoll (getc/fgets/… use-after-close), Kernel-Refcount-Paare (dget/dput,
  fget/fput, mntget/mntput, module_get/put), sk_buff-Double-Free. Smoke-Test: Parse + Registrierung.

**Bewusst NICHT als Refutation geschiffft (Soundness-Fallen / Redundanz):**
- **A — `ValidReference`**: im symbolischen Executor durch NoNullDeref + NoUseAfterFree + InBounds +
  Alignment + `ValidValue` **subsumiert** — eine dedizierte Refutation würde nur doppelt melden. Wie
  `StackIntegrity` ein Katalog-Label. (Kein redundanter Check hinzugefügt.)
- **A — `StackIntegrity`/RA-Integrität**: bräuchte Frontend-Frame-Umbau (RA-Slot), Korruption durch
  InBounds/ValidIndirectTarget subsumiert — deferred (siehe Session-3-Befund).
- **C — plain-wrapping add/sub/mul, Truncation, signed/unsigned-Verwechslung**: **definiertes** Verhalten
  in C (unsigned-wrap, mod-2ⁿ-Truncation, -fwrapv) — eine Refutation wäre ein **false FAIL**, kein Bug.
  Nur als contract-/taint-getriebene Heuristik sinnvoll (nicht als harte Obligation) → nicht geschiffft.
- **B — `ValidPointerArith`-Refutation**: reitet bewusst auf `InBounds` (das den OOB-Witness trägt);
  eine eigene Refutation würde nur redundant melden.

---

## Autonome Session 3 (2026-07-27) — Value-Validity, inline-asm-Contracts, Aliasing-Doku; große Reste mit Befund

**Geschiffft (sound, orakel-validiert — Miri RESULT: SOUND):**
- **[x] Value-Validity (`SafetyProperty::ValidValue`)** — die klassische Miri-„invalid value"-UB: ein
  `bool ∉ {0,1}` oder ein Enum-**Diskriminant** außerhalb seiner Menge. Frontend parst LLVM `!range !N`
  (`scan_meta_ranges`/`peek_load_range_meta`), trägt es als `Inst::Load.valid_range = [lo, hi)`
  (nicht-wrappend; wrapping/negativ → `None`, sound). Executor `check_valid_value`: drei-wege,
  **refutation-only** — PASS bei beweisbar in-Range, refutierter FAIL mit Witness nur bei beweisbar
  außerhalb auf exaktem Pfad, sonst UNKNOWN. Kann keinen false PASS erzeugen (additiv).
- **[x] inline-asm via Contracts** — strukturierte-Operanden-Asm (`<inline asm…|w0>`) konsultiert jetzt
  den Basisnamen-Contract; einheitlich mit plainer Asm (die schon oben im Loop matcht).
- **[x] Aliasing-Doku korrigiert** (F/#4): der `NoAliasingViolation`-Kommentar war **stale** — Write-
  durch-`&T`, `&mut`-Use-after-Invalidation und Sibling-Invalidierung sind **implementiert + getestet**
  (part_g), nicht future work. Echte Restlücken jetzt präzise: Cross-Call-Protectors + Tree-Borrows-Gitter.
- **[x] Full-Kernel-Devirt: kompaktierender Copy-Cycle-Collapse (H)** — `ProgramPointsTo::collapse_copy_cycles`:
  Tarjan-SCC über den Copy-(Subset-)Graphen, jede SCC → ein Repräsentant, Survivors **dicht renumeriert**
  (senkt `self.n`), sodass eine Relation, die sonst das Budget überschreitet (und Devirt komplett skippt),
  passt und solved. Verlustfrei/präzisions-erhaltend: `gep`/`load`/`store` schlüsseln auf Offset + (gleiches)
  Points-to-Set, nicht auf Knoten-Identität → Feld-Sensitivität + jeder Devirt-Singleton bleibt. Übersetzt die
  ganze Relation **und** die node-tragenden Seitentabellen (`reg_node`/`global_obj`-Werte, `obj_global`-Keys)
  konsistent; TOP bleibt Knoten 0; Field-Cell-Key-Kollisionen via Copy-Kanten equalisiert; `obj_global`-Namens-
  kollision (praktisch unmöglich) droppt den Eintrag → Devirt lehnt ab statt zu raten (nie falsches Ziel).
  Läuft in `finalize` nach der Deferred-Auflösung (Copy-Graph vollständig), vor `solve`. Validiert: gesamte
  absint-Suite (42) grün + 2 adversariale Zyklus-Tests (Singleton + Feld-durch-Zyklus-Zeiger). **Offen:**
  Kernel-Skala-Rescan zur Messung des tatsächlichen Node-Rückgangs (10,3M → ?) und Devirt-Reaktivierung.

**Deferred mit präzisem Befund (soundness-first: NICHT halb-validiert geschiffft):**
- **[ ] Wide-Ints > 128 bit (C/G)** — **Befund:** der Kern-`csolver_core::BitVector` ist fundamental
  `u128`-basiert (`words:[u64;2]` → immer als ein `u128` rekombiniert; `assert!(width<=128)`). Volle
  Bignum-Unterstützung ist ein Rewrite des **Kern-Werttyps** (value.rs + expr.rs fold_bin/cmp + bitblast
  MAX_WIDTH + lower.rs Konstanten-Clamp + lexer i128-Literale). Ein *halber* Bignum wäre ein Korrektheits-
  risiko im Werttyp, auf dem der **gesamte** Solver ruht — **kein Flag macht einen buggy Kern sound**.
  Aktueller Zustand ist sound: >128-bit-Konstanten → `Const::Undef`/top, Symbolik → linear-Abstraktion.
- **[ ] Echte Inter-Thread-Data-Races (E)** — volles whole-program Happens-Before/Thread-Modell; eine
  gerushte Version riskiert false FAILs. Aktuelle `DataRace`-Deckung: AA-Deadlock + Double-Fetch (sound).
- **[ ] `ValidReference`/`StackIntegrity`/Return-Address (A)** — **Befund:** der Stack-Frame ist EINE
  opake Region ohne unterschiedenen RA-Slot (`x86text::frame_insts`); ein dedizierter RA-Integritäts-Check
  bräuchte einen Frontend-Frame-Umbau (Alloc splitten + neuer `RegionKind`), und die konkreten Korruptions-
  pfade sind bereits durch `InBounds`-OOB / `ValidIndirectTarget` subsumiert (geringe Zusatzausbeute).

---

## A. Genuinely ungeprüft (catalogue-only — echte Löcher)

- [ ] **`ValidReference`** — kein Referenz-Validitäts-Check; die Variante ist zum „Frontend
  konnte Funktion nicht lowern"-Marker umfunktioniert (`verifier/src/run.rs:56`).
- [ ] **`StackIntegrity` / `ValidStackFrame`** — nie emittiert (deklariert als von `InBounds`/
  `ValidIndirectTarget` subsumiert). Return-Address-Integrität hat keinen dedizierten Check.

## B. Prove-only — sound, aber findet Bugs nicht (FAIL nie möglich)

- [x] **`NoNullDeref`** — definite `Null`-Deref refutiert jetzt (Hebel 3, `checks.rs`); opake
  „may-be-null" bleibt prove-only.
- [x] **`Alignment`** — beweisbare Fehlausrichtung wird jetzt refutiert (Session 3b, Basis ≥ aalign + Offset ≢ 0 mod aalign auf exaktem Pfad); sonst UNKNOWN.
- [ ] **`ValidPointerArith`** — Refutation abgeschaltet (`RefuteMode::Off`, reitet auf `InBounds`).

## C. Integer-UB — nur teilweise (alle nur `--bugs`)

Geprüft: Div/Mod-0, Shift-über-Breite, signed/unsigned-Overflow **nur mit `nsw`/`nuw`**. Offen:
- [ ] **plain wrapping** add/sub/mul ohne Flag — keine Obligation (`inst.rs:457`). Soundness-
  Falle: unsigned-wrap ist definiert, signed-ohne-nsw evtl. `-fwrapv`. **← Hebel 2 (nur sound-Teil)**
- [ ] **Truncation** (`size_t`→`int`) — kein dedizierter Check.
- [ ] **signed/unsigned-Verwechslung** — kein dedizierter Check.
- [ ] **Wide-Ints > 128 bit** (`i256`/`i512`) — UB-Checks komplett übersprungen (`step.rs:38`).
- [x] **`var*var`-Allokationsgröße** — n-Faktoren-general (Session 3b): Produkt in Summen-Breite, sofern
  ≤ MAX_WIDTH. Deckt 2 + 3 schmale Faktoren; all-`size_t`-3-Faktoren (192 bit) bleibt Wide-Int-begrenzt.
- [x] Integer-UB im strikten `verify`-Pfad — BEREITS abgedeckt (der `decide`-Gate refutiert div0/shift/
  overflow auf exaktem Pfad, nicht nur unter `--bugs`; Session-3b-Befund).

## D. Nur mit Contract-Korpus (ohne Contracts still)

- [ ] **Capability/`WriteCapability`**, **Taint/`TaintedSink`**, **Typestate/Refcount**,
  **Secret/Constant-Time** — Mechanismus existiert, feuert nur mit `.contract`-Instruktionen.
  Offen: ein mitgelieferter Kernel-Contract-Korpus für out-of-the-box Recall.

## E. Nebenläufigkeit — die größte Lücke

- [ ] **Echte Inter-Thread-Data-Races (G1/G4/G9)** — keine sound Entscheidungsprozedur; `DataRace`
  deckt nur **AA-Self-Deadlock** ab. **← Hebel 1** (happens-before + Lockset-Produkt; laut
  `docs/exploit-taxonomy.md` „die größte Einzelinvestition"). Erster sound Schritt: happens-before-
  Pruning (thread-create-Ordnung) gegen die Eraser-False-Positives.
- [ ] **Lockset/Eraser** (`verifier/src/datarace.rs`) — Heuristik, kein thread-create-HB.
- [ ] **ABBA-Lock-Order** (`verifier/src/lockorder.rs`) — Heuristik, Typ-Collapse-Over-Merge,
  `_nested`/`trylock` nicht unterschieden.
- [ ] **Interleaving/Weak-Memory** (`verifier/src/interleave/`) — bounded 2-Thread-Heuristik.
- [ ] Acquire/Release nur innerhalb der Weak-Memory-Heuristik, nicht als entschiedene Obligation.

## F. Rust-Aliasing (opt-in `--aliasing-model`, Teilklasse) **← Hebel 4**

- [ ] Nur „write-through-shared-`&T`" / „use-of-`&mut`-nach-Reborrow" (`checks.rs:466`). Offen:
  vollständigeres Stacked/Tree-Borrows-Modell (Reborrow-Stacks, `&mut`-Uniqueness über Calls).

## G. Frontend / Decoder — stille UNKNOWNs

- [ ] **Inline-asm** → opaker Call (nur mit strukturierten Mem-Operanden real); `callbr`/asm-goto
  opak; `cmpxchg`-Aggregat opak.
- [ ] **Wide-Ints > 128 bit** nicht repräsentierbar.
- [ ] `unsupported`-Drops zu `unanalyzed`: variable/unsizable struct-gep, switch auf Nicht-Integer,
  Typ-Zyklen.
- [ ] **ASM**: nur Common-Instruction-Subset; unbekannte Mnemonik → Funktion `unanalyzed`.

## H. Skalierbarkeit

- [x] **Whole-program Points-to** (P4-Devirt) — **skalierbarer Worklist-Solver** (nur geänderte
  Knoten neu propagiert, dynamische Copy-Kanten), Feldzellen ohne Debug-Name, `intern_field`-Cap,
  Budget 2M→10M. Kernel (~3,4M Knoten) solved jetzt statt zu no-op-degradieren. (Frontier #1,
  commit `d70d921`; Kernel-Skala per Rescan validiert.)
- [x] **Kompaktierender Copy-Cycle-Collapse** (`collapse_copy_cycles`, Session 3) — SCC-Zyklen-Elimination
  mit Knoten-Renumerierung senkt `self.n`, damit eine sonst-über-Budget-Relation Devirt behält statt zu
  skippen. Verlustfrei, absint-Suite + 2 adversariale Zyklus-Tests grün. Offen: HVN (Hash-Value-Numbering)
  für Nicht-Zyklus-Äquivalenzen; Kernel-Rescan zur Node-Rückgang-Messung.

## Frontier-Fortschritt (2026-07-23, vollständig-autonome Session)

- **#1 skalierbarer Points-to** ✅ (siehe H).
- **#2 vollständige Provenance** — **P2 caller-directed param push** ✅ (`e3de414`), **§3 Feld-Typ-
  Karte** (getypt/offset-0/store-Evidenz) ✅, **§3 Deep-Chains** (mehr-Hop void*-Ketten) ✅
  (`db88164`). Rest: **P3 inttoptr/Idiom-Typisierung** (fuzzy — hinter künftiger
  `--assume-kernel-idioms`-Flag; getypte inttoptr sind via `size_hinted` schon geschlossen).
- **#3 Nebenläufigkeit** — (a)/(b) HB-Pruning + 1a Init-HB + 1b Re-Entrancy ✅ (`3a37714`/`337401e`);
  (c) atomic/READ_ONCE-Exclusion **war bereits implementiert** (step.rs `!*volatile`-Guard); (d)
  Spawn/Join-HB ist **Interleave-Subsystem-Domäne** (weakmem.rs modelliert Spawn-Gating). #3 so
  vollständig wie im Lockset-Ansatz sinnvoll.
- **#4 Rust-Aliasing** — Modell ist bereits echte Stacked-Borrows-Under-Approximation
  (checks.rs:440–494: Reborrow-Stacks, unique/shared, pop-on-write, poison-on-lost-parent).
  „Vervollständigen" = Protectors + `&mut`-Uniqueness über Call-Grenzen — subtil, hohes false-FAIL-
  Risiko (bräche Miri-Orakel), eigener Miri-getriebener Task. **Nicht** als ungetesteter Flag-Patch
  geschifft (soundness-first).

## Autonome Session 2 (2026-07-23) — Miri-Bewertung, Contract-Auto-Gen, P3

- **[x] CSolver-vs-Miri-Bewertung** — `docs/csolver-vs-miri.md`. Komplementär: CSolver beweist über
  ALLE Inputs, multi-language, mit Annahmen-Schicht; Miri beobachtet UB auf ausgeführten Rust-Läufen
  mit höherer Fidelity bei den schwer-statisch-modellierbaren Klassen.
- **[x] `.contract`-Auto-Generierung** — `solver gen-contracts <dir>` (Naming-Heuristik über externe
  Calls) + **`--contracts <dir>`-Lademechanismus** (`init_user_contracts`, fehlte komplett!). Emittiert
  reviewbare Kandidaten, nicht auto-angewendet.
- **[x] P3 inttoptr** — `--assume-inttoptr-valid` (untypisierte inttoptr → assumed valide unsized
  Region; non-null/liveness decides, bounds UNKNOWN).

### Offene Miri-Parität (statisch sinnvoll) + große Reste — mit Design

- [ ] **#4 Stacked/Tree-Borrows vervollständigen** (die größte Rust-Fidelity-Lücke): Retag-
  Derivation-Trees, `&mut`-Use-after-Invalidation, 2-live-`&mut`, Protectors. Braucht Frontend-
  Retag-Events (teils da: `csolver.retag.mut/shared`) + Ableitungsbaum-Tracking im Executor
  (`region_borrows` erweitern). Hinter `--aliasing-model`; hohes false-FAIL-Risiko → Miri-Orakel-
  getrieben validieren.
- [ ] **Value-Validity-Invarianten** (`bool ∉ {0,1}`, ungültiger Enum-Diskriminant, `NonNull`=null):
  neue `ValidValue`-Obligation an getypten Loads (MIR-Frontend kennt die Typen). Statisch geringe
  Ausbeute (nur *beweisbar* ungültige Werte refutierbar), aber im Bug-Finding-Modus findet es
  transmute-von-untrusted-Daten. Frontend muss den Valid-Set am Load markieren.
- [ ] **Echte Inter-Thread-Data-Races** — whole-program Happens-Before/Thread-Modell (jeden Zugriff
  mit Spawn/Entry-Kontext taggen). HB-Pruning/1a/1b sind da; der volle Thread-Kalkül fehlt.
- [ ] **`ValidReference` / `StackIntegrity` / Return-Address-Integrität** — echte Checks statt
  Platzhalter; braucht Stack-Frame-/Canary-Modellierung.
- [ ] **Frontend**: `inttoptr` typisiert ist zu (P3); **Wide-Ints > 128 bit** (Solver-BitVector-
  Breite erweitern — groß), **inline-asm** via Contracts, restliche gep/switch-`unsupported`-Drops.
- [ ] **Float-UB**, **unwind-across-FFI** — Miri deckt sie ab; für einen statischen Solver Nische.

## Doku-Diskrepanz

- [ ] `docs/exploit-taxonomy.md` behauptet „jede Klasse ●" — die ●-Marks meinen *Mechanismus
  existiert*, nicht *out-of-the-box Recall*. Zeilen-Marks an die ehrlichere „Assessment"-Sektion
  angleichen.

---

## Hebel 1–4 — Stand (autonome Bearbeitung 2026-07-23)

3. **[x] `NoNullDeref` decided** — definite `Prov::Null`-Deref (oder pfad-erzwungene addr==0)
   refutiert jetzt auf exaktem/feasiblem Pfad (`checks.rs`); opake may-be-null bleibt prove-only.
   Commit `63ca5f6`. Orakel SOUND.
2. **[x] Integer-UB (sound-Teil)** — `var*var`-Allokations-Overflow in doppelter Breite geprüft
   (`size_overflow_goal`). Commit `0c8d00d`. Bewusst NICHT: nsw/nuw-Checks im strikten Verify
   (unbeweisbar für opake Inputs → Recall-Verlust; Integer-Overflow außerhalb Kern-Memory-Safety).

1. **[~] Inter-Thread-Data-Race** — **erster sound Increment erledigt; volle HB-Frontier offen.**
   - **[x] Happens-before-Pruning** (`detect_races(accesses, concurrent)`): nur Zugriffe aus
     *konkurrent-erreichbaren* Funktionen (die bestehende `whole_program_concurrent`-Closure:
     erreichbar von Entry oder Spawn-Target) zählen. Ein `module_init`/Setup-Helper, der eine
     Location ungelockt vor jedem Runtime-Handler berührt, vergiftet nicht mehr das Candidate-
     Lockset — die dominante Eraser-FP fällt weg. Sound (Über-Approx, verliert keinen echten Race).
   - **[x] trylock-ABBA-FP** ist bereits gemildert — `lock_acquire("spin_trylock")` gibt `None`.
   - **[x] 1a Init-happens-before-Runtime als echte Kante** — Device-Lifecycle-Callbacks
     (`*_probe`/`*_remove`/`*_shutdown`/`module_init`/`module_exit`, `is_init_lifecycle`) laufen
     einmalig sequenziell und werden aus dem Concurrent-Seed **und** aus der Indirect-Call-Über-
     Approximation (`addr_fns`) ausgeschlossen — sie werden also nicht mehr fälschlich konkurrent,
     wenn irgendeine konkurrente Funktion indirekt aufruft. Direct-Reachability in sie bleibt (echt
     konkurrenter Kontext). Recall-Rest: IRQ-während-Probe nicht modelliert (dokumentiert).
   - **[x] 1b same-Entry-Re-Entrancy** — bei aktivem Oracle genügt **eine** konkurrente Funktion
     mit inkonsistentem Lockset (`min_fns=1`): ein Syscall/ops-Handler auf N CPUs racet mit einer
     konkurrenten Instanz seiner selbst, was der `≥2`-Proxy verfehlte.
   - **[ ] Rest offen:** (c) `atomic`/`READ_ONCE`/per-CPU-Zugriffe als race-frei taggen (braucht
     einen Access-Flag im Executor); (d) Spawn-before-child + Join-after HB als echte Ordnung in
     die Lockset-Relation (statt nur Concurrent-Membership).
4. **[~] Rust-Aliasing** — **bereits substanzieller als der Audit sagte.** `checks.rs:440–494`
   implementiert echte Stacked-Borrows-Under-Approximation: Reborrow-Stacks (`region_borrows`),
   Tags, unique/shared-Unterscheidung, pop-on-write, poison-on-lost-parent. „Vervollständigen"
   heißt Protector/Two-Phase-Borrows + `&mut`-Uniqueness über Call-Grenzen — subtil, groß, und ein
   falscher FAIL hier wäre unsound. Eigener fokussierter Task; kein Schnellpatch.

**Fazit:** 2 & 3 sind sound erledigt (+ der kritische P4-OOM-Fix `4c07ead`). 1 & 4 sind echte
Mehr-Session-Komponenten (whole-program HB-Modell bzw. vollständige Borrow-Semantik); soundness-first
verbietet einen marginalen/unsicheren Teilpatch. Nächster großer Task hier: das HB/Thread-Modell (1).
