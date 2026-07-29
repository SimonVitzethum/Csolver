# Konkreter Arbeitsplan: UNKNOWN ≤ 3 % (≥ 97 % decided)

**Stand:** 2026-07-29. Diese Fassung **ersetzt** die Prognostik-Roadmap vom 2026-07-23 vollständig.
Die alte Fassung war eine Schätzung ohne Messgrundlage; drei ihrer tragenden Annahmen sind
inzwischen empirisch widerlegt (siehe [`unknown-to-5pct-plan.md`], Befunde 1–3), und ihre
Residual-Tabelle stammt aus einem Sample, dessen Auswertung nachweislich fehlerhaft war.

Dieser Plan ist **nicht** ein zweiter, konkurrierender Weg neben [`unknown-to-5pct-plan.md`].
Es ist derselbe Rumpf, zu Ende gedacht:

> **≤ 5 % ist die Analyse-Arbeit. Die letzten 2 pp auf ≤ 3 % sind Scoping + Annahmen-Buchhaltung,
> keine zusätzliche Analyse-Präzision.**

Wer nur eines von beiden liest: der 5-%-Plan enthält die Diagnose (*warum* steckt die Decided-Rate
bei 28 %), dieser hier die Arbeitspakete (*was genau zu tun ist, woran man Erfolg misst*).

**Kardinalregel unverändert:** nie ein false PASS. Unsound-im-Allgemeinen nur hinter benannter, im
Proof-Tree sichtbarer Annahme; beide Orakel (Miri + C-ASan/UBSan) pro Schritt.

---

## 0. Ausgangslage (gemessen, 2026-07-27)

| Korpus | Funktionen | PASS | FAIL | UNKNOWN | decided |
|---|---|---|---|---|---|
| `mm` (offen) | 5782 | 25,2 % | 2,2 % | 72,6 % | 27,4 % |
| `mm` + `--assume-inttoptr-valid` | 5782 | 25,2 % | 2,2 % | 72,7 % | 27,3 % |
| `kernel` (`--closed-world`) | 15439 | 26,9 % | 1,9 % | 71,2 % | 28,8 % |

Eine **abgeschlossene** Whole-Kernel-Zahl (37k) gibt es weiterhin nicht — jeder Lauf starb in Pass 2
mit exit 143, bevor das `== coverage ==`-Summary gedruckt wurde. Das ist AP-0.1.

## 0b. Was der Code-Audit vom 2026-07-29 an den Plänen korrigiert hat

Ein Abgleich jedes offenen Punkts gegen den Quelltext ergab vier Einträge, die **stale** waren, und
einen neuen, planrelevanten Befund:

- **Stacked-Borrows-Protectors sind gebaut** (`mir/lower.rs:208` Entry-Retag für `&mut`-Parameter,
  `symbolic/exec/step.rs:474-484` interprozeduraler Protector an Call-Argumenten, `two_phase` als
  shared Reborrow in `mir/parser/expr.rs:148`, Tests in `testsuite/tests/mir_frontend/part_c.rs`;
  Commit `9231b06`). Offen ist nur noch das **volle Tree-Borrows-Gitter** und exaktes `UnsafeCell`.
- **`docs/exploit-taxonomy.md` ist bereits ehrlich** (Legende Zeile 34; 40 ● / 16 ◐ / 6 ○,
  Commit `cc2d270`). Der „behauptet jede Klasse ●"-Nit ist erledigt.
- **ARM64 CBZ/ADRP/BLR existieren im Text-Decoder** (`asm/arm64_text.rs:178/204/158`). Die Lücke
  betrifft **nur** den Maschinencode-Decoder (`asm/arm64.rs`, erklärtermaßen „small, growing
  subset"). `tbz`/`tbnz` fehlt in beiden.
- **`ValidReference` ist nicht bloß ein Frontend-Marker.** Ja, `verifier/run.rs:62` missbraucht die
  Variante als Drop-Marker — aber `memory/access.rs:145,156` emittiert sie als echtes Residual
  (opake Provenance, untracked region), und `csolver-memory` hängt real an symbolic/verifier/
  solver/absint.
- **NEU und planrelevant:** `verifier/wholeprog.rs:119` befüllt `field_types` **ausschließlich unter
  `closed_world`** — sonst bleibt die Map leer. Der `mm`-Lauf mit 72,6 % UNKNOWN lief **ohne**
  `--closed-world`; dort war die §3-Feld-Typ-Karte also strukturell wirkungslos. Das ist ein
  billig prüfbarer Kandidat für „warum feuert 1a unterproportional" und wird als **AP-1.0 vor allen
  anderen Phase-1-Paketen** gemessen.

---

## 1. Warum ≤ 3 % ohne Annahmen-Schicht unerreichbar ist

Unverändert gültig aus der alten Fassung, jetzt aber mit Zahlen unterlegt:

1. **Sound-decided** (PASS/FAIL ohne jede Annahme): realistische Decke **~80–88 %**. Das ist
   deutlich pessimistischer als die alten „93–95 %" — Befund 1 (Funktions-decided ist durch die
   *schlechteste* Obligation gedeckelt) macht die Decke zu einem Produkt, nicht zu einer Summe.
2. **Decided-unter-benannter-Annahme**: PASS/FAIL auf einer ausgewiesenen, opt-in Annahme.

≤ 3 % UNKNOWN heißt also konkret: **≥ 97 % decided, davon ~80–88 pp strikt-sound und ~9–17 pp unter
benannten Annahmen.** Jede Zahl ist an ihr Annahmen-Bündel gebunden; ohne AP-0.2 (Report-Split) ist
sie schlicht nicht interpretierbar. Deshalb steht AP-0.2 **vor** jeder Präzisionsarbeit.

---

## 2. Arbeitspakete

Jedes Paket: **Anker** (wo im Code), **Schritte**, **Akzeptanzkriterium** (woran Erfolg gemessen
wird — nicht „fühlt sich besser an"), **Soundness**, **Abhängigkeit**.

### AP-0.1 — Abgeschlossener Full-Kernel-Scan `[Werkzeugseite erledigt 2026-07-29]`

- **Anker:** `cli/scan_dir.rs` (`scan_report`, Checkpoint-Automatik, `CKPT_*`-Konstanten),
  `cli/scan.rs:251-280` (`CSOLVER_MEM_TARGET_MB`, default ~70 % frei; `CSOLVER_MEM_FACTOR`),
  `cli/scan.rs:358-365` (`CSOLVER_MEM_RESERVE_MB`), `cli/scan_run.rs:396` (RSS-Sampling).
- **Befund:** die Infrastruktur war vollständig vorhanden — exit 143 ist eine Lauf-, keine
  Code-Frage. Was fehlte, war ein Weg, einen *gekillten* Lauf trotzdem auszuwerten: der
  Checkpoint ist opt-in, und ohne gesetzte Env-Variable hinterließen die 37k-Läufe nichts.

**Der geplante SIGTERM-Handler wurde verworfen — aus zwei Gründen, der zweite ist der wichtige:**
`unsafe_code = "forbid"` (Cargo.toml:56, per `allow` nicht aufhebbar) und null externe Crates
schließen einen Handler ohnehin aus. Entscheidender: **der OOM-Killer schickt SIGKILL, und den
fängt kein Handler.** Ein Handler hätte ausgerechnet den wahrscheinlichsten Fall nicht gerettet.

**Stattdessen umgesetzt — der Checkpoint trägt den Report, nicht der Prozess:**

- **`solver scan-report <ckpt>`** druckt den vollen Coverage-Report (Findings, Histogramm,
  0d-Split, Attribution) aus der Checkpoint-Datei allein. Ein gekillter Lauf ist damit eine
  Messung — bei TERM, bei KILL, bei Stromausfall.
- **Checkpoint ab `CKPT_AUTO_UNITS = 5000` per Default an** (`./csolver-scan.ckpt`;
  `CSOLVER_SCAN_CHECKPOINT=<file>` verschiebt, `CSOLVER_SCAN_CHECKPOINT=` schaltet ab). Das war
  vermutlich die Ursache dafür, dass die bisherigen Läufe nichts hinterließen.
- **Zeitgetriggertes Schreiben** (`CKPT_MAX_SECS = 120`) zusätzlich zum Alle-50-Units — 50 Units
  eines schweren Teilbaums können viele Minuten sein, und dieses Fenster ginge sonst verloren.
- **Peak-RSS im Checkpoint.** Das ist die Diagnose, die dieser Punkt verlangte: ein Wert an der
  Maschinengrenze ist die Signatur des OOM-Killers (SIGKILL, exit 137), ein moderater deutet auf
  einen externen Terminator (SIGTERM, exit 143 — `timeout`, Scheduler, Session-Abbau).

- **Verifiziert am synthetischen 5100-Unit-Korpus:** Lauf bei 350/5100 Units mit `SIGKILL`
  erschlagen, Prozess druckte **nichts** (0 `== coverage ==` im Log, exit 137); `scan-report` auf
  dem hinterlassenen Checkpoint liefert den vollständigen Report über die 500 fertigen Units
  inklusive Split und Peak-RSS. Genau der Fall, an dem AP-0.1 hing.
- **Weiterhin offen — und nur auf echter Hardware zu erledigen:** der 37k-Lauf selbst. Der
  Kernel-Korpus liegt nicht im Container. Nächster Schritt ist ein Rerun mit einem
  `CSOLVER_MEM_TARGET_MB` unterhalb der Box-Grenze; wenn er wieder stirbt, sagt jetzt der
  Peak-RSS im Checkpoint, ob es der Speicher war.
- **Akzeptanz (unverändert):** eine abgeschlossene 37k-Zahl. Diese ist ab dann *die* Referenzzahl;
  alle pp-Angaben unten beziehen sich darauf. Bis dahin gilt: ein abgebrochener Lauf liefert
  jetzt wenigstens eine ehrlich als partiell ausgewiesene Teilmessung.
- **Soundness:** n/a (Messinfrastruktur).

### AP-0.2 — Report-Split (sound / unter-Annahme / genuin-hart) ✅ **erledigt 2026-07-29**

- **Anker:** `verifier/report.rs` (`FunctionReport::assumption_footprint` / `is_sound_decided`),
  `cli/scan_run.rs` (`tally_assumptions`), `cli/findings.rs` (`report_assumption_split`),
  `cli/scan_dir.rs` (Aggregation + Checkpoint-Format 2).
- **Befund bei der Umsetzung:** das Rohmaterial lag vollständig vor — `ProofTree.assumptions`
  trägt die IDs seit jeher, `run.rs` sammelte sie nur modulweit ein, ohne Zuordnung zur Funktion.
  Es war reine Buchhaltung, keine neue Analyse.
- **Umgesetzt:** jede *entschiedene* Funktion bekommt ihren Assumption-Fußabdruck (Vereinigung
  über alle ihre Obligations — bei FAIL bewusst auch über die nicht-refutierten, denn der Zustand,
  in dem der Zeuge gefunden wurde, kann von einer Annahme geformt sein). Leerer Fußabdruck →
  sound-decided. Die Ausgabe zeigt die drei Buckets plus eine Attributionstabelle, und der
  Checkpoint trägt beides über einen Resume (Format-Version 2; eine Version-1-Datei wird
  **abgelehnt** statt fortgesetzt — sie hätte Decided-Zähler ohne Fußabdruck und würde einen
  stillschweigend zu kleinen Sound-Bucket drucken).
- **Erste Messung** (`tests/dwarf-corpus`, 38 Funktionen, Standardflags): 27 decided, davon
  **11 sound** und 16 unter Annahme. Also ~59 % der decided-Rate ruhen auf einer Annahme.
- **Wichtiger Befund aus dem Differential — die Attribution ist eine Klammer, kein Wert.**
  `param-valid` stand mit `touching 10 / sole 3` in der Tabelle. Ein Rerun mit
  `--no-assume-valid-params` kostete **10** entschiedene Funktionen, nicht 3: der Sole-Wert ist
  eine **untere** Schranke (eine Funktion mit drei Annahmen kann alle drei brauchen), der
  Touching-Wert eine **obere**. Die exakte Zahl liefert nur ein Differential-Rerun mit
  abgeschalteter Annahme. Der Report sagt das jetzt selbst dazu, statt eine Spalte zu wählen und
  Präzision zu suggerieren, die sie nicht hat. Kontrollpunkt derselben Messung: sound-decided
  blieb bei genau 11, während decided von 27 auf 17 fiel — der Split misst also das Richtige.
- **Soundness:** der Split *verschärft* die Aussage (er entzieht der Gesamtzahl die Annahmen).
- **Noch offen aus dem ursprünglichen Zuschnitt:** die Was-wäre-wenn-Spalte („dieses UNKNOWN
  würde unter einem *nicht aktivierten* Bündel decided") fehlt. Sie braucht einen Mehrfachlauf
  oder eine Annahmen-Gegenrechnung im Executor und ist damit kein Buchhaltungsposten mehr —
  sie wandert zu **AP-6.2**, wo sie ohnehin gebraucht wird.

### AP-1.0 — Das `closed_world`-Gate der Feld-Typ-Karte messen `[neu, Audit 2026-07-29]`

- **Anker:** `verifier/wholeprog.rs:119` (`field_types` nur unter `closed_world`, sonst leer),
  `wholeprog.rs:36/222`, `verifier/run.rs:240-282` (Ketten-Fixpunkt),
  `symbolic/exec/calls.rs:563` (`size_hinted_pointer`), verdrahtet in `exec/step.rs:21,316`.
- **Schritte:** `mm` einmal **mit** `--closed-world` gegen den bekannten Lauf ohne rechnen. Zwei
  mögliche Ausgänge, beide wertvoll: springt decided deutlich → §3 wirkt, und die 72,6-%-Zahl war
  schlicht gegen die falsche Konfiguration gemessen. Springt es nicht → §3 hat ein echtes Loch,
  und AP-1.1 wird pro-Residual-Debugging statt Vervollständigung.
- **Akzeptanz:** eine Zahl, kein Eindruck. Dazu die Frage beantwortet, ob eine **open-world-taugliche
  Teilmenge** der Feld-Evidenz (Feld-Typen aus demselben Modul, ohne Whole-Program-Overlay) sound
  konstruierbar ist — wenn ja, ist das der billigste Hebel im ganzen Plan.
- **Soundness:** reine Messung. **Abhängigkeit:** AP-0.1 wäre schöner, ist aber nicht nötig
  (`mm` läuft durch). **Vor AP-1.1/1.2/1.3.**

### AP-1.1 — Feld-Typ-Karte end-to-end vervollständigen

- **Schritte:** pro dominanter Residual-Ursache prüfen, ob die `(struct, offset) → pointee`-Karte
  für `void*`/`union`/`private_data`-Loads einen Typ liefert **und** ob `size_hinted_pointer` damit
  greift. Bekannte Einschränkung: `size_hinted_pointer` feuert laut `verifier/run.rs:325` nur auf
  `Prov::Unknown` — ein Zeiger, der schon eine schwache, größenlose Provenance trägt, wird nicht
  nachträglich dimensioniert. Das ist zu prüfen und ggf. zu erweitern.
- **Akzeptanz:** ein benanntes Residual-Muster verschwindet **und** die betroffenen Funktionen
  kippen auf decided (Befund 2: Klassen-Reduktion ohne Funktions-Flip ist kein Fortschritt).
- **Soundness:** `--closed-world` / `--assume-valid-params`, benannt. **Abhängigkeit:** AP-1.0.

### AP-1.2 — `RetSummary::Field { arg, offset, pointee }`

- **Anker:** `symbolic/summary.rs:91`. Bestand heute: `Unknown`, `Scalar`, `PtrFromArg`,
  `DanglingStack`, `Alloc`, `ValidRef`. **`Field` fehlt** (verifiziert 2026-07-29).
- **Schritte:** Variante ergänzen; Ableitung im Summary-Fixpunkt (Callee gibt auf jedem Pfad
  `&arg->feld` bei beliebigem Offset zurück); Pointee-Typ aus AP-1.1; Anwendung an der Call-Site
  analog zu `Alloc`/`ValidRef`, also **mit Größe**, damit die In-Bounds-Kaskade wirklich löst
  (Befund 3).
- **Akzeptanz:** Residual „loaded value (untyped, no store-load prov)" sinkt messbar **und** Feld-
  Accessor-lastige Funktionen kippen. Regressionstests: Offset ≠ 0, Kette über zwei Hops.
- **Soundness:** interprozedural unter denselben benannten Annahmen. **Abhängigkeit:** AP-1.1.

### AP-1.3 — Param-Closure (P2) auf Kernel/Rust ausweiten

- **Anker:** `symbolic/lib.rs:75-81`, `verifier/run.rs:124-127`, `symbolic/exec/step_mem.rs:10-12`,
  `llvm/lower.rs:408`, `elf/dwarf.rs:3`.
- **Schritte:** jeder rohe Pointer-Parameter bekommt die schwächste Caller-Garantie **inklusive
  Größe** (aus dem getypten Argument, nicht nur aus `alloca`). Für C/C++ validiert; auf Kernel/Rust
  ausdehnen. **Akzeptanz:** „uncontracted parameter" fällt, und zwar *mit* Größe.

### AP-2.1 — Kernel-Idiom-Größen (`--assume-kernel-idioms`)

`page` → `PAGE_SIZE`, per-cpu-Var → Typgröße, `phys_to_virt`/`__va` → Mapping-Größe, `container_of`
→ Container-Typgröße, `ERR_PTR`/`IS_ERR` → auf der `!IS_ERR`-Kante valide. Als Contract-/Idiom-
Tabelle, damit die materialisierte Region eine **Größe** trägt — genau der Grund, warum
`--assume-inttoptr-valid` allein nichts brachte. **Soundness:** opt-in, benannt; die Idiome sind
kernelspezifische Fakten, kein strikt-sound. **Akzeptanz:** die 22.551 in-bounds-Residuen aus dem
inttoptr-Experiment sinken, und Funktionen kippen.

### AP-2.2 — Guarded-Access-Beweis breiter

Ein größenloser, aber durch `if (i < n)` beschränkter Zugriff PROVEt in-bounds auch ohne
Region-Größe (bestehender `assume_guarded_index` / `--assume-field-invariants`, Muster auf
Feld-Länge und Loop-Bound erweitern).

### AP-3.1 — Container-Invarianten

`list_for_each_entry`, `hlist`, `rb_node`, `xarray`, `llist`: der Iterator bleibt in gültigen,
**dimensionierten** Knoten des deklarierten Typs (Contract, opt-in). Adressiert den zweitgrößten
Block im Histogramm.

### AP-3.2 — Induktions-Breite

Mehrdimensionale Arrays, verschachtelte Loops, Sentinel-Loops (`strlen`/`memchr`).

- **Anker/Messhinweis:** das Residual kommt aus `verifier/discharge.rs:315` („reached but not
  decided by the symbolic memory model: loop body or unsupported op"). Wichtig: die
  **Visit-Budget-Truncation ist ein eigener String** (`discharge.rs:313`) — die 11.230 sind also
  echt Loop/unsupported und keine verkappte Budget-Abschneidung. Die Zahl ist sauber.
- **Akzeptanz:** dieser eine String sinkt; getrennt ausweisen von `discharge.rs:313`.

### AP-4.1 — HVN (Hash-Value-Numbering)

- **Befund:** im ganzen Baum **null Treffer** für HVN/Value-Numbering — nicht angefangen
  (verifiziert 2026-07-29).
- **Warum es das Paket der Phase ist:** der Copy-Cycle-Collapse (`collapse_copy_cycles`) ist auf dem
  Kernel empirisch ein **No-op** (14.190.344 → 14.190.302 Knoten, 0,0 %; der Copy-Graph ist ein
  DAG). Damit bleibt Full-Kernel-Devirt budget-übersprungen (14,2M > 10M). Ohne HVN ist Phase 4
  auf dem Kernel wirkungslos.
- **Schritte:** offline Knoten mit identischer Points-to-Signatur (address-of-Quellen + eingehende
  Copy-Menge) mergen, analog zur bestehenden Renumerierung.
- **Soundness:** sound-für-Devirt — Merge *vergrößert* Sets nur, ein Singleton kann dadurch
  verschwinden, aber nie falsch entstehen. **Akzeptanz:** Knotenzahl unter das 10M-Budget; Devirt
  läuft auf dem Kernel überhaupt an. Adversariale Tests wie beim Cycle-Collapse.
- **Alternative, dokumentiert verworfen:** Budget-Raise — 24 GB RSS bei 14M Knoten in diesem Lauf.

### AP-4.2 — Devirt-Breite

vtable-/fnptr-Felder aus dem Closed-World-Initializer, `ops`-Registertabellen,
`static const struct …_ops`. Großer Ketten-Multiplikator: ein aufgelöster indirekter Call entsperrt
viele Downstream-Obligations **in derselben Funktion** — genau, was Befund 2 verlangt.

### AP-5.1 — Frontend-Drops

Multi-Index-/Vektor-`getelementptr`, switch auf Nicht-Integer, Typ-Zyklen. Jeder Drop ist teuer
(ganze Funktion = ein UNKNOWN), die Zahl ist aber klein (1–4 pro Subset).

### AP-5.2 — Wide-Ints > 128 bit

- **Anker:** `core/value.rs:27` (`words: [u64; 2]`), `solver/bitblast.rs:31` (`MAX_WIDTH = 128`),
  `solver/blaster.rs:52` (alles darüber abgewiesen).
- **Einordnung:** ein Rewrite des **zentralen Werttyps**, auf dem der gesamte Solver ruht. Der
  aktuelle Zustand ist sound (> 128 bit → `Const::Undef`/top). **Ein halber Bignum wäre ein
  Korrektheitsrisiko im Kern — kein Flag macht einen buggy Werttyp sound.** Dieses Paket ist
  bewusst **spät** und wird nur angefasst, wenn AP-0.1 zeigt, dass Crypto/SIMD messbar wehtut.

### AP-5.3 — ASM-Breite

Offen und verifiziert: x86 String-Ops (`rep movs/stos/scas/lods`) fehlen in **beiden** Decodern;
`cmpxchg`/`xadd` werden nicht dekodiert (nur der LOCK-Präfix-Fence ist modelliert,
`asm/x86/lower.rs:16`); SSE/AVX nur Länge + Disassembly-Namen, keine Semantik; x87 gar nicht.
ARM64: `tbz`/`tbnz` fehlen; Register-Form-ALU, LDP mit Register-Offset, `mul`/`udiv`/`sdiv`,
`cbz`/`adrp`/`blr` fehlen **im Maschinencode-Decoder** (`asm/arm64.rs`) — im Text-Decoder sind sie
da. Unbekannte Mnemonik → `unanalyzed`, also sound-degradiert.

### AP-6.1 — Attack-Surface-Scoping (`--attack-surface` + `--closed-world`)

Nur syscall/ioctl-erreichbarer Code braucht adversariale Parameter. Der Rest darf Caller-etablierte,
**dimensionierte** Invarianten annehmen → decided-unter-Annahme. Verschiebt den genuin harten Kern
auf die tatsächlich erreichbare Angriffsfläche.

### AP-6.2 — Annahmen-Buchhaltung (hier entsteht die 3 %)

Der Rest-*harte* Kern — kein Annahmen-Bündel schließt ihn — ist die ehrliche Zahl. Ziel: **< 1 %
genuin hart, < 2 % decided-unter-Annahme.** Baut direkt auf AP-0.2 auf; ohne den Split ist AP-6.2
nicht formulierbar.

---

## 3. Trajektorie (mit Bandbreite, nicht als Punktprognose)

| Nach | UNKNOWN | decided | tragend |
|---|---|---|---|
| heute | ~72 % | ~28 % | — |
| AP-0 | ~72 % | ~28 % | jetzt *steuerbar* |
| AP-1 | 45–52 % | 48–55 % | **nur** wenn Größe geliefert wird (Befund 3) |
| AP-2 | 35–42 % | 58–65 % | benannte Idiome |
| AP-3 | 28–35 % | 65–72 % | Loops/Container |
| AP-4 | 20–28 % | 72–80 % | HVN ist Voraussetzung |
| AP-5 | 18–26 % | 74–82 % | Drops |
| AP-6 | **≤ 3 %** | **≥ 97 %** | ~80–88 pp sound + ~9–17 pp unter Annahme |

Die alte Fassung prognostizierte −50 pp allein aus Phase A. Das tritt nicht ein: Funktionen sind
multi-kausal (Befund 2), und Provenance ohne Größe verschiebt das Residual nur (Befund 3). Es gibt
**keinen** einzelnen −50-pp-Sprung; die Zahl entsteht aus allen Paketen zusammen.

## 4. Reihenfolge

1. ~~**AP-0.2**~~ ✅ und ~~**AP-0.1 (Werkzeugseite)**~~ ✅ erledigt (2026-07-29). Offen bleibt der
   **37k-Lauf selbst** — er braucht echte Hardware, nicht mehr Code. Ohne ihn hat der Split keine
   belastbare Grundgesamtheit.
2. **AP-1.0** — eine Messung, potenziell der billigste Hebel im Plan.
3. **AP-1.1 → 1.2 → 1.3**, jeweils erst nach bestandenem Akzeptanzkriterium des Vorgängers.
4. **AP-3** früh (großer, provenance-**un**abhängiger Block).
5. **AP-4.1 vor 4.2** — ohne HVN ist 4.2 auf dem Kernel wirkungslos.
6. **AP-2, AP-5** parallelisierbar.
7. **AP-6** zuletzt.

## 5. Wann dieser Plan sein Ziel verfehlt (ehrliche Abbruchkriterien)

- **AP-1.0 zeigt keinen Sprung und AP-1.1 findet kein Loch** → Befund 3 ist noch stärker als
  angenommen; die Trajektorie ab AP-1 ist neu zu schätzen, bevor AP-1.2/1.3 gebaut werden.
- **HVN bringt die Knotenzahl nicht unter das Budget** → Phase 4 ist auf dem Kernel tot, −3 bis
  −5 pp entfallen ersatzlos, und ≤ 3 % braucht entsprechend mehr aus der Annahmen-Schicht.
- **AP-0.2 zeigt, dass die Annahmen-Schicht > 17 pp tragen müsste** → dann ist „≥ 97 % decided"
  zwar formal erreichbar, aber die Aussage so schwach, dass die 5-%-Zahl die ehrlichere Kennzahl
  ist. Das ist explizit ein akzeptables Ergebnis; **die Zahl darf nicht das Ziel ersetzen.**

## 6. Mess- & Soundness-Disziplin (jedes Paket)

1. **Vor Merge:** Miri + C-ASan/UBSan SOUND (0 false PASS / 0 false FAIL), volle Testsuite, clippy.
2. **Fortschritt** per abgeschlossenem Kernel-Scan (AP-0.1), decided auf **Funktions**-Ebene, plus
   ein frisches Residual-Histogramm — und die Frage „kippten Funktionen wirklich?" (Befund 2).
3. **Jede Annahme** als benannte Assumption im Proof-Tree; Report-Split sound/Annahme/hart (AP-0.2).
4. **Differential testet die Annahmen-Bündel mit** — ein Bündel, das einen Orakel-UB-Fall zu PASS
   macht, ist ein Bug im Bündel.

[`unknown-to-5pct-plan.md`]: ./unknown-to-5pct-plan.md
