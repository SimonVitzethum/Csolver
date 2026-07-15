# Todo — Schwächen & Risiken aus dem Code-Review (2026-07-13)

## MESSFEHLER korrigiert (2026-07-14) — Benchmark-Sample war unrepräsentativ

Zwei Fehler in der eigenen Auswertung, beide korrigiert:

1. **Kaputtes Residual-Parsing.** Der Residual-Text hat *verschachtelte* Klammern
   (`… (scalar-as-pointer (copy root unclassified: …))`). Ein `awk`, das die letzte
   Klammergruppe nahm, ordnete Ursachen systematisch falsch zu. Immer die **erste**
   öffnende Klammer nach `residual:` bis zum Zeilenende nehmen.
2. **Unrepräsentatives Sample.** Das 50-Datei-Kernel-Sample hatte nur **10 %** Debug-Info,
   das Korpus hat **98 %** (36.779/37.594 `.ll` mit `DICompositeType`). Es war also genau
   gegen die DWARF-Recovery verzerrt. Auf einem repräsentativen Sample (48/50 mit DWARF):
   **307 PASS / 16 FAIL / 523 UNKNOWN → Decided-Rate 38 %** (nicht 45 %).

**Konsequenz für die Priorisierung:** Es gibt **keinen Solo-Hebel**. 439 der 523 UNKNOWN
(84 %) hängen an *mehreren* Ursachen gleichzeitig. Häufigkeit über die UNKNOWN-Funktionen:
`bounds` 376 (72 %), `offset` 361 (69 %), `null?` 192, `loaded` 109, `align` 94.
`bounds`/`offset` sind **keine** Provenance-Lücken — Region und Größe sind bekannt, nur der
Index ist nicht beweisbar. Der Engpass ist also **Bounds-Präzision**, nicht Typinfo.

- [x] **C `(buf, len)`-Paarung** → `--assume-param-buffer-len` (Flagge, `param-buffer-len`).
  Erkennt auch den Fall, wo der Index aus der Länge *abgeleitet* ist (`buf[len-4]`). Bewusst
  NICHT in `used_as_length` gefaltet: das ist auch die Evidenz für Rusts *vertrauten*
  `slice-abi`-Contract, und ein abgeleiteter Index könnte dort einen Index-Parameter zur
  Phantom-Länge machen → false PASS. Nebenbei gefixt: C-Längen sind meist 32-bit, der
  Slice-Contract erwartete 64-bit `usize` → Breiten-Mismatch, `zext` vor der Multiplikation.
  **Wirkung auf dem Kernel-Sample: 0 Funktionen** (die Paarung greift, aber die betroffenen
  Funktionen blockieren an anderer Ursache).
- [x] **„Kontext hinter der Struktur"-Idiom** → `--assume-struct-tail` (Flagge, `struct-tail`).
  `gep %struct.T, ptr %p, i64 k` (k≥1) navigiert *in* Element k, dessen Ende bei
  `(k+1)·sizeof(T)` liegt → Region auf diese Reichweite vergrößern. Beide gep-Formen nötig:
  ein-indiziges `Gep` (`tfm + 1`) **und** `GepChain` (`tfm[1].feld`). Eingehängt an *drei*
  Stellen, weil ein Parameter je nach Herkunft unterschiedliche Pfade nimmt:
  `run.rs` (DWARF-`raw_ptr_hints` → Contract — der Pfad, der real greift), `driver.rs`
  (uncontracted Param) und `calls.rs` (`size_hinted_pointer`).
  **Nicht vakuum:** konstante Offsets werden durch eine `assumed`-Region ohnehin nie
  widerlegt, also geht keine Bug-Findung verloren — nur UNKNOWN → PASS. Risiko (im README):
  ein *symbolischer* Index könnte in den angenommenen Tail überlaufen.
  **Wirkung (repräsentatives Sample, zusammen mit `--assume-param-buffer-len`):
  307 → 314 PASS, FAIL unverändert 16, Default bit-identisch.**

- [x] **ioremap-API-Erkennung (Phase 1–3, 2026-07-15).**
  - **Phase 1 (sound, ohne Flagge):** `crates/contracts/data/mmio.contract` — die size-tragenden
    APIs (`ioremap(phys,size)`, `devm_ioremap(dev,off,size)`) via neuem `mmio`-Effekt als
    **initialisierte** `RegionKind::Global`-Region (extern vom Gerät initialisiert → ein
    Register-Read ist kein uninit-Read-FAIL; Bounds bleiben widerlegbar). Behob nebenbei den
    zeroing-Allocator-TODO-Mechanismus.
  - **Phase 2 (sound, Default):** `iomem`-Label auf *jeder* ioremap-Rückgabe (auch der
    größenlosen: `of_iomap`, `devm_platform_ioremap_resource`, `pci_iomap`). Nötig dafür:
    `label ret` (Label auf Rückgabe, deferred nach der Ergebnis-Bindung); und der
    Prov-Interner ist jetzt in der contracts-Crate (eine Quelle, damit Label-IDs zwischen
    Frontend und Executor übereinstimmen).
  - **Phase 3 (Flagge `--assume-valid-mmio`):** ein Zugriff/Offset durch einen
    `iomem`-gelabelten Zeiger gilt als innerhalb des Mappings — prove-only, widerlegt nie.
    **Wirkung (repräsentatives Sample): +1 Funktion (314→315), Default unverändert.**
- [ ] **LIMITIERUNG von Phase 2/3: cross-function Feld-Provenance.** Der *dominante* Treiber-Fall
  (`xgene_clk_pll_is_enabled`) bleibt UNKNOWN: `of_iomap`-Rückgabe wird in `probe` in ein
  Struct-Feld gestoret und in `is_enabled` geladen — das `iomem`-Label fließt aber **nicht**
  cross-function durch ein Feld (Labels reisen nur über `ProvTransfer`-Summaries für
  *Argumente*, nicht für Feldwerte). Der intra-funktionale und der Direkt-Rückgabe-Fall sind
  abgedeckt. Zum Schließen des Feld-Falls: whole-program Feld-Provenance, die Labels trägt
  (Erweiterung der closed-world member-provenance) — ein eigenes, größeres Stück.

## QEMU-Scan: MMIO-Dispatch-Vertrag gegen False Positives (2026-07-15)

Ein `--bugs`-Scan von QEMU (3120 `.ll`, aus C gebaut) meldete ~600 Funde, fast alle **False
Positives**. Beweis der Ursache: `sunhme_mif_read` isoliert = UNKNOWN (sound), als
`--auto-entries`-Entry = FAIL. `--auto-entries` behandelt jeden der ~12800 Ops-Handler als
Entry mit *freien* `addr`/`size` — der Executor refutiert dann `x/size` (size 0), `x<<size*8`
(size riesig), `regs[addr>>2]` (addr riesig), die QEMUs Dispatch nie erzeugt.

- [x] **Fix 1 (sound, kein Flag): MMIO-Dispatch-Vertrag modellieren.** Frontend erkennt
  `.read`/`.write` (Feld 0/8 eines `MemoryRegionOps`, das an `memory_region_init_io(…, size)`
  übergeben wird → `Module::mmio_handlers` mit Region-Größe). Executor seedet `1 ≤ size ≤ 8` und
  (bei bekannter Größe) `addr ≤ region_size ∧ addr+size ≤ region_size` auf den Params. **Präzision,
  keine Annahme** — nur eine Funktion, die real als `ops` übergeben wird, wird constrained (kein
  false PASS). Ein echter `region_size > Array`-Overrun (die VM-Escape-Signatur) refutiert weiter.
  **Wirkung: FAIL 581→480 (101 FPs sound entfernt), PASS +50.** Kein Fix 2 (kein UNKNOWN-Downgrade).
- [x] **Dispatch-Helper-Propagation (2026-07-15).** `synthesize_scalars` + `ScalarFacts::push_module`
  überschreiben das Call-Site-Intervall des `size`-Arguments eines Handlers auf [1,8], sodass der
  Bound an interne Helfer fließt (`reg_read(regs,addr,size)`). Sound (nur interne, callsite-komplette
  Callees). Verifiziert per Test.
- [x] **`_with_attrs`-Handler (2026-07-15).** `MmioHandler{region_size, size_param}`; Felder 16/24 →
  size_param=3 (nach dem `data`-Pointer). Seeding nutzt `size_param`.
- [x] **Cross-file + Whole-Program (2026-07-15).** `mmio_handlers` ist namensbasiert (überlebt Merge);
  `register_init_block{8,32,64}` als Registrierungsfunktion erkannt (ops@5, size@7);
  `WholeProgramFacts` unioniert Handler datei-übergreifend und emittiert `size∈[1,8]` als
  name-basierte Scalar-Precondition. **Verifiziert:** `register_read_memory`s `size`-Param ist jetzt
  cross-file auf [1,8] beschränkt (Zeuge wechselte von `size=0xE0000003` auf `size=3`).

### Verbleibende Div/Shift-FPs — ZWEI neue Klassen (nicht MMIO-Param)
Der QEMU-FAIL-Count blieb bei 480, weil die restlichen ~100 Div/Shift-FPs **nicht** an einem
Dispatch-Param hängen, sondern an:
- [x] **Struct-Feld-Invarianten (2026-07-15) — Fundament + Flag gebaut.**
  - **min/max-Modeling (sound, kein Flag, `556bd85`):** `llvm.umin/umax/smin/smax` werden als
    echtes `select(a<cmp>b, a, b)` gelowered statt als opakes frisches Skalar. `umin(y,4) ≤ 4`
    ist jetzt beweisbar; der Wert trägt seine Operanden-Symbole.
  - **`--assume-field-invariants` (Flag, `8f9acca`):** ein aus dem Speicher geladener Skalar
    (distinktes `fld…`-Symbol) gilt als gültig für seine Nutzung (Shift < Bitbreite, Divisor ≠ 0).
    Erkannt per Expr-Walk am Check (robust, weil das Symbol durch umins `ite`/shl/sub/zext fließt).
    Prove-only, als Annahme `field-invariants` ausgewiesen. Skalar-Analogon zu `--assume-valid-params`.
  - **Wirkung (Voll-Scan): +240 Funktionen UNKNOWN→PASS** (26.109→26.349), Orakel SOUND, Default inert.
- [x] **GELÖST (2026-07-15): war ein Shift-Breiten-BUG, keine Feld-Invariante (`62f3016`).** Die
  gezielte Diagnose ergab: der refutierende Shift ist `lshr i64 -1, zext(i32 (64 - size*8))`, und der
  `NoShiftOverflow`-Check nutzte `ctx.width(amt)` = die **Quell**-Breite des zext-Operanden (32,
  weil der Executor-zext ein werterhaltender No-Op ist) statt der **Ergebnis**-Breite (64). So wurde
  `64 - size*8 ∈ [32,56]` als „Shift ≥ Bitbreite (32)" geflaggt — Zeuge `size=3` → amt=40 ≥ 32 (falsch)
  aber < 64 (korrekt). Ein sauberer False Positive auf JEDEM register-array-Handler + ähnlichem
  `i64`-Shift-durch-`zext(i32)`-Code. Fix: Check nutzt jetzt die Ergebnis-Typ-Breite (`ty`) und weitet
  den Betrag darauf. **Sound, kein Flag.**
  - Nebenbei: `name_mmio` im Whole-Program-Kontext, damit der MMIO-Dispatch-Bound einen *exportierten*
    (Auto-Entry) cross-file-Handler erreicht (unbedingt geseedet, echter Invariant — nicht die
    non-exported-gated `scalar_pre`).
  - **Wirkung (Voll-Scan scan9→scan10): FAIL 480→468 (−12 FPs), Shift/Div-Funde 103→83 (−20),
    register_read_memory nicht mehr FOUND.** Orakel SOUND.
- [ ] **TCG-CPU-Emulations-Helfer.** `helper_palignr_{xmm,ymm,mmx}`, `softfloat_addMagsF32`,
  `helper_insertq_i` — Shift/Div über Gast-Instruktions-Operanden (SSE-Shuffle-Amount, Float-Exponent).
  Gast-kontrolliert via CPU-Emulation, QEMU maskiert sie; braucht ein TCG-Helfer-Operand-Modell,
  komplett getrennt von MMIO.

### Triage-Ergebnis (kein reportbarer VM-Escape)
274 Funde in `hw/` (Device-Emulation), Rest in `block/`/`util/`/`ui/`/Tests. Stichproben (lsi_ram,
sunhme, xlnx_dp, register_read_memory, cd_read_sector_cb): **alle FP** — Region-Größe = Array (Dispatch
beschränkt addr) bzw. unmodellierte Struct-Feld-Invarianten. 16 Atomicity-Funde: alle in Test-Code
(handgeschriebene Test-Mutexe). Free-Funde (`OPLCreate`, `vduse_dev_init`): nicht gast-erreichbar.
**Bewusst nichts an QEMU gemeldet** (spekulative CVE-Meldungen = Mass-Reporting-Antipattern).

## Einheitliches Typ-Sizing für JEDEN opaken Zeiger (2026-07-14) — Abschluss

Ein Prinzip, überall angewandt (`Explorer::size_hinted_pointer`, unter `--assume-valid-params`):
**ein Zeiger, den seine Nutzung typt (`gep %struct.T, ptr %r` → `Module::reg_ptr_hints`),
designiert ein valides Objekt dieser Größe** → sizierte `assumed`-Region statt opakem Zeiger.
Angewandt an *allen* Definitionsstellen: **Load** (Feld-Zeiger), **Assign/inttoptr** (`current`
per-cpu, `container_of`), **Call-Ergebnis** (unsummierter Callee) und **uncontracted Parameter**.

| Metrik (50-Datei-Kernel-Sample) | Start | Ende |
|---|---|---|
| **Funktionen PASS** | 213 | **248 (+35, +16 %)** |
| Funktionen FAIL (echte Funde) | 10 | **14 (+4)** |
| opaque call result | 10426 | **0** |
| int-to-pointer cast | 4923 | **980 (−80 %)** |
| in-bounds | 2822 | **1092 (−61 %)** |
| alignment | 2561 | ~860 (−66 %) |
| loop-havocked pointer | 5823 | **0** (Flag) |

**Soundness:** 792 Tests, Clippy 0, Miri- + C-Orakel SOUND; die C-Corpus-FAILs unter dem Flag sind
**echte** Bugs (`f_double_free`, `f_user_copy_oob`), kein false FAIL. Default-Pfad unverändert.

**Verbleibender Rest (keine Typquelle mehr — ehrliche Grenze):**
- [ ] **loaded value (4348)** — geladene Zeiger, die *nirgends* getypt sind (nie als typisierte-gep-
  Basis benutzt, kein DWARF-Feld). Ohne Typ keine Größe; ein unsized Region würde nur null/UAF
  entscheiden, nicht bounds → würde Funktionen kaum un-gaten.
- [x] **reached-but-not-decided (4162)** — **ERLEDIGT (2026-07-14), aber die Diagnose oben war
  falsch.** Es lag *nicht* an Loop-/Merge-Präzision: Die Klasse war fast vollständig die Property
  `no_dangling_deref`. Der Verifier enumeriert sie an *jedem* `Return(Some(_))` (discharge.rs:176),
  aber `check_return` (`exec/loadrec.rs`) hat sie **nur bei Verletzung** aufgezeichnet — ein
  *sicherer* Return erzeugte also gar keine Entscheidung, fiel auf UNKNOWN und hat über das
  worst-obligation-Gating die **ganze Funktion** auf UNKNOWN gezogen. Fix: `check_return` recordet
  jetzt immer (Skalar kann nicht dangeln; ein Zeiger, der beweisbar nicht in den eigenen
  Frame-Stack zeigt, ist ein *Beweis*, kein Schweigen). Sound, Default-Pfad.
  **Wirkung (50-Datei-Sample): PASS 248 → 748, FAIL 14 (unverändert, keine neuen false FAILs),
  UNKNOWN 1412 → 912; Decided-Rate 16 % → 45 %.** Miri- + C-Orakel weiter SOUND.
  *Lektion:* eine „unentschieden"-Restklasse kann ein fehlendes **Record** sein, nicht fehlende
  Präzision — erst die Property der Residuen ansehen, bevor man die Engine ausbaut.
- [ ] **uncontracted param (1734)** — Params ohne DWARF-Pointee *und* ohne typisierte gep-Nutzung.

## Generalisiertes Typ-Sizing für geladene Zeiger (2026-07-14) — teils

- [x] **Sizing für geladene Zeiger (unter `--assume-valid-params`)** — die `reg_ptr_hints`-Map
  (Register→Pointee-Größe, aus dem indizierenden gep ODER dem DWARF-Local-Typ) wird jetzt **nicht
  mehr nur am Loop-Header** konsumiert, sondern auch im **Load-Handler**: ein geladener Zeiger mit
  bekanntem Typ bekommt eine sizierte `assumed`-Region → bounds/null/alignment/liveness durch ihn
  entscheidbar. Verifiziert: `deep(o){ p=o->in; return p->v; }` → **PASS** (war UNKNOWN); Default-
  Pfad unberührt (Miri+C SOUND, 792 Tests, Clippy 0).
- [ ] **Kein Effekt auf den -O2-Kernel — ehrlich.** Grund gemessen: die Kernel-`.ll` (`make LLVM=1`,
  -O2) haben **0 `#dbg_value`-Records**, also feuert die DWARF-Local-Quelle dort nie; die
  typisierte-gep-Quelle ist für die *typed-gep-Basen* bereits vom RefWitness-Pfad abgedeckt (mein
  Change feuert dort, ist aber redundant). Der Gewinn liegt bei **`-g`/-O1-Code** (dbg_value
  vorhanden, Struct-gep zu Byte-gep kanonisiert → nur DWARF-Local rettet den Typ). Der loop-ptr-
  Bounds-Fall (gleiche Infrastruktur) hat dagegen gezogen (Residual 5823→0).
- [x] **lever 1b — `%struct.T`-Name → DWARF-Composite-id (UMGESETZT).** Die beiden Blocker gelöst:
  (a) `DebugInfo` indiziert `DICompositeType`-Namen (`by_name`, `composite_by_llvm_name`);
  (b) der gep-Parser erfasst den Struct-Namen aus dem *unaufgelösten* Typ (`ltype_raw` +
  `struct_name` an `GepChain`). `dwarf_field_loads` seedet `struct_of[base]` aus dem gep-Namen →
  Feld-Pointees laden jetzt durch **jede** typisierte Basis (Feld-Load / Call-Result / Global,
  nicht nur param-verwurzelt). **Wirkung:** in-bounds −65% (2822→986), alignment −67% (2561→857).
- [x] **Kernel-Idiome (#3, unter `--assume-valid-params`) — UMGESETZT.** Elegante Wiederverwendung:
  `current` (`inttoptr` vom per-cpu-Base) und `container_of` sind beide **typed-gep-Basen**, also
  hat `reg_ptr_hints` sie schon. Die hinted-Sizing (`size_hinted_pointer`) wurde von „nur Loads"
  auf **Assign/inttoptr** ausgeweitet → jeder durch seine Nutzung getypte Zeiger bekommt eine
  sizierte Region. **Wirkung:** int-to-pointer −80% (4923→980); **+7 Funktionen auf PASS (217→224)**
  — die Funktions-decided-Rate bewegt sich endlich (kombinierte Hebel un-gaten ganze Funktionen).
  792 Tests, Clippy 0, Miri + C-Orakel SOUND.

## Umsetzung #1–#7 (2026-07-14) — was gebaut wurde, was flag-gated ist, was offen bleibt

**Sound & Default (kein Flag):**
- [x] **#1 (Teil): `RetSummary::Alloc`** — ein Allocator-Wrapper (`foo_alloc(){ return kmalloc(N); }`)
  summiert jetzt als *frische, sizierte Heap-Region* statt `Unknown`. Am Call-Site bekommt der
  Caller eine lebende Region → Zugriffe werden geprüft statt opak. Fixt zugleich einen **latenten
  Bug**: `ret_of_fn` behandelte *jeden* `Inst::Alloc` (auch Heap!) als `LocalStack` → ein
  malloc-Wrapper wäre fälschlich als DanglingStack-Rückgabe markiert worden. Jetzt nach
  `RegionKind` gesplittet. Verifiziert: `use_oob(i){ p=wrap(); return p[i]; }` → **FAIL** (war
  UNKNOWN); geguardete Variante refutiert nicht.
- [x] **#4 null/opaque** — stabiles Adress-Symbol pro opakem Zeiger (`ptr#<id>`) + Null-Guard-Beweis;
  `if(p!=null)` trägt jetzt zum Deref. **−24 % null-Residual.**

**Flag-gated (unsound in general, im README dokumentiert):**
- [x] **`--assume-valid-returns`** (#1 Rest) — der interprozedurale Zwilling von
  `--assume-valid-params`: ein Zeiger aus einem *unsummierten* Call (externer Callee) gilt als
  valide + non-null. Beweist `no_null_deref` + `no_use_after_free` durch das Call-Ergebnis;
  **Bounds bleiben UNKNOWN** (für einen externen Callee ist nirgends eine Größe bekannt).
  Unsound in general (Call kann NULL / `ERR_PTR` / dangling liefern) → Assumption `valid-returns`.
  **Bewusst KEIN Scan-Default** — es würde genau die Null/UAF-Bugs verstecken, die ein
  Bug-Finding-Scan sucht.

- [x] **`--assume-valid-loop-ptrs`** (#2) — ein *loop-getragener* Zeiger (bewegter Iterator,
  `iter = iter->next`) wird am Loop-Header statt als opak als **valide lebende Region** (unbekannte
  Größe) materialisiert. Beweist `no_use_after_free` + `no_null_deref` durch den Iterator;
  **Bounds bleiben UNKNOWN** (das Objekt eines bewegten Zeigers hat keine statisch bekannte Größe).
  Unsound in general (Cursor kann aus dem Objekt laufen; ein Listenknoten kann bereits freed sein)
  → Assumption `valid-loop-ptrs`. **Kein Scan-Default.** Verifiziert an einer `list_for_each`-
  Traversierung: ohne Flag alles UNKNOWN, mit Flag null+UAF PASS.

- [x] **#2 Bounds (unter `--assume-valid-loop-ptrs`)** — der loop-getragene Zeiger bekommt jetzt
  die **Größe** seines Objekts, aus zwei Quellen: (a) dem typisierten gep, der ihn indexiert
  (`gep %struct.T, ptr %it`), und (b) — wo clang das zu einem Byte-gep kanonisiert hat (`-O1`/`-O2`) —
  aus der **DWARF-Local-Typ**-Kette (`#dbg_value(<local>, !V)` → `!DILocalVariable(type:)` →
  Pointee-Größe). Neu: Parser erfasst `#dbg_value`-Records, `DebugInfo::local_pointee_bytes`,
  `Module::reg_ptr_hints` bis zum Loop-Havoc durchgereicht. Alignment aus der Größe abgeleitet.
  **Ergebnis:** eine `list_for_each`-Traversierung verifiziert **vollständig PASS**; auf dem
  50-Datei-Kernel-Sample fällt das `loop-havocked pointer`-Residual **5823 → 0**, +4 PASS.
  792 Tests, Clippy 0, Miri + C-Orakel SOUND.

**Offen (bewusste Grenze):**
- [ ] Bounds nur soweit ein Typ bekannt ist (typed-gep ODER DWARF-Local). Ein völlig
  typloser bewegter Zeiger bleibt unsized (Liveness/Null trotzdem bewiesen).
- [ ] **#3 int-to-pointer** — `current`/per-cpu/`container_of` als Kernel-Idiom-Contracts hinter
  einem Flag. Roadmap-Phase 2. (Beliebigen Int als Zeiger anzunehmen bleibt ohne Idiom unsound.)
- [ ] **#5 loaded value / #6 reached-but-not-decided / #7 uncontracted param** — Restmengen nach
  den bereits gebauten Recoveries; inkrementell bzw. brauchen DWARF-Rückgabetyp-Import.
- [ ] **Bounds für `--assume-valid-returns`** — bräuchte den DWARF-Pointee des Callee-Rückgabetyps.

**Messung (sortiertes 50-Datei-Kernel-Sample):** Verdikte unverändert (213 PASS / 10 FAIL / 1451
UNKNOWN) — die *Obligations*-Ebene gewinnt (null −24 %), die *Funktions*-Ebene nicht, weil eine
Funktion durch ihre **schlechteste** Obligation gedeckelt ist und `RetSummary::Alloc` nur echte
Allocator-Wrapper trifft (im Kernel eine Minderheit). **Soundness:** 792 Tests, Clippy 0,
Miri + C-`--bugs`-Orakel SOUND.

## ROADMAP: Decided-Rate ≥ 95 % → `docs/decided-rate-roadmap.md`

Phasenplan (0 Fundament reiche Ret-Provenance-Summaries → 1 Return-Provenance #1 → 2 Kernel-Idiome
#3 → 3 Container/Loop #2 → 4 Guards #4 → 5 Long Tail). Trajektorie ~15 % → 40–55 → 60–72 → 72–82 →
80–88 → 85–93 %; die letzten Prozente auf 95 % stoßen an eine Soundness-Decke (ein Rest bleibt
korrekt „known-unknown"). Jede Phase einzeln sound + gegen Orakel/`mm`-Scan validiert.

## AKTUELLER STATUS: ELF- vs. LLVM-Pfad (Stand 2026-07-14)

Gemessen mit Scan-Defaults (`--bugs --assume-valid-params --closed-world`), ohne harte Timeouts.

### LLVM-Pfad (reif) — UNKNOWN-Ursachen #1–#7 bearbeitet (2026-07-14)

Jede der 7 dominanten UNKNOWN-Ursachen einzeln auf sound Machbarkeit geprüft. Ergebnis: **#4
umgesetzt** (sound), der Rest ist bereits adressiert oder eine bewusste Soundness-Grenze (ein
erzwungener „Fix" würde false PASS/FAIL erzeugen — soundness-first).

- [x] **#4 null/opaque provenance (~4300) — UMGESETZT & sound.** Ursache war: `scalarize` gab für
  einen opaken Zeiger ein *frisches* Symbol → ein `if(p!=null)`-Guard und der spätere Deref
  nutzten verschiedene Symbole, der Guard griff nicht. Fix: **stabiles Adress-Symbol pro opaker
  Zeiger-id** (`ptr#<id>`) + Null-Guard-Beweis in `check_access` (prove `ptr#id != 0` aus der
  Pfadbedingung). Prove-only (ungeguardeter Deref bleibt UNKNOWN → kein false FAIL). **−24 %
  null-Residual** (6743→5152, sortiertes 50-Sample), Verdikte identisch (Obligations-Gewinn, kein
  Funktions-Decided-Sprung — worst-obligation gated). 792 Tests, Miri+C-Orakel SOUND. Der Zig-
  `?*T`-Optional-Deref (echter Guard) beweist jetzt korrekt NoNullDeref (Test aktualisiert).
- [ ] **#1 opaque call result (~6300) — zurückgestellt.** Im echten Scan durch `--whole-program`/
  `--reachable`-Summaries großteils aufgelöst; Kernel-IR trägt **keine** `dereferenceable/nonnull`-
  Return-Attribute (geprüft: 0 Treffer), ein Return-Attribut-Import hätte also null Kernel-Wert.
  Rest = genuine externe/unsummierte Calls (inhärent opak).
- [ ] **#2 loop-havocked pointer (~5800) — zurückgestellt (sound-Grenze).** Der `modified`-Set ist
  **präzise** (loop-invariante Zeiger behalten schon ihre Provenance); der Rest sind *echt* im Loop
  modifizierte Zeiger (Listen-/Baum-Traversal `iter=iter->next`), die keinen statischen Bound haben.
  Der Array-Stride-Fall (`iter+=k; iter!=end`) ist bereits per Pointer-Walk-Induktion abgedeckt.
- [ ] **#3 int-to-pointer cast (~5800) — zurückgestellt (bewusste Grenze).** Einen beliebigen Int
  als gültigen Zeiger anzunehmen wäre unsound (false PASS). `current` per per-cpu-asm bleibt opak.
- [ ] **#5 loaded value (~2200) — zurückgestellt.** Bereits von ~20500 gesenkt (transitive/typed-
  gep/offset-0-Recovery, [[loaded-pointer-provenance]]); der Rest braucht tiefere Provenance.
- [ ] **#6 reached-but-not-decided (~1300) — zurückgestellt (inkrementell).** Loop-Body großteils
  per Induktion gelöst; „unsupported op" = einzelne Frontend/Decoder-Lücken, wachsen monoton.
- [ ] **#7 uncontracted pointer parameter (~970) — zurückgestellt (sound-Grenze).**
  `--assume-valid-params` deckt das Gros; der Rest hat keine DWARF-Pointee-Größe (ein `nonnull`
  ohne Größe beweist nur NoNullDeref, keine Bounds/Liveness).

### ELF-/Binär-Pfad (geringere Präzision, jetzt Contracts + fs/gs)
C-Corpus als saubere ELF-Testmenge:
- **`-O1` (sound Baseline):** 4 PASS / 12 UNKNOWN, 0 false FAIL. UNKNOWN dominiert von
  **`scalar-as-pointer`** (flacher Byte-Speicher, keine Typen — ein Zeiger ist ein Skalar).
  Verbleibende Decoder-Reste: 1 `unsupported opcode` (nicht 0x64) + `dangling branch target`.
- **`-O0`:** **5 false FAIL** — der **vorbestehende Frame-/Spill-Provenance-Bug** (siehe Punkt 3),
  nicht durch die neuen Contracts verursacht (Baseline reproduziert ihn).
- Neu & sound: Heap-Contracts (Punkt 1) + fs/gs-Präfixe (Punkt 2), siehe Batch unten.

Recall-Hierarchie bleibt **ISO ⊆ ELF ⊆ LLVM**; ELF=LLVM nur für `-g`-Binaries erreichbar,
stripped bleibt inhärent schwächer (keine Typen). Siehe [[binary-path-parity]].

## OFFEN — Punkt 3: Binär-Register-/Frame-Provenance (PRIORITÄT für Binär-Pfad)

- [ ] **Frame-Modell-false-FAIL (vorbestehender -O0-Soundness-Bug) — zuerst fixen.** Ein
  legitimer `[rbp-k]`-Zugriff im eigenen Frame refutiert bei `-O0` fälschlich `in_bounds`
  (`dfree` hat gar keinen Array-Zugriff, FAILt aber). Ursache: `mov rbp,rsp` erfasst rsp **vor**
  dem `sub rsp,N`, das die Frame-Region baut, + Call-Havoc-Interaktion. Echter Soundness-Bug.
- [ ] **Spill-Round-Trip-Provenance.** Ein zu einem Stack-Slot gespillter und neu geladener
  Zeiger verliert/verwechselt seine Provenance (loaded value vs. Stack-Frame).
- [ ] **Danach Punkt 3 i. e. S.: DWARF-Feld-Pointee auf Binär-Load-Adressen** (flaches Analogon
  zu [[loaded-pointer-provenance]]) — baut auf den beiden obigen Fixes auf. Erst dann wird der
  Nutzen der Heap-Contracts (Punkt 1) sichtbar (UAF/OOB/double-free am Binär refutierbar).

  Reihenfolge bewusst so: ein halber Provenance-Fix birgt false-PASS-Risiko (soundness-first),
  daher nicht spekulativ implementiert. Siehe [[binary-path-parity]].

## Externe Validierung & Vollscan-Ergonomie (2026-07-14 Batch)

- [x] **memsafety-Benchmarks laufen gelassen** (die vorhandenen Differential-Orakel als
  Benchmark-Suite): Rust↔Miri = **SOUND** (0 false PASS; 20 präzise PASS, 12 UB gefangen/UNKNOWN);
  C↔ASan/UBSan strikt = **SOUND** (0/0, 2 Bugs), `--bugs` = **SOUND** (0/0, **8/8 Bugs**).
- [x] **Differential-Harness-Scoping gefixt** (`differential/c/run.sh`): ein reiner
  `no_arith_overflow`-FAIL (arithmetische UB, die das memory-safety-Orakel bewusst ausschließt)
  wurde im `--bugs`-Lauf fälschlich als „false FAIL" gezählt → `f_signed_ovf` erschien als
  Scheinregression. Neu: `fail_is_arith_only` klassifiziert einen ausschließlich-arithmetischen
  FAIL als „out of scope" statt False Positive. Stellt die dokumentierte 0-FP-Eigenschaft wieder
  her (CSolver selbst war korrekt — es fand einen *echten* signed overflow).
- [x] **`scan` = kompletter Kernel-Scan per Default** (`crates/cli/src/main.rs`): die Vollscan-
  Features (`--bugs --assume-valid-params --closed-world --cross-file --whole-program
  --auto-entries --aliasing-model`) sind für `scan` jetzt **opt-out** — ein blankes
  `solver scan <dir>` fährt die maximale Recall-Konfiguration und streamt jeden Bug live
  (`[FOUND #n]`). Jede Einzel-Deaktivierung per **Anti-Flag** `--no-<name>`. `verify` bleibt der
  strikte, opt-in, soundness-first Pfad (unverändert). Helper `flag(args, name, default)`.
- [x] **Kernel-Scan-Skript mit Live-Feed** (`scaling/kernel/full-scan.sh`): baut das Release-
  Binary, zeigt auf `Kerneltests/linux` (37.597 `.ll`) per Default, streamt Bugs live und tee't
  ein Log. Nimmt ein alternatives Verzeichnis + durchgereichte Anti-Flags. End-to-end getestet
  (ipc-Subset: 108 Handler via auto-entries, Whole-Program-2-Pass, 6 DataRace live gestreamt).

## Decided-Rate (Punkt 3) — Zeiger-Provenance aus geladenen Feldern (2026-07-14)

Diagnose (ohne harte Timeouts, `solver scan`/verify-zu-Ende): die dominante UNKNOWN-Ursache
im Kernel ist **nicht** das Frontend-Droppen (0 dropped), sondern nicht-getrackte Zeiger-
Provenance. Mit Scan-Defaults (`--assume-valid-params`) killt das die „uncontracted param"-
Klasse (25643→1249); danach dominiert **„loaded value (no store-load provenance)"** — ein aus
dem Speicher geladener Zeiger (`p->a->b`, `current->cred->…`), dessen Provenance verloren geht.

- [x] **Transitive DWARF-Member-Provenance** (`member_pointee` + Seeding in `dwarf_field_loads`):
  ein geladenes Zeiger-Feld, das auf einen Struct zeigt, seedet `struct_of[dst]` → die nächste
  Feld-Ebene löst auch auf (`a->b->c`). Vorher nur eine Ebene tief.
- [x] **Offset-0-Feld-Loads** (`dwarf_field_loads`): clang emittiert für das *erste* Feld ein
  blankes `load ptr, ptr %base` ohne gep — vorher komplett verpasst, jetzt als Feld-Load bei
  Offset 0 erkannt (nur für Pointer-Loads, kein Scalar-Fehlgriff).
- [x] **Typ-gerichtete gep-Recovery** (`typed_gep_field_loads`, DWARF-frei): ein
  `gep %struct.T, ptr %b` beweist, dass `%b` auf `%struct.T` (bekannte LLVM-Größe) zeigt — das
  erreicht den **dominanten realen Fall**, wo der Basiszeiger *nicht* aus einem Parameter stammt
  (Feld-Load off `current`, Container/Listen-Walk, Global). Als `assumed`-Feld: nur unter
  `--assume-valid-params`, als `param-valid` ausgewiesen; ohne Opt-in **kein** Verhaltenswechsel
  (strikter `verify`-Pfad unverändert — Miri-Orakel identisch). `assumed`-Region unterdrückt
  Konstant-Offset-Refutation → kein false FAIL.

**Wirkung** (25-Datei-Sample, 479 Funktionen, beide Binaries zu Ende gelaufen, kein harter
Timeout): loaded-value-Residuals **2945→680 (−77%)**; Verdikte 69/5/405 → **71 PASS / 6 FAIL /
402 UNKNOWN** (+2 PASS, +1 neu gefundener Bug). Decided-*Rate* steigt moderat (Funktion ist erst
decided, wenn *alle* Obligationen es sind — verbleibende Klassen: opaque-call-result, loop-havock).
Sound: Miri strict = 0 false PASS (unverändert), C `--bugs` = 0/0, 8/8 Bugs; 792 Tests grün.
Verbleibender Haupthebel: **opaque call result** (interprozedural — durch `--whole-program`/
`--reachable` im echten Scan teils aufgelöst) und **loop-havocked pointer**.

### Experiment: Scan ganz ohne Zeitlimit (2026-07-14)

`scan` hat jetzt **kein per-Funktion-Wall-Clock-Limit mehr als Default** (`time_budget = None`;
`--time-limit <sek>` als optionaler Cap). Begründung: ein Wall-Clock-Cap ist genau der harte
Timeout, der eine langsam-aber-beweisbare Funktion zu UNKNOWN verwirft; Terminierung ist ohnehin
per Konstruktion beschränkt (Merge-Exploration besucht jeden Block einmal + SAT-Decision/CNF-Budget).

**Messung (mm-Subtree, 4907 Funktionen, das zeigerlastigste Subsystem):**
- mit 30s-Limit:  665 decided (13,6%), 35 Bugs, 453s Wall, **0 Deferrals**.
- ohne Limit:     665 decided (13,6%), 35 Bugs, 457s Wall, **0 Deferrals**.

**Byte-identische Verdikte, gleiche Bugs, gleiche Wall-Zeit.** Bestätigt empirisch, was der
`ExecLimits`-Doc behauptet: das Zeitbudget greift auf realem Kernel-Code **nie**. Keine Funktion
läuft pathologisch lang, keine entscheidet mit mehr Zeit zusätzlich. **Konsequenz für Punkt 3:**
die 86% UNKNOWN sind *präzisions*-limitiert (unbekannte Provenance, opake Calls), **nicht**
zeit-limitiert — mehr Rechenzeit hebt die decided-Rate nicht, nur besseres Modellieren.

### Experiment: ISO-/Binär-Scan vs. LLVM-Scan des gleichen Codes (2026-07-14)

Gleicher C-Code (`differential/c/corpus.c`) in drei Repräsentationen, alle mit
`--bugs --assume-valid-params`:
- **LLVM-IR**: **6 Bugs (FAIL)** gefunden (f_heap_oob, f_use_after_free, f_unchecked_get,
  f_negative_index, f_user_copy_oob, f_asm_then_oob), 10 UNKNOWN.
- **ELF-Objekt**: **0 Bugs**, 4 PASS, 12 UNKNOWN.
- **ISO** (mit dem ELF-Objekt, via `xorriso`): identisch zum ELF (der ISO-Pfad entpackt nur +
  `lower_elf`) — Verdikt Unknown, **0 Bugs**.

**Ergebnis: ja, der ISO-/Binär-Scan findet strikt weniger** (0 vs. 6). Zwei Ursachen, beide dem
Binär-Pfad inhärent: (1) Decoder-Lücke — 4 Funktionen ganz gedroppt an `x86 opcode 0x64` (das
`%fs:`/`%gs:`-Segment-Präfix für TLS/Stack-Canary, in Kompilat allgegenwärtig); (2) dominanter
Präzisionsverlust — flacher Byte-Speicher ohne Typen/Allokationsmodell, ein Zeiger ist nur ein
Skalar (Residuals „scalar-as-pointer"), also fehlt die Pointee-Größe/Heap-Allokation, die der
LLVM-Pfad aus Typen + DWARF + Allocator-Contracts hat → OOB/UAF nicht refutierbar. Bestätigt die
dokumentierte Präzisionshierarchie (STATUS.md): Recall ISO ⊆ ELF ⊆ LLVM.

### Roadmap: was nötig wäre für ISO = ELF = LLVM (Recall-Parität) (2026-07-14)

`ISO = ELF` ist für ein gegebenes Objekt **bereits erfüllt** — der ISO-Pfad entpackt nur +
`lower_elf` (inkl. DWARF-`parameter_pointee_sizes`), identisches Verdikt. Die ISO-spezifische
Restarbeit ist reine Container-Abdeckung (welche Objekte extrahiert werden: LZMS/PDB), nicht
Präzision. Die ganze Lücke ist **ELF → LLVM**. Priorisiert nach Wert × Machbarkeit:

1. **Allocator/Dealloc/User-Copy-Contracts auf Binär-Calls** (größter Hebel, gut machbar).
   `crates/asm` hat **keinen** Contract-Lookup: jeder `call` → `opaque_call()` (havoct nur Heap).
   Der LLVM-Pfad matcht `malloc/kmalloc/free/copy_from_user/…` gegen `crates/contracts` und baut
   sizierte Heap-/Freed-/User-Tainted-Regionen — genau das fehlt binär. Der Callee-Name ist im
   Binär da (Reloc des `call rel32` / PLT), wird aber verworfen. Nötig: (a) Call-Ziel-Symbol per
   `resolve` (existiert schon für Globals) auflösen, (b) SysV/Win64-ABI Arg-Register→Contract-Param
   (rdi/rsi/… — der Decoder modelliert rdi..r9 bereits als Params), (c) statt `opaque_call` ein
   `Alloc`/`Dealloc`/`MemIntrinsic` emittieren. Reused die gesamte Contract+Allokations-Maschinerie.
   Holt f_heap_oob, f_use_after_free, f_user_copy_oob (3 der 6 Corpus-Bugs).
2. **Decoder-Segment-Präfixe (0x64/0x65 = fs/gs)** + Opcode-Abdeckung (inkrementell, begrenzt).
   Das fs/gs-Präfix droppt ganze Funktionen (TLS/Stack-Canary). Als opaken Skalar-Read modellieren
   (der Wert treibt keine Memory-Safety) → Funktion bleibt analysierbar statt gedroppt.
3. **Feld-Load-Provenance im flachen Speicher** (tief, nur teils schließbar). `p->a->b` ist binär
   `mov rax,[rdi]; mov rbx,[rax+8]` ohne Typ. Das binäre Analogon zur `typed_gep`-Recovery bräuchte
   DWARF-Struct-Member-Info auf die Load-Adresse gemappt + Typ-Propagation durch Register (viel
   schwerer als durch SSA). Nur für `-g`-Binaries; teils schließbar.
4. **Inhärente Grenze (stripped Binaries):** ohne DWARF gibt es **keine** Typen — nur strukturelle
   Fakten (Stack-Frames aus Prologen, Globals aus Relocations). Heap-/Param-Pointee-Größen sind
   unrekonstruierbar. `ELF = LLVM` ist nur für `-g`-Binaries erreichbar; stripped bleibt echt
   schwächer (siehe [[verify-without-pointers]]). Der Binär-Pfad ist immer sound, nie false PASS —
   er sieht nur weniger.

## Binär→LLVM-Parität (ISO=ELF=LLVM) — Umsetzung Punkt 1–3 (2026-07-14)

- [x] **Punkt 1 — Allocator/Dealloc/User-Copy-Contracts auf Binär-Calls.** Der x86-Decoder löst
  jetzt das Ziel eines `call rel32` per Reloc auf (`CallResolver`) und emittiert einen **benannten**
  Call mit den SysV-Arg-Registern als Argumenten (`named_call`); ein Post-Pass in `lower_elf`
  (`apply_binary_call_contracts`) matcht den Namen gegen `crates/contracts` und ersetzt ihn durch
  `Alloc`/`Dealloc`/`MemIntrinsic` — dieselbe Maschinerie wie der LLVM-Pfad. **Sound & validiert**
  (792 Tests, Miri+C-Orakel SOUND, kein Regress ggü. Baseline). Nachweislich wirksam: ein
  Fill-Loop-Store *beweist* jetzt in-bounds gegen die Malloc-Region (vorher opak/UNKNOWN).
  Zusätzlich `ExecLimits.flat_memory`: Binär-Heap-Regionen sind **prove-only für Bounds** (der
  flache Registermodell-Pfad kann einen Heap-Index-Guard nicht zuverlässig rekonstruieren →
  Bounds-Refutation würde false FAIL riskieren), temporal (UAF/double-free) bleibt refutierbar.
- [x] **Punkt 2 — fs/gs-Segment-Präfixe (0x64/0x65).** Statt die Funktion zu droppen wird der
  Folge-Befehl dekodiert und sein Segment-Zugriff **neutralisiert** (Load→opaker Wert, Store→
  verworfen) — Segment-Speicher (Canary `%fs:0x28`, per-CPU `%gs:`) ist ein separater Adressraum
  außerhalb des Modells, seine Werte treiben keine Memory-Safety. **Sound & validiert**: 0 statt 4
  Funktionen auf `opcode 0x64` gedroppt; canary-geschützte (`-fstack-protector-all`) Funktionen
  werden analysiert.
- [ ] **Punkt 3 — Feld-Load-Provenance im flachen Speicher: DEEP, dokumentiert statt halb gebaut.**
  Bei der Umsetzung von Punkt 1 aufgedeckt: der Binär-Pfad hat **fundamentalere** Provenance-Lücken
  als Punkt 3 adressiert, die Punkt 1s Nutzen maskieren und einen **vorbestehenden -O0-Soundness-Bug**
  bilden:
  1. **Spill-Round-Trip-Provenance**: ein zu einem Stack-Slot gespillter und neu geladener Zeiger
     verliert/verwechselt seine Provenance (loaded value vs. Stack-Frame).
  2. **Frame-Modell-false-FAIL (vorbestehend, Baseline reproduziert)**: bei `-O0` refutiert ein
     legitimer `[rbp-k]`-Zugriff im eigenen Frame fälschlich `in_bounds` (z. B. `dfree` hat gar
     keinen Array-Zugriff, FAILt aber). Ursache: `mov rbp,rsp` erfasst rsp **vor** dem
     `sub rsp,N`, das die Frame-Region baut, plus Call-Havoc-Interaktion. **Das ist ein echter
     Soundness-Bug im Binär-Pfad bei -O0** und der eigentliche nächste Schritt — wichtiger als
     Punkt 3, und mit ihm die gemeinsame Wurzel (Binär-Register/Frame-Provenance).
  3. **-O1**: Provenance geht über Fill-Loops verloren (Register am Loop-Merge gehavoct).

  Ein halber Provenance-Fix birgt false-PASS-Risiko (Soundness-first), daher **bewusst nicht**
  spekulativ implementiert. Reihenfolge für später: erst (2) Frame-Modell + (1) Spill-Provenance
  sound fixen, dann wird Punkt 1 sichtbar wirksam und Punkt 3 (DWARF-Feld-Pointee auf Load-Adressen)
  baut darauf auf. Siehe [[object-loader-multiformat]], [[verify-without-pointers]].

## → WAS IST JETZT NOCH ZU TUN (Stand 2026-07-14, priorisiert)

Nach den Batches (SMT entfernt, 128-Bit, x86-ALU-mem+LOCK, interproc-Escape, CFI-Slice,
acquire/release, div/rem+Shifts). Alles Übrige ist **sound** (degradiert zu UNKNOWN, nie
false PASS). Geordnet nach *sound machbar × Wert*.

**Tier 1 — sound & begrenzt — ERLEDIGT 2026-07-14:**
- [x] **x86 MSIR restliche Speicheroperand-Formen** (508d324): `cmp/test [mem]`, `inc/dec [mem]`,
  `<op> [mem], imm` (Group-1), `call/jmp [mem]` (Group-5), `xchg [mem]` (atomar = Barrier+RMW),
  `cmovcc [mem]` — Zugriff wird jetzt geprüft statt verworfen.
- [x] **Typed-Decoder ALU-mem** (43378a8): `<alu> [mem], r` dekodiert (Länge + typed Operand).
- [x] **Interproc-Escape: Out-Parameter-Store** (a913ccd): `*out = &x` → `Summary.escapes_stack`
  (nur Entry-Block = unbedingt, kein false FAIL); Call-Site setzt dangling Wert an argK; Caller-
  Deref = UAF. Komplettiert das Escape-Trio (Return, Wrapper, Out-Param). Offen: bedingter Escape
  in einem Nicht-Entry-Block (sound gemisst) und Wrapper-Propagation von `escapes_stack`.

**Tier 2 — braucht ein anderes Modell (Klasse „E", bewusst zurückgestellt):**
- [ ] **TBAA / Strict-Aliasing / Union-Punning** — kein sound Refutations-Slice ohne Typ-Lattice
  (legitime `repr`-Reinterpretation = identische Form). Details unten.
- [ ] **ABA value-aware & Refcount „last reference"** — Lockset-Trace trägt keine Werte/Tags.

**Tier 3 — extern blockiert:**
- [ ] **LZMS** (kein Testkorpus — ISO ist all-LZX) und **PDB** (keine Windows-Buildumgebung).

**Tier 4 — inhärente Grenzen (nicht sound schließbar / bewusst):**
- Exact-Path-Recall-Gate (Bugs hinter Schleifen/Merges/opaken Calls nur in `--bugs` + genuine
  Inputs) — *load-bearing Soundness-Grenze*, siehe `docs/soundness-invariants.md`.
- Float/Vektor bleiben opak (Werte treiben keine Memory-Safety — flaggen wäre falsch).
- Volle x86-SSE/AVX- + AArch64-Decoder-Vollständigkeit (unbeschränkt, großteils irrelevant).
- Bit-Blaster: Breite > 128 und i128-`div/rem` (>300k Klauseln) → sound Linear-Fallback.

**Tier 5 — Infra/Hygiene:**
- [ ] Bus-Faktor 1 — teilweise gemildert (`docs/soundness-invariants.md`); Soundness-Argumente
  weiter nicht maschinengeprüft.
- [ ] MIR-Coroutine-`yield` — niche; aktuell sound abgelehnt (Funktion nicht analysiert).

---

## Coverage-Schließung (Code-Audit) 2026-07-14 — Batch

Aus dem code-basierten „was deckt der Solver nicht ab"-Audit; alle sound geschlossen oder als
bewusste Grenze dokumentiert:

- [x] **SMT-Backend entfernt** (dcd3abf): `crates/smt` gelöscht; der hauseigene CDCL/Bit-Precise-
  + Linear-Solver entscheidet alles. `Justification::SmtUnsat`→`Unsat` umbenannt.
- [x] **Bit-Blaster volle 128-Bit-Domäne** (96b2a27): `MAX_WIDTH` 64→128, `MAX_CLAUSES` 60k→300k.
  i128 add/sub/mul/shift/bitwise/compare jetzt bit-präzise; i128 **div/rem** (>300k Klauseln)
  fällt sound auf linear zurück. Einzige nicht-blastbare Konstruktion: Breite > 128.
- [x] **x86 ALU-Read-Modify-Write auf Speicher + LOCK-Prefix** (7315d70): `add/or/and/sub/xor
  [mem], r` → load-modify-store (Speicherzugriff jetzt geprüft); LOCK → Full-Barrier + atomare
  RMW. (Der *typed* Decoder lehnt ALU-mem weiter ab — separate Tabelle, nur Länge/Differential.)
- [x] **StackIntegrity/ValidStackFrame** — am Enum als **subsumiert-by-design** dokumentiert:
  Overflow→RA = InBounds, Call-in-Daten = ValidIndirectTarget; dedizierte RA/Canary-Property
  bräuchte ein Rücksprungadress-Modell (tief, kein Mehrwert über InBounds).
- [x] **Exact-Path-Gate (Recall-Rand)** — als **load-bearing Soundness-Grenze** dokumentiert
  (calls.rs, docs/soundness-invariants.md): auf inexakten Pfaden zu refutieren erzeugt false
  FAILs; kann nicht generell aufgehoben werden. Bewusster Precision/Recall-Tradeoff, kein Bug.
- Bewusst **nicht** geschlossen (korrekt so): Float/Vektor bleiben opak (Werte treiben keine
  Memory-Safety); volle x86-SSE/AVX- + AArch64-Decoder-Vollständigkeit ist unbeschränkt und
  großteils irrelevant; die „E"-Klassen (TBAA, ABA-value, LZMS/PDB) unverändert zurückgestellt.

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

- [x] ~~`csolver-smt` NullSolver~~ → **Backend ganz entfernt** (dcd3abf): der hauseigene
  CDCL/Bit-Precise-+Linear-Solver entscheidet alles; kein externes SMT mehr.
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
