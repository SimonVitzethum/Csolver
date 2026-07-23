# Roadmap: UNKNOWN unter 3 % (≥ 97 % decided, Kernel)

**Ziel:** den Anteil *entschiedener* Kernel-Funktionen (PASS ∨ FAIL) von aktuell **~30 %**
(SCAN10-Teilstand: 28,7 % PASS / 1,0 % FAIL / **70,3 % UNKNOWN**) auf **≥ 97 %** heben —
UNKNOWN **< 3 %** — ohne je einen false PASS zu erzeugen.

Diese Roadmap ist die Fortsetzung von [`decided-rate-roadmap.md`] (Ziel ≥ 95 %). Sie beschreibt,
was *zusätzlich* nötig ist, um die letzten Prozente bis unter 3 % zu schließen.

---

## Die harte Wahrheit zuerst: zwei Bedeutungen von „decided"

`decided-rate-roadmap.md` misst eine **Soundness-Decke** von grob **3–7 %**: ein Restanteil ist
*genuin unentscheidbar* ohne Soundness-Verlust (angreifer-beeinflusste indirekte Dispatch-Ziele,
daten-abhängiges Aliasing, tiefe Provenance über opake Grenzen). **< 3 % UNKNOWN liegt an oder
unter dieser Decke.** Das Ziel ist daher nur erreichbar, wenn man zwei Größen sauber trennt:

1. **Sound-decided** (strikt): PASS/FAIL ohne jede Annahme. Realistische Decke ~93–95 % decided
   (≈ 5–7 % UNKNOWN). Darunter geht es strikt **nicht**.
2. **Decided-unter-benannten-Annahmen**: PASS/FAIL, das auf einer *ausgewiesenen, opt-in*
   Annahme ruht (Kernel-Invariante, Closed-World-Caller, Container-Vertrag) — im Proof-Tree
   sichtbar, auditierbar, per Flag steuerbar. **Nur so kommt UNKNOWN unter 3 %.**

**Verdikt vorab:** < 3 % UNKNOWN ist erreichbar, aber **nicht als rein-sound-decided** — es
erfordert eine umfassende, benannte Annahmen-Schicht für den unentscheidbaren Kern, plus das
konsequente Schließen aller Modellierungs- und Frontend-Lücken darüber. „Decided" heißt dann
„entschieden modulo explizit ausgewiesener Annahmen" — das ist legitim und nützlich, aber es ist
eine andere (schwächere) Aussage als strikt-sound. Jede Zahl in dieser Roadmap ist an ihr
Annahmen-Bundle gebunden.

---

## Wo der Rest sitzt (Residual-Histogramm, ~89 % Zeiger-Provenance)

| Klasse | ~Residual | Status nach ValidRef-Batch |
|---|---|---|
| loaded value (kein store-load) | 3601 | teilw. (ValidRef interproz. + RefWitness intraproz.); Rest: void*/union/private_data |
| uncontracted pointer parameter | 1990 | offen (Param ohne getypte Nutzung) |
| non-null / opaque provenance | 1887 | *downstream* von Provenance |
| in-object (valid-ptr-arith) | 1289 | *downstream* |
| in-bounds (access in allocation) | 1103 | *downstream* |
| scalar-as-ptr (intrinsic/asm/deep) | 1036 | teilw. (Ptr-Identity-Intrinsics); Rest: asm, tiefe Ketten |
| alignment | 892 | *downstream* |
| int-to-pointer | 851 | teilw. (getypt via size_hinted); Rest: untyped |
| opaque call result | 786 | **geschlossen** (Alloc/ValidRef/valid-returns) |
| null / integer-derived | 594 | *downstream* |
| loop-body / unsupported op | ~1600 | teilw. (Induction + assume-valid-loop-ptrs) |
| arithmetic overflow | 235 | teilw. (interval-facts + width-fix) |
| concurrency-Heuristik | ~368 | schwer (bleibt evtl. UNKNOWN) |

**~89 %** aller Residuen sind Provenance (direkt) oder Provenance-*Folgen* (non-null, in-object,
in-bounds, alignment resolven, sobald die Herkunft bekannt ist). Der Hebel ist eindeutig.

---

## Phase A — Interprozedurale Provenance-Vollständigung (70 % → ~20 % UNKNOWN)

Der mit Abstand größte Sprung. Vier Bausteine, alle mit Multiplikator (Funktion-decided ist durch
die schlechteste Obligation gedeckelt — eine geschlossene Klasse kippt viele Funktionen).

- **A1 — Loaded-Value-Vollständigung.** Jeden geladenen Zeiger typisieren, auch die harten Fälle:
  `void*`/`union`/`private_data`/`data`-Felder, deren echten Typ erst der **Closed-World-Caller**
  (`--closed-world`, [`closed-world-member-provenance`]) festlegt. `RetSummary::Field { arg,
  offset, pointee }` mit *beliebigem* Offset (nicht nur offset-0), transitive DWARF-Ketten
  `a->b->c->d` durchgängig. **Soundness:** unter `--assume-valid-params`/`--closed-world` (benannt).
- **A2 — Parameter-Contract-Summaries.** Aus den *eigenen Zugriffen* eines Callees ableiten,
  welche Größe/Validität er für jeden Zeiger-Parameter voraussetzt, und diese Precondition an alle
  sichtbaren Caller propagieren (Cross-Fn-Fixpunkt). Schließt „uncontracted parameter" (1990)
  ohne getypte Nutzung. Unter `--closed-world` werden **alle** verbleibenden Raw-Pointer-Params
  gegeben einen Caller geschlossen (heute für C/C++ validiert — auf Rust/Kernel ausweiten).
- **A3 — `RetSummary::Global`/`NonNull` + int-to-ptr-Breite.** Funktionen, die eine Global-Adresse
  oder einen definitiv-non-null-Zeiger zurückgeben; untypisierte `inttoptr` breiter recovern
  (per-cpu/phys/container_of). Schließt „opaque call result"-Rest + „int-to-pointer" (851).
- **A4 — Downstream-Kaskade (automatisch).** non-null (1887), in-object (1289), in-bounds (1103),
  alignment (892), null/int (594) sind an Provenance gegated und lösen sich mit A1–A3 mit — **~5764
  Residuen ohne eigene Arbeit.**

**Aufwand:** groß (IR + Executor + Fixpunkt + Closed-World-Typenschluss). **Schätzung: −50 pp.**

## Phase B — Loop- & Container-Vollständigkeit (~20 % → ~12 %)

- **B1 — Container-Invarianten** für den *standardisierten* Kernel-Satz: `list_for_each_entry`,
  `hlist`, `rb_node`, `xarray`/`radix_tree`, `llist`. Ein Iterator bleibt in gültigen Knoten des
  deklarierten Typs (Vertrag, opt-in). Schließt „loop-havocked pointer".
- **B2 — Induktions-Breite:** mehr Muster (mehrdimensionale Arrays, verschachtelte Loops,
  `memchr`/`strlen`-Sentinel-Loops), damit „loop-body / unsupported op" (~1600) sinkt.
- **B3 — Multi-Index/Vektor-`getelementptr`** (dokumentierte Frontend-Lücke, droppt Funktionen zu
  `unanalyzed` → jede ist ein UNKNOWN). Vollständig lowern. **Schätzung: −8 pp.**

## Phase C — Kernel-Idiom-Annahmen-Schicht (~12 % → ~7 %)

Opt-in, als Annahme ausgewiesen (`--assume-kernel-idioms`):
- **C1 — ERR_PTR/IS_ERR/PTR_ERR:** Fehlerzeiger-Wertebereich; auf dem `!IS_ERR`-Pfad ist der
  Zeiger valide. (Zuvor zurückgestellt — hier bewusst als *benannte* Annahme, nicht im strikten
  Pfad, mit branch-sensitiver Provenance-Verfeinerung auf der Erfolgskante.)
- **C2 — `container_of`/`this_cpu_ptr`/`rcu_dereference`/`list_entry`** als Contract „returns valid
  `T*`" flächendeckend (Contract-Sprache erweitern). **Schätzung: −5 pp.**

## Phase D — Devirtualisierungs-Vollständigkeit (~7 % → ~4 %)

Ein unaufgelöster indirekter Call havoct alles danach. Heute: konstante ops-Struct-Loads devirt.
Ausbauen auf: vtable-/fnptr-Felder aus dem Closed-World-Initializer, `ops`-Register-Tabellen,
`static const struct …_ops`. Jeder aufgelöste Dispatch entsperrt die ganze Kette dahinter (großer
Multiplikator). **Soundness:** die Auflösung ist definit (konstante Tabelle) — sound, oder unter
`--closed-world` benannt. **Schätzung: −3 pp.**

## Phase E — Frontend-/Decoder-Lückenschluss (~4 % → ~2 %)

Jede zu `unanalyzed` gedroppte Funktion ist ein UNKNOWN (SCAN10: „dropped" > 0). Restliche
unsupported LLVM-Konstrukte, exotische Intrinsics, Inline-asm-Ausgänge (via Contracts), breite
Integer (i256/i512 — bit-präzise-Domäne teilweise erweitern oder als word-weise Modell). **−2 pp.**

## Phase F — Der unentscheidbare Kern (~2 % → < 1 %)

Was strikt UNKNOWN bleibt, wird **nur** durch die benannte Annahmen-Schicht + Attack-Surface-
Scoping decided:
- **F1 — Attack-Surface-Skopierung** (`--attack-surface` + `--closed-world`): nur syscall/ioctl-
  erreichbarer Code braucht adversariale Parameter; der Rest darf Caller-etablierte Invarianten
  annehmen → decided-unter-Annahme. Das verschiebt den „genuin adversarialen" Kern auf die kleine,
  tatsächlich erreichbare Angriffsfläche.
- **F2 — „Decided-unter-Annahme"-Buchhaltung:** ein UNKNOWN, das unter einer *ausgewiesenen*
  Annahme zu PASS/FAIL würde, wird als solches gezählt (getrennter Bucket, Annahme im Proof-Tree).
  Der verbleibende *harte* Kern (kein Annahmen-Bundle schließt ihn) ist die ehrliche Rest-Zahl —
  Ziel: **< 1 %** genuin, plus < 2 % decided-unter-Annahme = **< 3 % UNKNOWN gesamt.**

---

## Trajektorie & ehrliche Decke

| Nach Phase | UNKNOWN (Schätzung) | decided | Rest ist… |
|---|---|---|---|
| heute (SCAN10) | ~70 % | ~30 % | Provenance |
| A (Provenance) | ~20 % | ~80 % | Loops/Container |
| B (Loops/Container) | ~12 % | ~88 % | Idiome |
| C (Kernel-Idiome) | ~7 % | ~93 % | Dispatch |
| D (Devirt) | ~4 % | ~96 % | Frontend-Lücken |
| E (Frontend) | ~2 % | ~98 % | genuin-adversarial |
| F (Annahmen-Schicht) | **< 3 %** ✔ | **> 97 %** | genuin-hart (< 1 %) |

**A–B sind größtenteils sound** (Under-Approximation + `--assume-valid-params`/`--closed-world`).
**C–D–F ruhen wesentlich auf benannten Annahmen** — hier entsteht die < 3 %, nicht als strikt-sound.
Die **strikt-sound-decided-Rate** landet realistisch bei **~88–93 %**; die Lücke von dort auf > 97 %
ist die Annahmen-Schicht.

## Mess- & Soundness-Disziplin (jede Phase, unverhandelbar)

1. **Vor Merge:** Miri- + C-ASan/UBSan-Orakel SOUND (0 false PASS/FAIL), volle Testsuite, clippy.
2. **Fortschritt** per vollem Kernel-Scan (Checkpoint, kein harter Timeout), decided auf
   **Funktions**-Ebene; pro Phase ein frisches **Residual-Histogramm** (welche Klasse blieb).
3. **Jede Annahme** als benannte Assumption im Proof-Tree (wie `param-valid`), plus ein
   **Report-Split**: „sound-decided" vs. „decided-unter-Annahme X" vs. „genuin-UNKNOWN". Ohne
   diesen Split ist die < 3 %-Zahl nicht interpretierbar.
4. **Differential auch für die Annahmen:** ein Annahmen-Bundle, das einen Miri-/ASan-UB-Fall zu
   PASS macht, ist ein Bug im Bundle — die Orakel testen das Bundle mit.

## Priorität nach Hebel × Machbarkeit

1. **Phase A** zuerst und mit Abstand — allein −50 pp, größtenteils sound, klarer Bauplan.
2. **Phase D (Devirt)** früh vorziehen (kleiner Aufwand, großer Ketten-Multiplikator).
3. **B, C, E** parallelisierbar, monoton.
4. **F** zuletzt — es ist Buchhaltung + Scoping, keine Analyse-Präzision; ohne A–E bringt es nichts.
