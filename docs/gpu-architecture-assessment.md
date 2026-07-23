# GPU-Portability-Bewertung des CSolver-Kerns

**Frage:** Lässt sich die Architektur so umstrukturieren, dass der Solver *gut und effizient* auf
einer GPU läuft?

**Kurzantwort:** Als Ganzes **nein** — der Kern ist control-flow-gebunden, irregulär und
pointer/index-indirekt; seine Parallelität ist grobkörniges MIMD, das schon CPU-Kerne sättigt.
Es gibt **eine** genuin GPU-förmige Teilstruktur (Millionen winziger, unabhängiger,
breiten-beschränkter Entscheidungs-Queries), die als **untrusted Batch-Decision-Service**
ausgelagert werden *könnte* — aber mit großem Rewrite, unsicherem Nutzen und weiterhin
CPU-seitiger Soundness-Prüfung. Wer Durchsatz will, skaliert die vorhandene coarse-grain-
Parallelität risikoarm über mehr CPU-Kerne/Cluster.

---

## 1. Wo die Zeit wirklich hingeht (das entscheidet alles)

Die Beweisstrategie ist **linear-first** (`solver/src/lib.rs:77` `prove_implies_method`):

1. **Linear** (Fourier–Motzkin, `linear.rs`) — billig, entscheidet den *Großteil* der
   Memory-Safety-Ziele (unter `linear-no-overflow`).
2. **Bit-präzise Verfeinerung** (kleines SAT-Budget) — nur um die Annahme fallenzulassen.
3. **Bit-präziser Fallback** (SAT, `FALLBACK_BUDGET=200_000`) — nur wenn linear scheitert.

Darüber liegt der eigentliche Kostenträger: der **merge-basierte symbolische Executor**
(`crates/symbolic`, ~12k LOC) pro Funktion, plus der **coarse-grain Scan** über tausende
Funktionen (`crates/cli/src/scan_dir.rs`, `thread::scope`+`spawn`, `worker_count`).

**Konsequenz:** „GPU beschleunigt den SAT-Solver" zielt auf eine **Minderheit** der Arbeit — und
ausgerechnet auf den divergentesten Teil. Der SAT-Kern ist ein *budgetierter Fallback*, kein
Hot-Path.

---

## 2. Warum der Kern GPU-feindlich ist (belegt aus dem Code)

GPUs (SIMT) wollen: tausende Threads, *gleicher* Instruktionsstrom auf *verschiedenen* Daten,
koaleszierte Speicherzugriffe, minimale Divergenz, minimale dynamische Allokation. CSolver
liefert das Gegenteil auf jeder Ebene außer der grobkörnigen:

### 2a. Coarse-grain (Funktionen/Dateien) — MIMD, nicht SIMT
Tausende **unabhängige** Tasks — aber jeder ist eine *andere*, verzweigte, irreguläre Rechnung:
eigenes CFG, HashMap-lastiger `PathState` (Regionen/Heap-Store-Records/env/facts/pathcond), ein
**hash-cons-Term-DAG** (`solver/src/expr.rs:159`, `nodes: Vec<Node>` + `intern`-Map,
Index-Chasing). Eine Funktion pro GPU-Thread ⇒ katastrophale Warp-Divergenz + irreguläre
Speicherzugriffe + dynamisches Vec/HashMap-Wachstum (auf der GPU nicht darstellbar). Das ist das
Sweet-Spot-Profil einer **Mehrkern-CPU**, nicht einer GPU.

### 2b. Der SAT-Inner-Loop — inhärent sequentiell + divergent
Aus der Code-Kartierung (`crates/solver/src/sat.rs`, `sat_learn.rs`):
- **BCP / 2-watched literals** (`sat.rs:239`): geschachtelte Loops mit Early-Outs, variabler
  Inner-Scan `2..clause.len()`, bedingte Watch-Migration, daten-abhängiger Konflikt-Break; pro
  Propagation eine frische `keep`-Vec-Allokation.
- **Konflikt-Analyse 1-UIP** (`sat_learn.rs:17`): Loop-Länge = Implikationsgraph-Tiefe, über
  `seen[]`/`reason[]`-Index-Chasing — irregulär.
- **Speicherzugriff = daten-abhängiger Gather/Scatter:** `watches[lit] → clauses[ci][k] →
  assign[var]`; jede Adresse hängt vom vorherigen Load *und* der partiellen Belegung ab. Kein
  Streaming/koalesziertes Muster.
- Der CDCL-Loop selbst ist **sequentiell**: jede Entscheidung hängt vom Propagations-Fixpunkt der
  letzten ab. Klassisch schwer zu parallelisieren, GPU-SIMD nur mit vollständigem Redesign
  (geflachte Klausel-Arrays, blocking literals, GPU-BCP) — bis heute Forschungsstand, selten
  besser als ein Multicore-CPU-Portfolio.

### 2c. Was regulär *ist* (aber nicht der Engpass)
- **Bit-Blasting** (`bitblast.rs`, `blaster.rs`): feste Gatter-Schaltungen (Ripple-Adder,
  Barrel-Shifter, per-Bit-Bitwise), regulär und parallel erzeugbar — aber billig relativ zum
  Lösen.
- **`pick_branch` VSIDS** (`sat_learn.rs:137`): linearer Scan, trivial parallel-reduzierbar, aber
  winzig.
- **Intervall-/AI-Fixpunkt** (`crates/absint`): Dataflow über das CFG; Transfer-Funktionen
  verzweigt, Iteration über viele Funktionen parallel — marginal.

---

## 3. Die *eine* GPU-förmige Struktur: Batch aus Millionen winziger Queries

Der Workload hat eine Sondereigenschaft, die die SAT-Kartierung bestätigt:

- **Keine SAT-Inkrementalität** (`sat.rs:168` `Solver::new` *konsumiert* eine frische CNF; kein
  push/pop, keine Assumptions-Schnittstelle, kein Klausel-Reuse). Jede Obligation ist eine
  **vollständig unabhängige** Solver-Instanz über ihre eigene CNF.
- **Breiten-beschränkt:** `BitVector { width: u32, words: [u64;2] }`, `MAX_WIDTH = 128`. Instanzen
  sind klein (Memory-Safety-Queries sub-ms; Cap `MAX_CLAUSES = 300_000`, Budget `200_000`
  Entscheidungen, 250 ms Wall-Clock-Ventil).

Das ist **nicht** „ein großes SAT", sondern **„löse 10⁶ *winzige* unabhängige BV-Instanzen"** —
ein data-paralleles *„viele kleine Probleme"*-Muster: ein Warp/Block pro Instanz, **fixes,
allokationsfreies Klausel-Layout** (machbar, weil Instanzen klein/beschränkt sind). Das ist die
einzige lohnende GPU-Wette.

**Aber vier harte Einschränkungen:**
1. **Rewrite in fixe SoA-Form.** Die heutigen `Vec<Vec<Lit>>`-Klauseln/Watch-Lists und die
   Per-Schritt-Allokation müssen zu flachen, größen-beschränkten Arrays werden (Struct-of-Arrays,
   koaleszierbar). Großer, riskanter Umbau des Solver-Kerns.
2. **Nur die Fallback-Teilmenge.** Weil linear-first den Großteil entscheidet, ist die
   GPU-berechtigte Menge (bit-präziser Fallback) eine *Minderheit* — der Nutzen ist gedeckelt.
3. **Divergenz *innerhalb* des Warps.** Jede Instanz sucht anders; selbst „eine Instanz pro Warp"
   divergiert, weil die 32 Lanes eines Warps *eine* Instanz gemeinsam bearbeiten müssten (sonst
   verschenkt man den Warp). Genau hier scheitern GPU-SAT-Ansätze meist gegen Multicore.
4. **Soundness bleibt CPU-seitig.** Die GPU ist **untrusted**: ein gefundenes Modell (Bug) prüft
   die CPU billig nach; ein UNSAT (= PASS) darf nie ungeprüft übernommen werden — es braucht das
   bestehende Budget *plus* idealerweise ein prüfbares **LRAT-Zertifikat**, das ein kleiner
   Trusted-Checker validiert. (Siehe `docs/` zur Soundness-Disziplin.)

---

## 4. Wie eine *ehrliche* Restrukturierung aussähe (Hybrid)

Nicht „den Solver auf die GPU portieren", sondern **den irregulären Teil auf der CPU lassen und
einen batched Decision-Kernel auslagern**:

```
 CPU (Host, MIMD)                          GPU (Device, SIMT)
 ─────────────────                         ──────────────────
 Frontends, CFG, AI, Contract-Synthese,
 merge-basierter symbolischer Executor  ── sammelt ──▶  Batch aus N bit-präzisen
 (verzweigt, pointer-chasing — bleibt CPU)               BV-Goals in fixer SoA-Form
        ▲                                                       │
        │  Ergebnis + (für Bug) Modell,                         ▼
        │  (für PASS) LRAT-Zertifikat            batched fixed-layout BV/SAT-Kernel
        └────────  CPU prüft/akzeptiert  ◀────────  (untrusted, ein Block/Instanz)
```

- **Enabler:** die hash-cons-DAG-Terme in eine **flache, arena/SoA-, beschränkte** Repräsentation
  überführen (der teuerste, aber tragende Umbau).
- **Executor bleibt CPU** (inhärent verzweigt) und wird zum *Produzenten* von Goal-Batches.
- **GPU wird ein „Decision-Service"** für die bit-präzise Teilmenge — hinter CPU-Prüfung.
- Die Recall-only-Teile (Pfad-Fan-out, Kandidaten-/Witness-Suche) sind ohnehin CPU-geprüft und
  wären ebenfalls sound auslagerbar — aber auch die sind verzweigt.

---

## 5. Verdikt & Empfehlung

| Ebene | GPU-Eignung | Grund |
|---|---|---|
| Scan über Funktionen | MIMD, **CPU** | unabhängig, aber je irregulär/verzweigt |
| Symbolischer Executor | **GPU-feindlich** | HashMap/DAG-Pointer-Chasing, Divergenz, dyn. Allokation |
| CDCL-Inner-Loop | **GPU-feindlich** | sequentiell, daten-abhängiger Gather, Per-Schritt-Allokation |
| Bit-Blaster | GPU-fähig, aber **billig** | reguläre Gatter — nicht der Engpass |
| **Batch winziger BV-Queries** | **die einzige Wette** | unabhängig, beschränkt — braucht SoA-Rewrite + CPU-Prüfung |

**Empfehlung:**
1. **Für Durchsatz jetzt:** mehr CPU-Kerne / Cluster. Die coarse-grain-Parallelität skaliert
   nahezu linear, Risiko ~0, kein Rewrite. Das ist die klar beste €/Durchsatz-Option.
2. **GPU nur als Forschungswette:** einen **Prototyp des batched fixed-layout BV-Kernels** für die
   bit-präzise Fallback-Teilmenge bauen und *messen*, bevor irgendetwas committet wird — als
   untrusted Beschleuniger hinter CPU-Verifikation. Erwartung gedämpft: die Literatur zeigt, dass
   Small-Instance-GPU-SAT ein Multicore-Portfolio selten schlägt.
3. **Nicht** den symbolischen Executor oder den CDCL-Inner-Loop auf die GPU zwingen — das
   bekämpft die Natur des Problems (symbolisches Schließen ist verzweigt).

**Soundness-Fazit (unverändert):** GPU-Beschleunigung wird nicht durch eine *sichere Sprache* auf
dem Device sound, sondern durch **Prüfung der Device-Ausgabe auf dem vertrauenswürdigen
CPU-Pfad** (Modelle billig; UNSAT via Zertifikat). Der GPU-Kernel bleibt untrusted.
