# Großer Plan: UNKNOWN auf ≤ 5 % (≥ 95 % decided)

**Stand:** 2026-07-27. Dieser Plan ersetzt die optimistische Prognostik von
[`unknown-under-3pct-roadmap.md`] nicht, sondern **erdet sie mit frischen Messdaten** und korrigiert
drei Modell-Annahmen, die sich empirisch als falsch erwiesen haben. Ziel bewusst **5 %** (nicht 3 %):
das liegt näher an der ehrlichen strikt-sound-Decke und braucht die benannte-Annahmen-Schicht nur für
die letzten paar Prozentpunkte.

**Kardinalregel unverändert:** nie ein false PASS. Unsound-im-Allgemeinen nur hinter benannter,
im Proof-Tree sichtbarer Annahme; beide Orakel (Miri + C-ASan/UBSan) pro Schritt.

> **Nachtrag 2026-07-29.** [`unknown-under-3pct-roadmap.md`](./unknown-under-3pct-roadmap.md) ist
> keine konkurrierende Roadmap mehr, sondern die **Arbeitspaket-Fassung dieses Plans**: dieselben
> Phasen mit Code-Ankern, Schritten und Akzeptanzkriterien, plus die letzten 2 pp (≤ 5 % → ≤ 3 %),
> die reines Scoping + Annahmen-Buchhaltung sind. Dieses Dokument bleibt die **Diagnose**
> (*warum* steckt decided bei 28 %), jenes die **Ausführung**.
>
> Ein Code-Audit am 2026-07-29 hat außerdem einen planrelevanten Befund für Phase 1 ergeben:
> `verifier/src/wholeprog.rs:119` befüllt `field_types` **ausschließlich unter `closed_world`**.
> Der `mm`-Lauf oben lief **ohne** `--closed-world`, dort war die §3-Feld-Typ-Karte also
> strukturell wirkungslos — ein billig prüfbarer Kandidat für „warum feuert 1a unterproportional".
> Als AP-1.0 vor allen anderen Phase-1-Paketen zu messen.

---

## 0. Gemessener Ist-Zustand (2026-07-27, aktuelles Binary)

Abgeschlossene Scans (das `== coverage ==`-Summary erscheint **nur** bei vollständigem Lauf — alle
bisherigen 37k-Kernel-Scans wurden nach Stunden in Pass-2 mit SIGTERM (exit 143) gekillt, bevor es
gedruckt wurde, daher gibt es **keine** abgeschlossene Whole-Kernel-Zahl):

| Korpus | Funktionen | PASS | FAIL | **UNKNOWN** | decided |
|---|---|---|---|---|---|
| `mm` (offen) | 5782 | 25,2 % | 2,2 % | **72,6 %** | 27,4 % |
| `mm` + `--assume-inttoptr-valid` | 5782 | 25,2 % | 2,2 % | **72,7 %** | 27,3 % |
| `kernel` (`--closed-world`) | 15439 | 26,9 % | 1,9 % | **71,2 %** | 28,8 % |

**Kernbeobachtung:** trotz umfangreicher, bereits gelandeter Provenance-Arbeit (P2 caller-directed
push, §3 Feld-Typ-Karte, P4 Points-to-Devirt, closed-world member-provenance) steckt die Decided-Rate
bei **~28 %** — weit unter den ~80 %, die Phase A der alten Roadmap prognostizierte. Dieser Plan
diagnostiziert **warum** und leitet daraus die Prioritäten ab.

---

## 1. Drei empirische Befunde (die die alte Roadmap-Prognostik korrigieren)

### Befund 1 — Decided ist per-Funktion durch die **schlechteste** Obligation gedeckelt
`report_scan` zählt eine Funktion als UNKNOWN, sobald **eine einzige** ihrer Proof-Obligations
unentschieden ist. Eine Funktion mit 50 Zugriffen, von denen 49 PASSen und 1 UNKNOWN bleibt, zählt
komplett als UNKNOWN. Um Funktions-decided von 28 % auf 95 % zu heben, muss also in **fast jeder**
Funktion **jede** Obligation entschieden werden — ein extrem strenger Multiplikator, der gegen uns
arbeitet.

### Befund 2 — Eine Residual-**Klasse** zu schließen kippt fast **keine** Funktion
Experiment: `--assume-inttoptr-valid` schließt die mit Abstand größte Residual-Klasse in `mm`
(int-to-pointer, **81.122** von ~140k Residuen = ~60 %). Effekt auf Funktions-decided: **27,4 % →
27,3 %** (−0,1 pp, faktisch null). Grund: die betroffenen Funktionen tragen **mehrere** unabhängige
Residual-Ursachen; eine davon zu schließen lässt die anderen stehen → die Funktion bleibt UNKNOWN.
**Konsequenz:** Fortschritt entsteht nur, wenn die Residual-Ursachen **pro Funktion korreliert**
geschlossen werden, nicht klassenweise über den ganzen Korpus.

### Befund 3 — Provenance **ohne Größe** löst die Kaskade NICHT, sie **verschiebt** sie
Die alte Roadmap nahm an: „non-null / in-object / in-bounds / alignment lösen sich automatisch,
sobald die Herkunft bekannt ist" (~5764 Folge-Residuen „ohne eigene Arbeit"). **Empirisch falsch.**
Mit `--assume-inttoptr-valid` verschwindet zwar `int-to-pointer` (die Provenance ist jetzt bekannt:
eine valide Region), aber **`could not prove in bounds` springt von 2.402 → 22.551**, `alignment` von
932 → 3.333, `one-past-end` von 3.135 → 3.428. Der Zeiger ist jetzt valide, aber **größenlos** —
also ist die In-Bounds-Prüfung nicht beweisbar, und das Residual ist nur von „Provenance" nach
„Bounds" gewandert. **In-Bounds braucht eine GRÖSSE, Alignment braucht `base_align` — Validität
allein genügt nicht.** Nur **getypte** Provenance (Pointee-Typ → `sizeof` → Größe + Align) löst die
Kaskade wirklich; größenlose Provenance (int-to-ptr, opaker Call ohne Größe) tut es nicht.

**Fazit der drei Befunde:** Das Ziel ist nicht „die größte Residual-Klasse schließen", sondern
**pro Funktion alle Residual-Ursachen mit GETYPTER (dimensionierter) Provenance schließen.** Das ist
schwerer und anders priorisiert als die alte Roadmap annahm.

---

## Phase 0 — Mess-Infrastruktur (Voraussetzung für alles Weitere)

Ohne diese kann kein Fortschritt gemessen oder gesteuert werden — sie ist der teuerste bisher
fehlende Baustein (das obige Histogramm musste ich per-Datei von Hand aggregieren).

- **0a — Residual-Histogramm in `scan`.** `report_scan` aggregiert die `ObligationResult::Open`-
  Residuen (`predicate`/`reason`) über den ganzen Lauf und druckt eine nach Häufigkeit sortierte
  Tabelle. Ohne dieses Signal ist jede Phase blind. (Klein, rein additiv.)
- **0b — Per-Funktion-Residual-**Anzahl**-Verteilung.** Wie viele *verschiedene* Residual-Ursachen
  hat eine UNKNOWN-Funktion im Median? Befund 2 sagt „mehrere" — die Verteilung quantifiziert, wie
  viele Klassen man *gemeinsam* schließen muss, um die Funktion zu kippen. Steuert die Reihenfolge.
- **0c — Abgeschlossener Full-Kernel-Scan.** Der 37k-Lauf muss bis zum `== coverage ==`-Summary
  durchlaufen (Checkpoint/Resume robust, Mem-Headroom, kein SIGTERM). Ohne eine *abgeschlossene*
  Whole-Kernel-Zahl steuern wir nach Subset-Proxys. (Ursache des exit-143 zuerst diagnostizieren:
  Mem-Target? OOM? Reboot? — `CSOLVER_SCAN_CHECKPOINT` existiert bereits.)
- **0d — Report-Split.** Jede decided-Zahl in drei Buckets: **sound-decided** / **decided-unter-
  benannter-Annahme X** / **genuin-UNKNOWN**. Ohne diesen Split ist „5 %" nicht interpretierbar.

**Aufwand:** klein–mittel. **Hebel:** 0 pp direkt, aber Voraussetzung für die Steuerbarkeit aller
folgenden Phasen. **Zuerst.**

---

## Phase 1 — Getypte (dimensionierte) Provenance-Vollständigung

Der eigentliche Hebel (Befund 3): Provenance, die **Größe + Align** mitliefert, damit die
In-Bounds/Alignment-Kaskade *tatsächlich* auflöst. Die Mechanismen sind größtenteils gebaut
(§3 Feld-Typ-Karte, `size_hinted_pointer`, `RetSummary::ValidRef`) — Phase 1 ist **Vervollständigung
+ Verdrahtungs-Audit**, nicht Neubau.

- **1a — Feld-Typ-Karte (§3) end-to-end validieren.** Warum feuert sie auf dem Kernel unter-
  proportional? (Befund: Decided steckt trotz Landing.) Pro-Residual prüfen: liefert die
  `(struct, offset) → pointee`-Karte für die dominanten `void*`/`union`/`private_data`-Loads einen
  Typ, und greift `size_hinted_pointer` damit? Lücken schließen (transitive Ketten `a->b->c->d`
  durchgängig, beliebiger Offset, nicht nur offset-0). **Liefert Größe → Kaskade löst.**
- **1b — Param-Closure (P2) unter `--closed-world` für Rust/Kernel.** Jeder rohe Pointer-Param
  bekommt die schwächste Caller-Garantie **inkl. Größe** (aus dem getypten Argument, nicht nur
  `alloca`). Für C/C++ validiert; auf Kernel ausweiten. Schließt „uncontracted parameter" **mit
  Größe**.
- **1c — `RetSummary::Field { arg, offset, pointee }`** (Feld-Accessor-Return beliebigen Offsets),
  Pointee-Typ aus 1a. Schließt „loaded value" interprozedural mit Größe.

**Soundness:** alles unter `--assume-valid-params` / `--closed-world` (benannt). **Hebel-Schätzung
(revidiert, konservativer als alte Roadmap):** −20 bis −30 pp — aber **nur** wenn 1a wirklich Größe
liefert (Befund 3). Messen nach 0a.

---

## Phase 2 — Größen-Recovery für **untypisierte** Provenance

Der Teil, den Phase 1 nicht erreicht (int-to-ptr, opake Calls ohne Typ) — genau der `mm`-Kern und
der Grund, warum `--assume-inttoptr-valid` allein nichts brachte (Befund 3).

- **2a — Bekannte Kernel-Größen für int-to-ptr-Idiome:** `page` → `PAGE_SIZE`, per-cpu-Var → Typ-
  Größe, `phys_to_virt`/`__va` → Mapping-Größe, `container_of` → Container-Typ-Größe. Als Contract/
  Idiom-Tabelle (`--assume-kernel-idioms`), damit die materialisierte Region eine **Größe** trägt.
- **2b — Guarded-Access-Beweis breiter** (`--assume-field-invariants` / bestehender
  `assume_guarded_index`): ein größenloser, aber durch ein Bound-Guard (`if (i < n)`) beschränkter
  Zugriff PROVEt in-bounds, auch ohne Region-Größe. Muster erweitern (Feld-Länge, Loop-Bound).
- **2c — One-past-end/Alignment-Feinschliff:** die +3.4k one-past-end und +3.3k alignment aus dem
  int-to-ptr-Experiment gezielt adressieren (base_align aus Idiom-Größe, gcd-Faltung).

**Soundness:** opt-in benannte Annahmen (Idiome sind kernel-spezifische Fakten, kein strikt-sound).
**Hebel:** −8 bis −12 pp im speicher-lastigen Code (`mm`, page-alloc, dma).

---

## Phase 3 — Loop-/Container-Vollständigkeit

Die **zweitgrößte** Klasse im frischen Histogramm: `memory op not analyzed (loop body / unsupported
op)` = **11.230** Residuen (unabhängig von Provenance). Ein loop-havockter Zeiger/Zugriff kippt die
Funktion.

- **3a — Container-Invarianten** für den Standard-Satz (`list_for_each_entry`, `hlist`, `rb_node`,
  `xarray`, `llist`): der Iterator bleibt in gültigen, dimensionierten Knoten des deklarierten Typs
  (Contract, opt-in). Liefert **getypte** (also dimensionierte) Loop-Pointer → löst auch die Kaskade.
- **3b — Induktions-Breite:** mehrdimensionale Arrays, verschachtelte Loops, Sentinel-Loops
  (`strlen`/`memchr`). Senkt „unsupported op" im Loop-Body.

**Hebel:** −6 bis −10 pp.

---

## Phase 4 — Devirtualisierungs-Vollständigkeit (Ketten-Multiplikator)

Ein unaufgelöster indirekter Call havoct **alles danach** — ein einziger kippt die ganze Funktion.
Heute: konstante ops-Struct-Loads devirt (P4). **Wichtiger Befund aus dem Rescan (2026-07-27):** der
Copy-Cycle-Collapse reduziert den Kernel-Points-to-Graphen **nicht** (0,0 %, azyklisch) → Full-Kernel-
Devirt bleibt budget-übersprungen. **Der echte Node-Reduktions-Hebel ist HVN** (Hash-Value-Numbering:
azyklisch-äquivalente Knoten mergen), damit die 14,2M-Knoten-Relation unter Budget solved und Devirt
überhaupt läuft.

- **4a — HVN** (Voraussetzung, damit Full-Kernel-Devirt aktiv wird — sonst ist Phase 4 auf dem Kernel
  wirkungslos). Sound-für-Devirt (Merge vergrößert Sets nur).
- **4b — Devirt-Breite:** vtable-/fnptr-Felder aus dem Closed-World-Initializer, `ops`-Register-
  Tabellen, `static const struct …_ops`.

**Hebel:** −3 bis −5 pp, aber großer Multiplikator (jede aufgelöste Kette entsperrt viele
Downstream-Obligations in derselben Funktion — genau was Befund 2 verlangt).

---

## Phase 5 — Frontend-/Decoder-Lückenschluss

Jede zu `unanalyzed` gedroppte Funktion ist **direkt** ein UNKNOWN. Aktuell klein (`dropped` = 1–4
pro Subset), aber jeder Drop ist teuer (ganze Funktion).

- **5a — Restliche `unsupported`-Drops:** multi-index/vektor-`getelementptr`, switch auf Nicht-
  Integer, Typ-Zyklen.
- **5b — Wide-Ints > 128 bit:** der Kern-`BitVector` ist `u128`-gebunden (word-weises Modell nötig —
  großer Kern-Rewrite; siehe TODO). Betrifft Crypto/SIMD.
- **5c — Inline-asm-Ausgänge via Contracts** (Mechanismus gebaut, Session 3).

**Hebel:** −1 bis −2 pp.

---

## Phase 6 — Benannte-Annahmen-Schicht + Attack-Surface-Scoping (die letzten pp)

Der genuin-adversariale Kern (angreifer-beeinflusste Dispatch-Ziele, daten-abhängiges Aliasing) wird
**nur** durch Scoping + benannte Annahmen decided:

- **6a — Attack-Surface** (`--attack-surface` + `--closed-world`): nur syscall/ioctl-erreichbarer
  Code braucht adversariale Parameter; der Rest darf Caller-etablierte, **dimensionierte**
  Invarianten annehmen → decided-unter-Annahme. Verschiebt den harten Kern auf die kleine reale
  Angriffsfläche.
- **6b — Decided-unter-Annahme-Buchhaltung** (Phase 0d): der Rest-*harte* Kern (kein Annahmen-Bündel
  schließt ihn) ist die ehrliche Zahl.

**Hebel:** schließt die Lücke von der strikt-sound-Decke (~88–93 %) auf ≥ 95 %.

---

## Trajektorie (revidiert, konservativer als die alte Roadmap)

| Nach Phase | UNKNOWN (Schätzung) | decided | Bemerkung |
|---|---|---|---|
| heute (gemessen) | ~72 % | ~28 % | Provenance + Loops + per-Funktion-Deckel |
| 0 (Mess-Infra) | ~72 % | ~28 % | jetzt *steuerbar* |
| 1 (getypte Provenance) | ~45–52 % | ~48–55 % | **nur** wenn Größe geliefert wird (Befund 3) |
| 2 (Größen-Recovery) | ~35–42 % | ~58–65 % | int-to-ptr/opak mit Größe |
| 3 (Loops/Container) | ~28–35 % | ~65–72 % | die 11k Loop-Body-Residuen |
| 4 (HVN + Devirt) | ~20–28 % | ~72–80 % | Ketten-Multiplikator |
| 5 (Frontend) | ~18–26 % | ~74–82 % | Drops |
| 6 (Annahmen + Scoping) | **≤ 5 %** ✔ | **≥ 95 %** | die letzten pp unter benannter Annahme |

**Ehrliche Einordnung:** die alte Roadmap prognostizierte −50 pp allein aus Phase A; Befund 2 + 3
zeigen, dass das **nicht** eintritt, weil (a) Funktionen multi-kausal sind und (b) Provenance ohne
Größe nur das Residual verschiebt. Die revidierte Trajektorie ist deutlich flacher und braucht
**alle** Phasen zusammen — es gibt keinen einzelnen −50-pp-Sprung. **Strikt-sound-decided** landet
realistisch bei ~80–88 %; die Lücke auf ≥ 95 % ist die benannte-Annahmen-Schicht (Phase 6), im
Proof-Tree ausgewiesen.

---

## Priorität nach Hebel × Machbarkeit × Befund-Konsistenz

1. **Phase 0 zuerst, unverhandelbar** — ohne Residual-Histogramm im Scan + abgeschlossenen
   Full-Kernel-Lauf ist jeder weitere pp-Anspruch nicht belegbar (das ist die Lehre aus „−0,1 pp bei
   der größten Klasse": ohne Messung hätte man das Gegenteil vermutet).
2. **Phase 1 (getypte Provenance)** — der Hebel, *sofern* er Größe liefert; nach 0a pro-Residual
   verifizieren, dass die Kaskade wirklich löst (nicht nur die Provenance-Klasse verschwindet).
3. **Phase 3 (Loops)** früh — 11k Residuen, unabhängig von Provenance, klarer eigener Block.
4. **Phase 4 (HVN→Devirt)** — großer Multiplikator, aber HVN ist Voraussetzung (der Cycle-Collapse
   ist auf dem azyklischen Kernel ein No-op, empirisch belegt 2026-07-27).
5. **Phase 2, 5** parallelisierbar.
6. **Phase 6** zuletzt — Scoping + Buchhaltung, keine Analyse-Präzision.

## Mess- & Soundness-Disziplin (jede Phase)

1. **Vor Merge:** Miri + C-ASan/UBSan SOUND (0 false PASS/FAIL), volle Testsuite, clippy.
2. **Fortschritt** per abgeschlossenem Kernel-Scan (Phase 0c), decided auf Funktions-Ebene, plus ein
   frisches Residual-Histogramm (Phase 0a) — **welche Klasse blieb, und kippten Funktionen wirklich**
   (Befund 2: Klassen-Reduktion ohne Funktions-Flip ist kein Fortschritt).
3. **Jede Annahme** als benannte Assumption im Proof-Tree; Report-Split sound/annahme/hart (0d).
4. **Differential testet die Annahmen-Bündel mit** — ein Bündel, das einen Orakel-UB-Fall zu PASS
   macht, ist ein Bug im Bündel.
