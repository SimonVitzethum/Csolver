# Roadmap: Decided-Rate auf ≥ 95 % (Kernel)

**Ziel:** den Anteil *entschiedener* Kernel-Funktionen (PASS = beweisbar sicher ODER FAIL =
refutiert) von aktuell **~15 %** auf **≥ 95 %** heben — ohne Soundness aufzugeben (kein false
PASS, kein false FAIL im strikten Pfad).

**Baseline (2026-07-14, frische Whole-Program-Scans):** `mm` 13,6 % decided (86,4 % UNKNOWN),
`ipc` 10,6 %. Kernelweite Schätzung: **~15–20 % decided, ~80–85 % UNKNOWN**.

## Warum die Rate hoch ist — und wo der Hebel sitzt

Zwei Fakten bestimmen den Plan:

1. **Funktion-decided ist durch die *schlechteste* Obligation gedeckelt.** Eine Funktion ist erst
   PASS/FAIL, wenn *alle* ihre Obligationen entschieden sind. Die Obligations-Ebene ist viel
   besser entschieden als die Funktions-Ebene — d. h. jede Funktion hängt meist an *einer* Klasse
   ungelöster Obligationen. Wer diese Klasse schließt, kippt viele Funktionen auf einmal.
2. **Die dominante ungelöste Klasse ist interprozedurale Zeiger-Provenance.** Der Kern-Engpass:
   `RetSummary::Unknown` — ein Call, dessen Zeiger-Rückgabe nicht parameter-relativ ist (Heap-
   Alloc, Feld-Load, Global, valide Referenz), zwingt den Caller zum Havoc → alle Folgezugriffe
   UNKNOWN. Das kaskadiert: EIN aufgelöster Call-Rückgabewert entsperrt oft eine ganze Kette.

**Nicht** zeitlimitiert (unbegrenzte Zeit ändert nichts, gemessen) und **nicht** durch mehr
Recall-Flags lösbar — es ist ein *Modellierungs*-Problem. Die Reihenfolge unten ist nach
Hebel × Machbarkeit geordnet; jede Phase ist einzeln sound und gegen die Orakel (Miri, C-ASan/
UBSan) + einen `mm`-Scan zu validieren, bevor die nächste beginnt.

---

## Phase 0 — Fundament: reiche interprozedurale Zeiger-Provenance-Summaries

Der Enabler für Phase 1–3. Heute trägt `Summary.ret` nur `Unknown | Scalar | PtrFromArg |
DanglingStack`. Erweitern auf:

- `RetSummary::Alloc { size }` — die Funktion gibt eine frische Heap-Region bekannter Größe zurück
  (ein Allocator-Wrapper). Am Call-Site → sizierte Heap-Region statt Havoc.
- `RetSummary::Field { arg, offset, pointee_size }` — gibt einen aus `arg->feld` geladenen Zeiger
  zurück (mit DWARF-Pointee → sizierte Region, `assumed` unter `--assume-valid-params`).
- `RetSummary::Global { name }` / `ValidRef { size, writable }` / `NonNull`.

Plus ein **Parameter-Pointer-Contract-Summary** (welche Größe/Validität ein Callee für jeden
Zeiger-Parameter *voraussetzt*, aus seinen eigenen Zugriffen abgeleitet) und Fortführung des
Cross-Fn-Fixpunkts (`finalize` + `summarize_module` in Lockstep, Losslessness-Orakel).

**Soundness:** jede neue Ret-Form ist eine Unter-Approximation (nur wenn *definitiv* zutreffend);
`Alloc`/`Field` unter der bestehenden `--assume-valid-params`/`alloc-succeeds`-Annahme. **Aufwand:**
mittel-groß (IR + Executor-Anwendung + Fixpunkt). **Gate:** Orakel SOUND, `mm`-Scan ≥ Baseline.

## Phase 1 — Return-Provenance anwenden (#1 opaque call result, ~6300 Obl.)

Mit Phase 0 löst ein Call, der eine Alloc/Feld/Ref/Global-Rückgabe hat, am Call-Site eine echte
Region statt `POrigin::Call`-Opak. Whole-Program-Fixpunkt propagiert das über TU-Grenzen.
**Erwarteter Sprung: der größte einzelne** — interprozedurale Zeiger entsperren die meisten Ketten.
**Schätzung: ~15 % → 40–55 % decided.**

## Phase 2 — Kernel-Idiom-Contracts (#3 int-to-pointer, ~5800 + Struct-Chasing)

Die per-cpu/`inttoptr`-Fälle sind fast alle **Kernel-Invarianten**, sound als Contracts (opt-in,
wie `--assume-valid-params`; sie sind per Definition gültig):
- `current` (`%gs`-per-cpu) → valider `task_struct*`.
- `container_of(ptr, T, member)` → valider `T*`, wenn `ptr` valide (Rückwärts-Offset).
- `this_cpu_ptr`/`per_cpu_ptr`, `list_entry`/`hlist_entry`, `rcu_dereference`.
- `ERR_PTR`/`IS_ERR`/`PTR_ERR` → Fehlerzeiger-Wertebereich (entsperrt `if(IS_ERR(p))`-Guards).

Erweitert die Contract-Sprache (`crates/contracts`) um „returns valid `T*`" / „error-pointer".
**Soundness:** Kernel-Invarianten, opt-in, als Annahme ausgewiesen. **Schätzung: +15–20 %.**

## Phase 3 — Container-/Loop-Zeiger-Modellierung (#2 loop-havocked, ~5800)

Der `modified`-Set ist präzise; der Rest sind *echte* Moving-Zeiger. Aber der Kernel nutzt einen
**kleinen, standardisierten** Satz intrusiver Container. Modelliere deren Invariante: ein
`list_for_each`/`list_for_each_entry`-Iterator bleibt in gültigen Listenknoten; `rb_node`/`hlist`
analog. Plus mehr Induktionsmuster (der Array-Stride-Fall ist schon abgedeckt).
**Soundness:** die Container-Invariante ist ein Kernel-Vertrag (opt-in). **Aufwand: groß.**
**Schätzung: +10–15 %.**

## Phase 4 — Guard-Vollständigkeit (#4-Rest + Bounds, interprozedural)

Der Null-Guard (opake `ptr#id`-Symbole + Pfadbedingung) ist umgesetzt. Ausbauen auf:
- **Vollständige Bounds-Guard-Propagation** durch die CFG (Intervall-Domäne ist da; Feld-Guards
  und interprozedurale Guards fehlen).
- **Caller→Callee-Skalar-Preconditions** (teilweise vorhanden: `caller-range-precondition`) —
  ein im Caller geprüfter Index/Länge fließt in den Callee.
**Schätzung: +5–10 %.**

## Phase 5 — Long Tail (#5, #6, #7 + Frontend/Decoder-Lücken)

Monoton wachsende Einzelabdeckung: Multi-Index-/Vektor-`getelementptr` (dokumentierte Lücke, droppt
Funktionen zu `unanalyzed`), restliche unsupported Ops, uncontracted Params ohne DWARF,
Devirtualisierung weiterer indirekter Calls (ops-Struct/vtable). **Schätzung: +5 %.**

---

## Trajektorie & ehrliche Decke

| Nach Phase | Kumulativ decided (Schätzung) |
|---|---|
| Baseline | ~15 % |
| 0+1 (Return-Provenance) | 40–55 % |
| 2 (Kernel-Idiome) | 60–72 % |
| 3 (Container) | 72–82 % |
| 4 (Guards) | 80–88 % |
| 5 (Long Tail) | 85–93 % |

**Die letzten ~2–10 % auf 95 % sind die härtesten** und stoßen an eine **Soundness-Decke**: ein
Restanteil (grob 3–7 %) ist *genuin* unentscheidbar ohne Soundness-Verlust — angreifer-beeinflusste
indirekte Dispatch-Ziele ohne Devirtualisierung, daten-abhängige Aliasing-Muster, tief-verschachtelte
Provenance über opake Grenzen. Für die bleibt „UNKNOWN" die *korrekte* Antwort.

**Verdikt:** 95 % decided ist ein **Stretch-Ziel**, erreichbar *wenn* Phase 0–5 alle sauber landen
und die Kernel-Idiom-+Container-Modellierung umfassend ist. Realistisch bringen Phase 0–2 den
Großteil (auf ~60–72 %), Phase 3–4 den Sprung auf ~80–88 %; die 95 %-Marke erfordert zusätzlich das
systematische Abschleifen des Long Tails **und** die Akzeptanz, dass die letzten Prozente teils
„known-unknown" bleiben (der Verifier sagt korrekt: unentscheidbar). Wo genau die Decke liegt, misst
man erst nach Phase 3 belastbar.

## Querschnitt: Mess- & Soundness-Disziplin (jede Phase)

1. **Vor Merge:** Miri- + C-ASan/UBSan-Orakel = SOUND (0 false PASS), volle Testsuite grün,
   `cargo clippy` sauber.
2. **Fortschritt messen** per `solver scan mm` (Whole-Program, Budget-Defer statt harter Timeout —
   siehe `docs/`), nicht per hart-getimeoutetem per-Datei-Loop.
3. **Decided auf Funktions-Ebene** ist die Zielmetrik; die Obligations-Ebene als Frühindikator.
4. Jede neue Annahme (Kernel-Invariante, Container-Vertrag) wird als benannte Assumption im
   Proof-Tree ausgewiesen (wie `param-valid`/`alloc-succeeds`), damit „decided" prüfbar bleibt.
