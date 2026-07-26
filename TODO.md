# CSolver — offene Abdeckung (Coverage-TODO)

Code-fundierter Audit-Stand (2026-07-23). Zwei Sinne von „Abdeckung": **Bug-Klassen**
(welche Safety-Properties überhaupt *entschieden* werden) und **Decided-Rate** (wieviel %
der Funktionen PASS/FAIL statt UNKNOWN — die Provenance-Story, siehe
`docs/complete-pointer-provenance-plan.md` / `docs/unknown-under-3pct-roadmap.md`).

Kardinalregel: **nie ein false PASS**. Refutation (FAIL) nur auf feasiblem/exaktem Pfad;
unsound-im-Allgemeinen hinter benannter Annahme; beide Orakel (Miri + C-ASan/UBSan) pro Schritt.

---

## A. Genuinely ungeprüft (catalogue-only — echte Löcher)

- [ ] **`ValidReference`** — kein Referenz-Validitäts-Check; die Variante ist zum „Frontend
  konnte Funktion nicht lowern"-Marker umfunktioniert (`verifier/src/run.rs:56`).
- [ ] **`StackIntegrity` / `ValidStackFrame`** — nie emittiert (deklariert als von `InBounds`/
  `ValidIndirectTarget` subsumiert). Return-Address-Integrität hat keinen dedizierten Check.

## B. Prove-only — sound, aber findet Bugs nicht (FAIL nie möglich)

- [ ] **`NoNullDeref`** — selbst beweisbar `Null` → UNKNOWN, nie FAIL (`checks.rs:70`). **← Hebel 3**
- [ ] **`Alignment`** — echte Fehlausrichtung bleibt UNKNOWN (`checks.rs:154`).
- [ ] **`ValidPointerArith`** — Refutation abgeschaltet (`RefuteMode::Off`, reitet auf `InBounds`).

## C. Integer-UB — nur teilweise (alle nur `--bugs`)

Geprüft: Div/Mod-0, Shift-über-Breite, signed/unsigned-Overflow **nur mit `nsw`/`nuw`**. Offen:
- [ ] **plain wrapping** add/sub/mul ohne Flag — keine Obligation (`inst.rs:457`). Soundness-
  Falle: unsigned-wrap ist definiert, signed-ohne-nsw evtl. `-fwrapv`. **← Hebel 2 (nur sound-Teil)**
- [ ] **Truncation** (`size_t`→`int`) — kein dedizierter Check.
- [ ] **signed/unsigned-Verwechslung** — kein dedizierter Check.
- [ ] **Wide-Ints > 128 bit** (`i256`/`i512`) — UB-Checks komplett übersprungen (`step.rs:38`).
- [ ] **`var*var`-Allokationsgröße** (≥2 variable Faktoren) — ungeprüft (`checks.rs:333`).
- [ ] Erwägen: Integer-UB-Checks auch im strikten `verify`-Pfad (exakt-Pfad-Refutation).

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

- [ ] **Whole-program Points-to** (P4-Devirt) skaliert nicht auf Full-Kernel (naiver Andersen OOMt
  bei ~112 GB; jetzt Budget-gedeckelt zu no-op > 2 M Knoten). Ersetzen durch skalierbaren Solver
  (Worklist + Zyklen-Kollaps/HVN), damit Full-Kernel-Devirt reaktiviert.

## Doku-Diskrepanz

- [ ] `docs/exploit-taxonomy.md` behauptet „jede Klasse ●" — die ●-Marks meinen *Mechanismus
  existiert*, nicht *out-of-the-box Recall*. Zeilen-Marks an die ehrlichere „Assessment"-Sektion
  angleichen.

---

## Aktiv in Arbeit (autonom, Hebel 1–4)

1. **Inter-Thread-Data-Race** — happens-before-Pruning (sound FP-Reduktion) → §E.
2. **Integer-UB (sound-Teil)** — definite signed-Overflow/plain-wrap wo sound refutierbar → §C.
3. **`NoNullDeref` decided** — definite `Prov::Null`-Deref auf feasiblem Pfad refutieren → §B.
4. **Rust-Aliasing vervollständigen** — Reborrow-Stack-Modell erweitern → §F.
