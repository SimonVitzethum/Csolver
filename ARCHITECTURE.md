# CSolver — Architektur

> Formaler Speichersicherheits-Verifizierer für Rust (inkl. `unsafe`) auf den
> Ebenen MIR, LLVM-IR, x86-64/AArch64-Assembly und ELF.

Dieses Dokument ist die **verbindliche Architektur**. Es wird *vor* der
Implementierung einer Komponente gelesen und gepflegt. Jede Komponente
verweist auf die hier definierten Schnittstellen.

---

## 1. Ehrliche Einordnung (Scope & theoretische Grenzen)

Vollständige Speichersicherheit beliebiger Maschinenprogramme ist **nicht
entscheidbar** (Reduktion auf das Halteproblem; Rice-Theorem). CSolver kann
daher *prinzipiell* nicht für jedes Programm automatisch „PASS“ liefern. Das
ist kein Implementierungsmangel, sondern eine mathematische Grenze.

Der Anspruch von CSolver ist deshalb präzise formuliert:

1. **Soundness vor Completeness.** Ein `PASS` bedeutet: *bewiesen sicher unter
   den explizit ausgewiesenen Annahmen*. Wir geben niemals wissentlich ein
   `PASS` ohne Beweis aus. Wenn wir es nicht beweisen können, sagen wir
   `UNKNOWN` (mit offenen Beweisverpflichtungen) oder `FAIL` (mit
   Gegenbeispiel).
2. **Jede Annahme ist explizit.** FFI-Grenzen, Inline-Assembly,
   Nichtdeterminismus des Allokators, Hardware-Speicherordnung etc. erzeugen
   *named assumptions*, die im Report erscheinen. Ein Beweis ist immer relativ
   zu einer Annahmenmenge.
3. **Drei Ausgänge pro Beweisverpflichtung:** `PASS` (Beweisbaum), `FAIL`
   (Gegenbeispiel = konkretes Modell), `UNKNOWN` (verbleibende
   Verpflichtungen + Vorschlag minimaler Zusatzannotationen).

Was realistisch *vollständig* beweisbar ist: nicht-rekursive oder
struktur-rekursive Funktionen mit beschränkten Schleifen über lineare
Pointer-Arithmetik, deren Indizes durch Intervall-/Octagon-Invarianten und
SMT entschieden werden können — also ein großer Teil von realem (auch
`unsafe`) Rust-Code, der „eigentlich offensichtlich korrekt“ ist. Was *nicht*
automatisch entscheidbar ist, wird im Report mit Begründung markiert.

---

## 2. Leitidee: ein gemeinsames Memory-Safety-IR (MSIR)

Der zentrale Architekturentscheid: **alle Frontends lowern in ein einziges,
analyse-freundliches Zwischenformat — MSIR** (`csolver-ir`). Die teuren
Analysen (Abstract Interpretation, symbolische Ausführung, Beweis-Generierung)
werden **einmal** gegen MSIR geschrieben, nicht je Frontend dupliziert.

```
            ┌────────────┐  ┌────────────┐  ┌────────────┐  ┌────────────┐
  Quelle →  │ csolver-mir│  │csolver-llvm│  │ csolver-asm│  │ csolver-elf│
            │  (Rust MIR)│  │ (LLVM IR)  │  │ x86/ARM64  │  │ Loader/    │
            └─────┬──────┘  └─────┬──────┘  └─────┬──────┘  │ DWARF/Reloc│
                  │ lower         │ lower         │ lower   └─────┬──────┘
                  └───────┬───────┴───────┬───────┘               │ liefert
                          ▼               ▼                        ▼ Kontext
                    ┌───────────────────────────────────────────────────┐
                    │                MSIR  (csolver-ir)                  │
                    │  typisiertes, CFG-basiertes IR mit expliziten      │
                    │  Memory-Ops + SafetyChecks (Beweisverpflichtungen) │
                    └───────────────────────────┬───────────────────────┘
                                                │
        ┌───────────────────┬───────────────────┼───────────────────┐
        ▼                   ▼                   ▼                   ▼
 ┌────────────┐     ┌──────────────┐    ┌──────────────┐    ┌──────────────┐
 │ csolver-cfg│     │csolver-absint│    │csolver-symbol│    │csolver-memory│
 │ Dom/PostDom│     │ Domänen +    │    │ symbolische  │    │ Region/Ptr-  │
 │ Loops      │     │ Fixpunkt     │    │ Ausführung   │    │ Modell       │
 └─────┬──────┘     └──────┬───────┘    └──────┬───────┘    └──────┬───────┘
       └───────────────────┴─────────┬─────────┴───────────────────┘
                                      ▼
                            ┌───────────────────┐     ┌──────────────┐
                            │  csolver-verifier │────▶│ csolver-solver│
                            │ erzeugt & entlädt │     │ Constraint-IR │
                            │ Beweisverpflicht. │◀────│ Simplify      │
                            └─────────┬─────────┘     └──────┬───────┘
                                      │                      ▼
                                      │               ┌──────────────┐
                                      │               │ csolver-smt  │
                                      │               │ Z3/Bitwuzla/ │
                                      │               │ CVC5         │
                                      ▼               └──────────────┘
                            ┌───────────────────┐
                            │  csolver-report   │  PASS / FAIL / UNKNOWN
                            │  Beweisbaum,      │  + Beweisbaum / Gegenbsp.
                            │  Gegenbeispiel    │  + offene Verpflichtungen
                            └─────────┬─────────┘
                                      ▼
                            ┌───────────────────┐
                            │   csolver-cli     │  `solver verify ...`
                            └───────────────────┘
```

**Warum ein gemeinsames IR statt N Analysen?** (a) Soundness lässt sich an
*einer* Stelle argumentieren; (b) eine in MSIR formulierte Schleifeninvariante
gilt unabhängig von der Quellebene; (c) Querverbindungen zwischen Ebenen
(z. B. MIR-Borrow-Info als Hinweis für die LLVM-Analyse) laufen über MSIR-
Metadaten statt über Ad-hoc-Kanäle.

**Soundness des Lowerings.** Jedes Frontend muss eine *Refinement*-Eigenschaft
erfüllen: jedes konkrete Verhalten des Originals ist ein konkretes Verhalten
des MSIR (Über-Approximation der Zustände, Unter-Approximation der Garantien).
Diese Pflicht steht je Frontend in dessen `Verification/`.

---

## 3. Crate-Topologie und Abhängigkeiten

Strikt azyklische Schichtung (Pfeile = „hängt ab von“):

```
                       csolver-core   (keine internen Deps)
                          ▲   ▲   ▲
        ┌─────────────────┘   │   └──────────────────┐
   csolver-ir            csolver-memory          (genutzt von allen)
   ▲    ▲    ▲                ▲
   │    │    └── csolver-cfg  │
   │    │            ▲        │
   │    └── csolver-absint ───┤
   │            ▲             │
   │    csolver-symbolic ─────┤
   │            ▲             │
 Frontends:     │         csolver-smt ◀── csolver-solver
 mir, llvm,     │             ▲             ▲
 asm, elf       │             └─────┬───────┘
 (→ ir)         └──────────── csolver-verifier
                                    ▲
                            csolver-report
                                    ▲
                              csolver-cli
                                    ▲
                            csolver-testsuite (dev, e2e)
```

| Crate | Verantwortung | Hängt ab von |
|---|---|---|
| `csolver-core` | Verdikte, Beweisverpflichtung, Beweisbaum, IDs, Diagnostik, abstrakte Werte/Bitvektoren, `Result`/Fehler | — |
| `csolver-ir` | MSIR: Typen, Funktionen, Basic Blocks, Instruktionen, Memory-Ops, `SafetyCheck` | core |
| `csolver-cfg` | CFG-Konstruktion, Dominator-/Post-Dominator-Baum, natürliche Schleifen, SCCs | core, ir |
| `csolver-parser` | geteilte Lexer-/Parser-Infrastruktur (Tokens, Spans, Fehlerbehebung) | core |
| `csolver-mir` | Rust-MIR-Frontend → MSIR (nutzt Borrow-/Panic-Info) | core, ir, parser |
| `csolver-llvm` | LLVM-IR-Frontend → MSIR (SSA, PHI, Intrinsics, MemorySSA-Hinweise) | core, ir, parser |
| `csolver-asm` | x86-64 (Intel/AT&T) + AArch64 → MSIR | core, ir, parser |
| `csolver-elf` | ELF/PE/Mach-O-Loader, Sections, Reloc, Symbole, DWARF, PLT/GOT/TLS, Exception-Tables | core, ir |
| `csolver-memory` | symbolisches Speichermodell: Region, Pointer, Provenance, Permissions, Alignment, Lifetime | core |
| `csolver-absint` | Abstract-Interpretation-Framework + Domänen (Interval, Congruence, Octagon, …), Widening/Narrowing | core, ir, cfg, memory |
| `csolver-symbolic` | symbolische Ausführung: Path-Split/Merge, Lazy-Init, interprozedural, Summaries | core, ir, cfg, memory, solver |
| `csolver-smt` | SMT-Backend-Abstraktion + Z3/Bitwuzla/CVC5 (+ portabler interner Fallback-Solver) | core |
| `csolver-solver` | Constraint-IR, Simplifikation, Übersetzung in SMT | core, memory, smt |
| `csolver-verifier` | Orchestrierung: erzeugt Beweisverpflichtungen aus MSIR+Analysen, entlädt sie, bildet Verdikte | core, ir, cfg, memory, absint, symbolic, solver, smt |
| `csolver-report` | menschenlesbare & maschinenlesbare (JSON) Ausgabe, Beweisbaum, Gegenbeispiel | core |
| `csolver-cli` | `solver`-Binary: `verify`, `report` | alle obigen |
| `csolver-testsuite` | reale Rust-Programme mit `unsafe` als End-to-End-Fixtures | verifier, cli (dev) |

Externe Crates werden bewusst **spät** eingeführt und je Komponente in deren
`Verification/Assumptions.md` begründet (z. B. `gimli`/`object` für DWARF/ELF,
`iced-x86`/`yaxpeax` für Disassembly, `z3` für SMT). Das aktuelle Gerüst ist
absichtlich `std`-only und damit offline reproduzierbar baubar.

---

## 4. Die zentralen Schnittstellen (Verträge)

Diese Typen/Traits sind die *Verträge* zwischen Komponenten. Details in den
jeweiligen `lib.rs`-Doku-Kommentaren; hier der konzeptionelle Überblick.

### 4.1 Verdikt & Beweis (`csolver-core`)

```rust
enum Verdict { Pass, Fail, Unknown }

struct ProofObligation { id, kind: SafetyProperty, location, predicate, .. }

enum SafetyProperty {            // die Eigenschaften aus dem Auftrag
    InBounds, NoUseAfterFree, NoDoubleFree, NoDanglingDeref,
    NoNullDeref, StackIntegrity, ValidPointerArith, ValidReference,
    ValidWrite, ValidRead, NoForbiddenOverlap, Alignment,
    ValidStackFrame, ValidIndirectTarget,
}

enum ObligationResult {
    Proven(ProofTree),
    Refuted(CounterExample),
    Open(Vec<ResidualObligation>, Vec<SuggestedAssumption>),
}
```

`ProofTree`, `CounterExample`, `Assumption` sind ebenfalls in `core`, damit
*jede* Komponente Beweise im gleichen Format produziert.

### 4.2 MSIR (`csolver-ir`)

Ein typisiertes, blockbasiertes IR. Speicheroperationen sind **explizit** und
tragen die nötige Information für Beweisverpflichtungen:

```rust
enum Inst {
    Assign(Reg, RValue),
    Load  { dst: Reg, ptr: Operand, ty: Type, align: Align },
    Store { ptr: Operand, value: Operand, ty: Type, align: Align },
    Alloc { dst: Reg, region: RegionKind, size: Operand, align: Align },
    Dealloc { ptr: Operand, region: RegionKind },
    PtrOffset { dst: Reg, base: Operand, offset: Operand, elem: Type },
    Call  { .. }, Asm { .. }, Intrinsic { .. },
    SafetyCheck(SafetyProperty, Predicate),  // explizite Beweisverpflichtung
}
```

Jede `Load`/`Store`/`PtrOffset`/`Dealloc` impliziert kanonische
`SafetyCheck`s; das Frontend darf zusätzliche aus Quellinformation (Borrow,
Panic-Pfade) anhängen.

### 4.3 Frontend-Vertrag

```rust
trait Frontend {
    type Input;
    fn lower(&self, input: Self::Input) -> Result<ir::Module>;
}
```

### 4.4 Abstract-Interpretation-Vertrag (`csolver-absint`)

```rust
trait AbstractDomain: Clone + PartialEq {
    fn bottom() -> Self;  fn top() -> Self;
    fn join(&self, other: &Self) -> Self;     // ⊔
    fn meet(&self, other: &Self) -> Self;     // ⊓
    fn widen(&self, other: &Self) -> Self;    // ∇  (Terminierung)
    fn narrow(&self, other: &Self) -> Self;   // Δ  (Präzisionsrückgewinnung)
    fn leq(&self, other: &Self) -> bool;      // ⊑
}

trait TransferFunction<D: AbstractDomain> {
    fn apply(&self, inst: &ir::Inst, state: &D) -> D;
}
```

Der Fixpunkt-Iterator (Worklist + Widening an Schleifen-Headern, identifiziert
von `csolver-cfg`) ist domänen-generisch.

### 4.5 SMT-Vertrag (`csolver-smt`)

```rust
trait SmtSolver {
    fn declare(&mut self, sort: Sort) -> Term;
    fn assert(&mut self, t: Term);
    fn check(&mut self) -> SatResult;          // Sat(Model) | Unsat(UnsatCore) | Unknown
    fn push(&mut self); fn pop(&mut self);
}
```

Backends (Z3/Bitwuzla/CVC5) implementieren denselben Trait; ein portabler,
schwacher interner Bitvektor-Solver dient als Fallback und für CI ohne externe
Solver. Theorien: `BV`, `Array`, `UF`, optional `Int`/`Real`.

### 4.6 Verifizierer-Vertrag (`csolver-verifier`)

```rust
fn verify_function(f: &ir::Function, cfg: &Config) -> FunctionReport;
// FunctionReport { verdict, per_obligation: Vec<(ProofObligation, ObligationResult)> }
```

Strategie pro Verpflichtung (eskalierend, billigste zuerst):
1. **Abstract Interpretation** entlädt „offensichtliche“ Checks (Intervalle).
2. **Symbolische Ausführung + SMT** für das, was AI nicht schließt.
3. Bleibt etwas offen → `UNKNOWN` mit Residual + Vorschlag minimaler Annotation.

---

## 5. Datenfluss eines `solver verify <binary>`

1. `csolver-cli` erkennt Eingabetyp (ELF/`.ll`/`.s`/Crate) und wählt Frontend.
2. `csolver-elf` lädt ELF, liefert Sections/Symbole/Reloc/DWARF an `csolver-asm`.
3. `csolver-asm` disassembliert → MSIR; DWARF liefert Stack-Layout/Typen.
4. `csolver-cfg` baut CFG, Dominatoren, Schleifen.
5. `csolver-absint` berechnet Invarianten (Intervalle, Pointer-Domäne …).
6. `csolver-verifier` erzeugt Beweisverpflichtungen, entlädt via AI, sonst via
   `csolver-symbolic` + `csolver-solver`/`csolver-smt`.
7. `csolver-report` rendert PASS/FAIL/UNKNOWN mit Beweisbaum bzw. Gegenbeispiel.

Für `.ll`/MIR/Crate analog, nur mit anderem Frontend; ab MSIR ist der Pfad
identisch.

---

## 6. Querschnitt: Performance & Inkrementalität

- **Parallelität:** Funktionen sind die natürliche Parallelisierungseinheit
  (interprozedural via Summaries, s. u.). Worklist-Fixpunkte je Funktion.
- **Summaries:** interprozedurale Analyse nutzt zusammenfassende Pre-/
  Postconditions je Funktion (kontextsensitiv per Call-String-Bound *k*).
- **Caching/Inkrementell:** Verdikte werden über einen stabilen Hash des
  MSIR-Funktionskörpers + Konfiguration gecacht; unveränderte Funktionen
  werden nicht neu bewiesen.
- Diese Mechanismen sind in `csolver-verifier` verortet; das Gerüst legt die
  Schnittstellen an, die Implementierung folgt iterativ.

---

## 7. Verifikationsdokumentation pro Komponente

Jede Crate hat einen Ordner `Verification/` mit den Abschnitten **Design,
Spezifikation, Annahmen, Grenzen, Beweise, Teststrategie** (aktuell als ein
`Verification/README.md` mit diesen sechs Abschnitten; bei Bedarf in
Einzeldateien aufgeteilt). Dort steht insbesondere das *Soundness-Argument*
der Komponente und welche Annahmen sie in den globalen Report einbringt.

---

## 8. Roadmap (iterativ, je Stufe: Code + Tests + Doku + Verification)

- **M0 (dieser Stand):** Architektur, Workspace, `core`-Verträge, MSIR-Typen,
  `cfg`-Dominatoren, `memory`-Pointermodell, `absint`-Intervalldomäne — alles
  getestet und grün; übrige Crates als dokumentierte Interface-Stubs.
- **M1:** Vertikaler Durchstich „LLVM-IR → In-Bounds-Beweis“ für eine
  Funktion mit beschränkter Schleife (Interval-AI, ohne SMT).
- **M2:** symbolische Ausführung + interner Bitvektor-Solver; `FAIL` mit
  Gegenbeispiel.
- **M3:** Z3-Backend; Array-Theorie für Heap; Use-after-Free/Double-Free.
- **M4:** ELF+asm-Frontend (x86-64) für kleine Binaries; DWARF-Stacklayout.
- **M5:** MIR-Frontend mit Borrow-/Panic-Info; interprozedurale Summaries.

Reihenfolge nach M0 ist verhandelbar und wird mit dem Auftraggeber priorisiert.
