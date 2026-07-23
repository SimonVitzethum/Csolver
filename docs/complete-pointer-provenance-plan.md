# Plan: vollständige Zeiger-Provenance (Roadmap Phase A, ausführbar)

**Ziel:** die Zeiger-Provenance so weit vervollständigen, dass der mit Abstand größte UNKNOWN-Block
verschwindet. **~89 % aller Kernel-UNKNOWNs sind Provenance** — direkt (ein Zeiger ohne bekannte
Herkunft) oder *Folge* davon (non-null, in-object, in-bounds, alignment lösen sich, sobald die
Herkunft steht). Der Hebel ist eindeutig; dieses Dokument macht ihn ausführbar.

**Kardinalregel (unverändert):** nie ein false PASS. Jede Provenance-Recovery, die im Allgemeinen
unsound ist, läuft hinter einer **benannten Annahme** (`--assume-valid-params` / `--closed-world` /
neue `--assume-*`), im Proof-Tree sichtbar; die Orakel (Miri + C-ASan/UBSan) testen jedes Bündel mit.

---

## 1. Das Modell heute (verankert)

Es gibt **zwei** Provenance-Typen — nur einer ist live:
- `csolver_memory::pointer::Provenance` (crates/memory/src/pointer.rs:13) — **Altlast/parallel**, vom
  Exec-Engine nicht benutzt. Nicht anfassen.
- **`csolver_symbolic::exec::value::Prov`** (crates/symbolic/src/exec/value.rs:22) — der lebendige:
  `Null | Region(usize) | Select{…} | Unknown(POrigin, Option<u32>)`. Ein `SymValue::Ptr` trägt einen
  `SymPointer { prov, offset, align, borrow }` (value.rs:139). `Region(i)` indiziert
  `PathState.regions`; `Unknown(POrigin, id)` ist ein **opaker** Zeiger mit Herkunfts-Tag `POrigin`
  (value.rs:50: `Param|Call|Load|IntToPtr|Loop|…|ScalarAsPtr(ScalarPtrCause)`) und einer nur fürs
  Aliasing genutzten Identität.

**Der geladene Zeiger (`Inst::Load` eines ptr-Feldes) ist per Default opak** — `POrigin::Load`
(loadrec.rs:25/61/65 → merge.rs:25 `fresh_value`). Er bekommt **nur** über drei Pfade echte Provenance:
1. **Store→Load-Forwarding** (`Must`-Alias im Store-Log, loadrec.rs:24) — der einzige Pfad, auf dem
   ein zuvor gespeicherter `Prov` überlebt. Speist auch die Member-Provenance (§4).
2. **`RefWitness`** (step_mem.rs:8) — das Frontend hat den Load als gültige Referenz getypt (DWARF/
   getypte Nutzung); materialisiert eine Region. Raw-Pointer-Feld nur unter `--assume-valid-params`.
3. **`size_hinted_pointer`** (calls.rs:563, gerufen an step.rs:296) — `reg_ptr_hints[dst]` + `avp`
   ⇒ ersetzt den opaken Zeiger durch eine dimensionierte `assumed`-Region.

**Rückgabe-Provenance** = `RetSummary` (summary.rs:90): `Unknown | Scalar | PtrFromArg | DanglingStack
| Alloc | ValidRef`. Produziert aus dem `AbsVal`-Lattice (perfn.rs:440), konsumiert am Call-Site
(calls.rs:409). Ein Load-Return fällt heute in `Opaque ⟶ Unknown` (perfn.rs:392) ⟶ „opaque call result".

**Cause-Taxonomie** = `POrigin::residual` (value.rs:88) + `ScalarPtrCause::residual` (classify.rs:66),
emittiert in checks.rs:70/72/217. Ein neuer Messbucket = eine neue `POrigin`/`ScalarPtrCause`-Variante.

**Contract-Fixpunkt** (contracts/ptr.rs:33, streaming facts.rs) synthetisiert **caller→callee**: er
liest die (vollständigen) Call-Sites, um die *schwächste* Param-Precondition des Callees abzuleiten;
Transitivität per Runden-Layering (`prior`). A2 (teilweise erledigt) erdet eine Call-Site zusätzlich
aus dem **getypten** Argument-Hint (`hint_guarantee`, contracts.rs:95), nicht nur aus `alloca`.

---

## 2. Root-Cause vs. Folge — worauf zielen

| Klasse | ~Residuen | Art | Ziel-Phase |
|---|---|---|---|
| loaded value (kein store-load) | **3601** | **root** | P1 |
| uncontracted pointer parameter | **1990** | **root** | P2 |
| scalar-as-ptr (intrinsic/asm/tief) | **1036** | **root** | P3 |
| int-to-pointer (untyped) | **851** | **root** | P3 |
| non-null / opaque provenance | 1887 | Folge | — (kaskadiert) |
| in-object (valid-ptr-arith) | 1289 | Folge | — |
| in-bounds (access in allocation) | 1103 | Folge | — |
| alignment | 892 | Folge | — |
| null / integer-derived | 594 | Folge | — |

**~5764 Folge-Residuen** (non-null/in-object/in-bounds/alignment/null) sind in checks.rs an dieselbe
Region-Prüfung gegated: sobald der Zeiger eine `Prov::Region` mit Größe/Align trägt, PROVEn sie
**ohne eigene Arbeit**. Deshalb zielt der Plan ausschließlich auf die **4 Root-Klassen** (7478
Residuen direkt, ~5764 kaskadierend = ~13k = die Masse).

---

## 3. Der vereinheitlichende Kern: eine whole-program **Feld-Typ-Karte** (closed-world)

Die Einzelmaßnahmen unten teilen *einen* Mechanismus — das direkte Analogon zum gerade gebauten
Points-to-Devirt: eine **streaming whole-program Karte `(struct-Typ, byte-offset) → Pointee-Typ/Größe`**,
gefüllt aus *jedem* im Programm sichtbaren Beweis für den Feldtyp:
- DWARF-Member-Typ (heute, slices.rs:82 — bricht bei `void*`/`union`),
- **der Typ, den *irgendein* Caller in dieses Feld schreibt** (`store &T, obj->f` closed-world),
- der Typ, mit dem *irgendeine* Funktion das Feld nach dem Load benutzt (getyptes gep auf dem
  Load-Ergebnis, slices.rs:192).

Ein `void *private_data`, das der Treiber-Init mit `&struct foo_priv` belegt, wird so **überall**
als `struct foo_priv *` getypt — genau die closed-world Store-Vollständigkeit, die schon die
Member-Provenance (§4) und den Devirt tragen. Gebaut als vierter Streaming-Builder in
`WholeProgramFacts` (crates/verifier/src/wholeprog.rs), `push_module`/`merge`/`finalize` wie die
anderen, name-/typ-gekeyed, konsumiert via `WholeProgramContext`. **Soundness:** ein Feld wird nur
getypt, wenn alle sichtbaren Schreiber *denselben* Typ (oder subtyp-kompatibel) schreiben; uneinige
oder unbekannt-beschriebene Felder bleiben untypisiert (⊤, wie die Poison-Regel im Points-to). Gate
`--closed-world`; benannte Assumption `closed-world-field-type`.

Diese Karte speist alle vier Root-Phasen. Sie ist das größte Einzelstück (mehrere hundert Zeilen +
Merge + Oracle), aber sie schließt `void*`/`union`/`private_data` — den harten Kern von P1.

---

## 4. P1 — Loaded-Value-Vollständigung (~3601 + Kaskade)

**P1a — `RetSummary::Field { arg, offset, pointee }`** (Feld-Accessor-Return beliebigen Offsets).
Heute ist nur `ValidRef` (RefWitness-getyptes Feld) interproc.; ein `return obj->f` mit Offset ≠ 0
oder ohne RefWitness fällt zu `Opaque`. Ausbau (Extension-Points aus der Architektur-Karte):
- `AbsVal::FieldOf { arg, offset, pointee }` erzeugen, wenn der Return-Reg ein Load von einem
  param-verwurzelten Zeiger bei konstantem Offset ist (perfn.rs:392, heute `other ⟶ Opaque`).
- in `ret_of_fn` mappen (perfn.rs:440), am Call-Site konsumieren (calls.rs:409): `argvals[arg]`
  offsetten und — wie `PtrFromArg` + `ValidRef` — entweder den geforwardeten Store-Wert oder eine
  `pointee`-dimensionierte Ref-Region liefern. **Nicht** `composes_through_wrapper` (arg-abhängig).
- Pointee-Typ aus der Feld-Typ-Karte (§3), sonst DWARF. Gate `--assume-valid-params`.

**P1b — untypisierte Felder (`void*`/`union`/`private_data`) via §3.** Der eigentliche Rest von 3601.
`size_hinted_pointer` (calls.rs:569) bricht heute ab, weil `reg_ptr_hints[dst]` fehlt. Die Feld-Typ-
Karte liefert den Hint aus dem closed-world Store; damit greift der bestehende `size_hinted_pointer`-
Pfad unverändert. **Kein Executor-Umbau — nur die Hint-Quelle wird whole-program.**

**P1c — transitive DWARF-Ketten `a->b->c->d`.** Bereits unbegrenzt (single-pass, slices.rs:111), bricht
nur an untypisierten Zwischengliedern — die §3 typisiert. P1c ist damit ein Nebenprodukt von P1b.

**Aufwand:** groß (P1a IR+executor; P1b = §3). **Hebel: −geschätzt 25–30 pp** (die größte Einzelklasse
+ ihre Kaskade).

---

## 5. P2 — Uncontracted Pointer Parameter (~1990 + Kaskade)

Heute synthetisiert der Fixpunkt eine Param-Precondition nur, wenn **alle** Call-Sites sie hergeben
(ptr.rs:88). Zwei Ausbauten:

**P2a — closed-world „alle Raw-Pointer-Params schließen".** Für C/C++ validiert
([[closed-world-member-provenance]]); auf **Rust/Kernel** ausweiten: unter `--closed-world` bekommt
jeder noch unkontrahierte Raw-Pointer-Param die schwächste Caller-Garantie; ohne sichtbaren Caller
(Entry) bleibt er adversarial. Das ist die Kern-1990-Schließung.

**P2b — caller-gerichteter Precondition-Push.** Heute reicht eine Callee-Precondition **nicht** an
einen Caller-UNKNOWN zurück. Neuer Pass nach Fixpunkt-Konvergenz: für jedes `Call(g, args)` die
`param_contracts[(g,i)]` auf `args[i]`s Register mappen und wie ein `FieldContract` seeden
(neuer Seeding-Arm neben driver.rs:416). So erbt das Caller-Argument eine Region, weil der Callee
beweist, dass es gültig sein *muss* (closed-world: der Callee dereferenziert es unbedingt). Nutzt die
bestehende `local_defs`/`reconstruct_defs`-Maschinerie (fields.rs:200). Gate `--closed-world`.

**Aufwand:** mittel (Fixpunkt + ein Seeding-Arm). **Hebel: −geschätzt 8–10 pp.**

---

## 6. P3 — scalar-as-ptr + int-to-pointer (~1036 + 851 + Kaskade)

**P3a — `inttoptr`-Typisierung** (per-cpu/`__phys`/`container_of`/`this_cpu_ptr`). Heute untyped ⟶
`POrigin::IntToPtr` opak (eval.rs). Wo die Herkunft ein bekanntes Kernel-Idiom ist (Adresse = Base +
konstanter/typisierter Offset), die Ziel-Region aus der Basis-Provenance ableiten. Teilweise via
`size_hinted` schon getypt (Memory); Rest = Idiom-Contracts (`--assume-kernel-idioms`).

**P3b — Scalar-Copy-Chain-Provenance.** `classify_scalar_ptr_defs` (classify.rs:280) klassifiziert
bereits die Kette; wo die Wurzel ein getypter Zeiger ist (`PtrToInt` → arithmetik → `IntToPtr`
zurück, das `container_of`-Muster), die Provenance durch die Kette *erhalten* statt am `ptrtoint` zu
verlieren. Sound: bit-identische Round-Trip-Adresse.

**P3c — inline-asm-Ausgänge via Contracts** ([[asm-integration-effort]], [[contract-externalization]]):
ein `asm`-Block, der einen getypten Zeiger liefert (`this_cpu_read`, `current`), bekommt einen
Effekt-Contract „returns valid `T*`" statt `ScalarAsPtr` opak.

**Aufwand:** mittel–groß (Idiom-Contracts + Ketten-Erhaltung). **Hebel: −geschätzt 6–8 pp.**

---

## 7. P4 — Downstream-Kaskade (automatisch, ~5764 Residuen)

Kein eigener Code: non-null (1887), in-object (1289), in-bounds (1103), alignment (892), null (594)
sind in checks.rs:72 an `p.prov` non-Region gegated. Sobald P1–P3 dem Zeiger eine `Prov::Region` mit
Größe/Align geben, PROVEn sie. **Der Multiplikator, der Phase A groß macht.** Einzige Pflicht: die
Regionen tragen `assumed`/`contract` korrekt (kein false PASS — eine `assumed`-Region refutiert nicht,
sie prooft nur), exakt wie die bestehende `size_hinted`/FieldContract-Disziplin.

---

## 8. Soundness-Disziplin (jede Phase, unverhandelbar)

1. **Vor Merge:** Miri + C-ASan/UBSan Orakel SOUND (0 false PASS/FAIL), volle Testsuite, clippy.
2. **Jede unsound-im-Allgemeinen Recovery** hinter benannter Assumption (`param-valid`,
   `closed-world-*`, `kernel-idioms`), im Proof-Tree; **Differential testet das Bündel** (ein Bündel,
   das einen UB-Fall zu PASS macht, ist ein Bug im Bündel).
3. **Die Feld-Typ-Karte (§3)** typisiert ein Feld nur bei einiger Schreiber-Übereinstimmung; uneinige/
   unbekannt-beschriebene Felder bleiben ⊤ (die Poison-Regel des Points-to, dieselbe Beweislast).
4. **Kaskade darf nicht maskieren:** eine `assumed`-Region ist prove-only; ein genuiner OOB/UAF über
   sie refutiert weiterhin auf exaktem Pfad (bug-finding-Modus unverändert).
5. **Messung pro Phase:** frischer kernelweiter closed-world Scan (Checkpoint, kein harter Timeout,
   [[no-hard-timeouts]]), **decided auf Funktionsebene**, plus ein **Residual-Histogramm nach
   `POrigin`/`ScalarPtrCause`** (welche Root-Klasse blieb) — der einzige interpretierbare Fortschritt.

---

## 9. Phasen & ehrliche Decke

| Nach | UNKNOWN (Schätzung) | Rest ist… | Soundness |
|---|---|---|---|
| heute (P4-Devirt gemessen: TBD) | ~50–70 % | Provenance | — |
| §3 Feld-Typ-Karte + P1 | ~25–30 % | uncontracted params | größtenteils `--closed-world`/`avp` |
| P2 params | ~18–22 % | scalar/int-ptr | `--closed-world` |
| P3 scalar/int-ptr | ~12–15 % | Loops/Frontend/Idiome | teils `--assume-kernel-idioms` |

**Strikt-sound-decided** (ohne jede Annahme) bleibt bei **~88–93 %** — die letzten Prozente sind
prinzipiell die benannte Annahmen-Schicht, nicht Analyse-Präzision (siehe
[[unknown-under-3pct-roadmap]] Phase F). Dieser Plan schließt die **Provenance-Masse** darüber; er
bringt UNKNOWN realistisch von ~50 % auf ~12–15 %, **unter benannten, auditierbaren Annahmen**.

## 10. Reihenfolge nach Hebel × Machbarkeit

1. **§3 Feld-Typ-Karte zuerst** — sie ist der gemeinsame Mechanismus von P1b/P1c/P2b und schließt den
   harten `void*`/`union`-Kern; ohne sie deckelt sich P1 selbst.
2. **P1a `RetSummary::Field`** parallel (unabhängige Executor-Arbeit, klarer Extension-Point).
3. **P2** (Fixpunkt-Ausbau) danach — nutzt §3.
4. **P3** (Idiome/Ketten) parallelisierbar, monoton.
5. **P4** fällt automatisch mit 1–3.

**Verankerte Extension-Points** (aus der Architektur-Karte, für die Umsetzung):
loaded default loadrec.rs:25 + merge.rs:25 · RetSummary summary.rs:90 / perfn.rs:392,440 /
calls.rs:409 · Feld-Seeding driver.rs:416 · Hint/DWARF slices.rs:82-205 / debuginfo.rs:208-332 ·
Cause-Taxonomie value.rs:88-115 / classify.rs / checks.rs:70-227 · Contract-Fixpunkt ptr.rs:13-131 /
facts.rs / fieldsyn.rs · whole-program Facts wholeprog.rs (WholeProgramFacts/Context).
