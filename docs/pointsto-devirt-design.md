# Design: soundes Devirtualisieren von `obj->ops->fn()` (whole-program Feld-Points-to)

**Ziel:** den heap/param-verwurzelten Kernel-Dispatch `obj->ops->fn()` sound-unbedingt
auflösen — den häufigsten indirekten-Call-Shape, den [`Phase D`](../crates/verifier/src/discharge.rs)
für konstante Globals bereits schließt. Der allgemeine Fall (`obj` ist Heap/Param) braucht mehr:
zu wissen, **welches** Global das `ops`-Feld über das ganze Programm hält.

Dies ist ein **mehr-Session-Komponentenstück** (eine whole-program Points-to-/Alias-Analyse).
Dieses Dokument ist der ausführbare Plan; es ist bewusst *nicht* am Ende einer langen Session
überstürzt implementiert (Soundness-Risiko: ein falscher Devirt ⇒ falsche Callee-Summary ⇒
false PASS/FAIL — der Kardinalfehler).

---

## 1. Warum es eine echte Alias-Analyse braucht (der Kern)

Naiv: „scanne alle typisierten Stores `store &G, gep %struct.T, obj, …, ops`; wenn alle dasselbe
`&G` schreiben ⇒ löse Loads von `T.ops` zu `G` auf." **Das ist unsound**, weil ein
*untypisierter/aliaster* Store (`store &X, some_i8_ptr`) dasselbe Feld überschreiben kann und in
der typisierten Sicht **unsichtbar** ist. Um „alle Stores auf `T.ops` sind die sichtbaren
typisierten" zu *beweisen*, braucht man eine Analyse, die für jeden Store bestimmt, welche
abstrakten Speicherorte er treffen *kann* — d. h. eine **Points-to-/Alias-Analyse**.

**Store-Vollständigkeit ist die eigentliche Beweislast, und sie ist nur closed-world sinnvoll.**

## 2. Der entscheidende Soundness-Trick: Devirt von Provenance *entkoppeln*

Ein Load `%opsp = load obj->ops` ist flow-insensitiv-mehrdeutig mit *uninitialisiert* (das Feld
könnte vor dem ersten Store gelesen werden). Würde man `%opsp` als valide Region von `G_ops`
materialisieren, maskierte man einen möglichen Null-/Uninit-Deref (false PASS).

**Lösung:** Points-to nur für die **Call-Ziel-Auflösung** nutzen, *nicht* für Provenance/Sicherheit.
- `%opsp` behält seine opake Provenance ⇒ die Null-/Uninit-/Bounds-Checks auf `load %opsp->fn`
  bleiben unverändert (sound; ein uninit-Feld refutiert weiterhin).
- Separat: die Analyse weiß „`%opsp` zeigt-auf-Menge = {G_ops}" (Singleton). Ein
  `%fn = load %opsp + fn_offset` löst den *Wert* `%fn` zu `global_fn_ptrs[G_ops][fn_offset]` auf,
  und der Call devirtualisiert — **ohne** `%opsp`s Provenance anzufassen.

So verbessert Devirt nur die *Callee-Effekt-Präzision* des Calls, nie die Speicher-Sicherheit des
Loads. Kein Uninit-Masking. (Falls `%opsp` doch null wäre, faultet der Load zuerst — der
Call-Ziel-Wert ist dann irrelevant.)

Aber: die Auflösung `{G_ops}` selbst muss **exakt** sein — ein *falsches* `G_ops` ⇒ falsche
Summary ⇒ unsound. Darum bleibt Store-Vollständigkeit (§1) Pflicht. Ein Singleton-*Über*-
Approximations-Ergebnis ist exakt (die Menge enthält das echte Ziel und hat Größe 1), also
sound auflösbar; jede unklassifizierbare (may-alias) Store „vergiftet" das Feld ⇒ nicht auflösbar.

## 3. Die Analyse (feld-sensitives Andersen, flow-insensitiv)

**Abstrakte Orte:** Globals, Allokationssites (Heap), Stack-Allocas, plus **Felder** davon
(feld-sensitiv: `loc.offset`, nur konstante, typ-abgeleitete Offsets).

**Constraints (aus MSIR/LLVM, closed-world):**
- `p = &x` ⇒ `x ∈ pts(p)`
- `p = q` / `p = cast q` ⇒ `pts(q) ⊆ pts(p)`
- `p = gep %struct.T, q, …, off` ⇒ `pts(p) ⊇ { x.off : x ∈ pts(q) }`
- `p = load q` ⇒ `∀ x ∈ pts(q): pts(x) ⊆ pts(p)`
- `store v, q` ⇒ `∀ x ∈ pts(q): pts(v) ⊆ pts(x)`  ← die Store-Verteilung, die Vollständigkeit erzwingt
- **Unbekannter Store** (`q` untypisiert / `pts(q)` = ⊤ / inline-asm / opaker Call, der schreibt)
  ⇒ jedes Feld, das `q` treffen könnte, wird ⊤ (vergiftet). Konservativ = sound.

**Lösen** zum Fixpunkt (worklist, subset-propagation). Feld-Sensitivität hält `T.ops` getrennt
von `T.other`. Ergebnis: `pts(T-instance.ops)`; ist es ein **Singleton-Global** `{G_ops}` und nicht
vergiftet ⇒ `field_target[(T, ops_off)] = G_ops`.

**Aufwand:** groß (Andersen mit Feld-Sensitivität, ~mehrere hundert Zeilen + Tuning für
Kernel-Größe; whole-program über den Streaming-Facts-Pfad wie A2). Klassisch, aber real.

## 4. Integration (call-resolution-only)

- Neue Analyse-Ausgabe: `reg_devirt_points_to: HashMap<(FuncId, RegId), String>` — Register →
  das eindeutige Global, auf das es (über Feld-Points-to) zeigt.
- Executor: eine **Seiten-Annotation** (analog `state.fn_ptrs`), die *nur* die
  `load %opsp->fn`-Devirt speist — Provenance/Sicherheit unberührt (§2).
- Wiederverwendet die bestehende `global_fn_ptrs`-Tabellen-Devirt für den zweiten Hop.
- **Gate:** `--closed-world` (Store-Vollständigkeit) + benannte Assumption `closed-world-devirt`
  im Proof-Tree.

## 5. Soundness-Disziplin

1. Die Points-to ist eine **Über**-Approximation; nur **Singleton**-Felder werden aufgelöst
   (Singleton-Über-Approx = exakt). Jeder unklassifizierbare Store vergiftet ⇒ konservativ.
2. Devirt entkoppelt von Provenance (§2) ⇒ kein Uninit-/Null-Masking.
3. Beide Orakel SOUND, volle Testsuite, clippy — plus ein **Devirt-Differential**: ein
   Testkorpus mit bewusst *mehrdeutigen* ops-Feldern (zwei verschiedene Globals) muss
   **nicht** auflösen (Poison), ein eindeutiges muss.
4. Nur unter `--closed-world`; ohne das Flag unverändert.

## 6. Phasen (fokussierte Folge-Tasks)

1. **P1 — Points-to-Kern:** die Constraint-Sammlung + der Worklist-Solver als neues Modul
   (`crates/absint/src/pointsto.rs` o. ä.), feld-sensitiv, mit ⊤-Vergiftung. Unit-getestet
   isoliert (Constraints → pts).
2. **P2 — Feld-Ziel-Extraktion:** `field_target[(T, off)]` aus dem pts-Ergebnis; Singleton-Regel.
3. **P3 — whole-program (Streaming):** über den Facts-Pfad wie A2/Phase D, damit der Scan profitiert.
4. **P4 — Executor-Integration:** `reg_devirt_points_to` + Seiten-Annotation für die
   Call-Auflösung; `--closed-world`-Gate; Assumption.
5. **P5 — Validierung:** Orakel + Devirt-Differential + `mm`/af_alg-Messung.

**Verdikt:** sound machbar, aber es ist die whole-program Points-to-Analyse als eigene Komponente
(P1–P5), nicht ein fokussierter Patch. Der Entkopplungs-Trick (§2) ist der Schlüssel, der es
*sound* macht ohne Flow-Sensitivität; die Store-Vollständigkeit (§1) ist die Kern-Arbeit.
