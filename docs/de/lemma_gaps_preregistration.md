# Vorab-Festlegung: das Lückenexperiment

Geschrieben, **bevor** irgendein Modell eine Lücke gesehen hat. Der Datensatz
ist gebaut; angesehen wurden nur Ausschlusszahlen, drei Stichproben zur
Kontrolle des Schnittpunkts und die Verteilung der menschlichen Wahl.

## Warum ein zweites Experiment

Der erste Test (16 gepaarte IMO-Aufgaben) war unentschieden: D = +0,42,
p = 0,18, nötig wären ~175 Paare gewesen. Die Zitationsstudie von Algaba u. a.
(NAACL Findings 2025) zeigt einen Ausweg: nicht ganze Lösungen vergleichen,
sondern einzelne Stellen maskieren und das Modell dieselbe Stelle füllen
lassen. Jede Stelle ist ein perfekt gepaartes Datum.

## Hypothese

**H1.** An einer Stelle, an der ein Mensch in einem mathlib-Beweis ein Lemma
benannt hat, wählt ein KI-Beweiser — bei identischem vorangehendem Text — ein
Lemma, das in mathlib häufiger explizit benutzt wird.

**H0.** Kein Unterschied.

## Daten

- **1.000 Lücken** aus 1.000 verschiedenen Theoremen, die erst **nach dem
  1. August 2026** in mathlib kamen (nicht in den Schnitten 2026-07 und
  2026-08, nicht in MathlibGraph vom Feb 2026, nicht in LeanDojo v2/v3). Damit
  liegen sie nach dem Trainingsstichtag jedes Probanden; kein Modell kann den
  menschlichen Beweis gesehen haben.
- **Umbenennungsfilter:** 166 Theoreme ausgeschlossen, deren Aussage (ohne
  Namen) schon im mathlib-Baum vom 2026-08-01 stand.
- **Pro Theorem eine Lücke:** ein zufällig gewähltes (Seed 0) benanntes Lemma,
  an seinem ersten Vorkommen im Beweis. Das Lemma muss in LeanDojo v2
  (Mai 2025) existieren — ein Lemma, das der Proband nicht kennen kann, wäre
  ein unfairer Vergleich.
- **Präfix:** `import Mathlib`, die `open`- und `namespace`-Zeilen der
  Deklaration, Aussage, Beweis bis unmittelbar vor das Lemma. Kommentare
  entfernt. `variable`-Zeilen fehlen (Einschränkung, gilt für alle Lücken
  gleich).

## Probanden

**Primär: DeepSeek-Prover-V2-7B** (`mlx-community/DeepSeek-Prover-V2-7B-4bit`),
lokal auf dem Mac des Nutzers. Derselbe Beweiser wie im ersten Test, damit die
Ergebnisse zusammen lesbar sind.

Optional: Goedel-Prover-V2-8B. Wird er gerechnet, dann mit identischem Verfahren
und getrennt berichtet.

## Verfahren

- **Reine Textfortsetzung** des Präfixes, kein Chat-Template, kein
  Anweisungstext. So entsteht die Wahl genau so, wie beim Schreiben eines
  Beweises von links nach rechts.
- **Greedy-Dekodierung** (Temperatur 0), höchstens 32 neue Token.
- **Die Wahl des Modells** = der erste Bezeichner der Fortsetzung, aufgelöst
  mit denselben Regeln wie die menschliche Wahl (voller Name oder über die
  geöffneten Namespaces).

Jede Fortsetzung fällt in genau eine Kategorie:

| Kategorie | Bedeutung |
|---|---|
| **gleich** | dasselbe Lemma wie der Mensch |
| **anderes Lemma** | ein existierendes theorem, aber ein anderes |
| **kein Lemma** | Taktik, lokale Hypothese, Schlüsselwort, Klammer |
| **erfunden** | sieht aus wie ein Lemmaname, existiert nicht |

Die Auflösung macht nicht das Skript auf dem Mac, sondern die Auswertung
hier — dasselbe Programm für alle Probanden.

## Primärmetrik

Popularität = **explizite Nutzungshäufigkeit in LeanDojo v2** (Mai 2025,
541.841 nachverfolgte Verwendungen). Grund: das misst, wie oft ein Modell ein
Lemma im Text gesehen haben kann, und — anders als MathlibGraph — enthält es
die additiven `@[to_additive]`-Lemmas, die ein Viertel der menschlichen Wahlen
ausmachen.

Pro Lücke *s* mit Kategorie **gleich** oder **anderes Lemma**:

> Dₛ = log(1 + Nutzung(Wahl des Modells)) − log(1 + Nutzung(Wahl des Menschen))

**Primärtest:** Mittelwert von D über alle diese Lücken (Übereinstimmungen
zählen als 0) gegen 0, Vorzeichen-Permutationstest, 10.000 Ziehungen,
zweiseitig, α = 0,05.

**Bedeutsam** ab |mittleres D| ≥ 0,25 (Faktor ~1,3). Signifikant, aber
darunter: „messbar, aber klein".

## Sekundärmetriken

1. **Nur Abweichungen** (Kategorie *anderes Lemma*): wenn das Modell etwas
   anderes wählt als der Mensch — wählt es Populäreres? Das ist die schärfere
   Frage nach einer Vorliebe.
2. **Gesamter Eingangsgrad in MathlibGraph** statt expliziter Nutzung, nur für
   Lücken, in denen beide Lemmas dort vorkommen. Prüft den Hinweis aus dem
   ersten Test (Effekt stärker beim Gesamt- als beim expliziten Grad).
3. **Kategorienanteile**, insbesondere wie oft das Modell an einer Stelle, an
   der der Mensch ein Lemma benannt hat, gar keines benennt.
4. **Vergleichsanker:** exp(mittleres D) als Faktor, neben dem Faktor 6–7 der
   Zitationsstudie.

## Explorativ: Stufe 2, Lean-Prüfung

Nur falls gerechnet: in jeder Lücke der Kategorie *anderes Lemma* wird die
Wahl des Modells an die Stelle der menschlichen gesetzt und die Datei mit
Lean geprüft. Frage: funktionieren die populäreren Wahlen? Ist D unter den
funktionierenden Wahlen kleiner als unter den scheiternden, würde formale
Verifikation die Homogenisierung bremsen. Das ist ausdrücklich explorativ.

## Bekannte Verzerrungen, vorab benannt

- **Erfundene Namen fallen aus D heraus.** Erfindet das Modell eher bei
  schwierigen Stellen, bleiben leichtere übrig — das drückt D eher nach
  unten. Der Test ist in dieser Hinsicht konservativ.
- **Nichtwissen vs. Vorliebe.** Ohne Lean-Prüfung ist nicht zu trennen, ob
  das Modell ein populäres Lemma *vorzieht* oder das passende seltene *nicht
  kennt*. Beides ist für die Wirkung auf eine Bibliothek gleich; für den
  Mechanismus nicht. Stufe 2 trennt das teilweise.
- **Das Präfix endet vor dem Namen, nicht vor der Taktik.** Das Modell sieht
  also schon, dass hier ein Term erwartet wird (etwa nach `rw [`). Das gilt
  für jede Lücke gleich.

## Abbruchkriterium

Fallen weniger als 200 Lücken in die Kategorien *gleich* oder
*anderes Lemma*, ist H1 mit diesem Probanden nicht prüfbar und wird so
berichtet.

---

## Abweichungen vom Plan

**L1 — Datensatz neu gebaut, bevor ein Modell lief.** Ein Probelauf des
Generierungsskripts mit einem Attrappen-Modell zeigte in Lücke 0 ein Präfix,
das in eine `@[deprecated] alias`-Zeile hinter dem Theorem hineinlief. Zwei
Fehler, beide behoben:

1. Der Quelltextbereich einer Deklaration reichte bis in die folgende Zeile.
   Jetzt endet der Beweis an der ersten Zeile, die in Spalte 0 beginnt.
2. Ein veralteter Alias, der auf ein Theorem zeigt, beweist, dass das Theorem
   ein neuer Name für ein altes Lemma ist — der Aussagefilter hatte solche
   Fälle übersehen, wenn sich die Aussage leicht verändert hatte. Neuer
   Filter: fliegt raus, wenn in derselben Datei ein `@[deprecated]`-Alias oder
   `@[deprecated <Name>]` darauf verweist.

Neue Ausschlusszahlen: **401** Umbenennungen über den Alias-Filter, **54**
weitere über den Aussagefilter (vorher insgesamt 166). Brauchbar 2.779 Lücken,
davon 1.000 gezogen (Seed 0), 501 Module. Menschliche Wahl: explizite Nutzung
Median 23, additive Zwillinge 24,8 %. Nachgeprüft über **alle** 1.000 Lücken:
kein Präfix enthält `alias`/`deprecated`, keines eine Spalte-0-Zeile nach dem
Kopf.

**L2 — Beweismethoden ausgeschlossen, bevor ein Modell lief.** Beim Schreiben
der Auswertung fiel auf: 238 der 1.000 Lücken waren keine Wahl zwischen
Lemmas, sondern Beweismethoden — `rfl` (181), `ext` (33), `Iff.rfl` (10),
`congr` (7) u. a. Solche Namen sind in Lean zugleich Taktik oder generischer
Reflexivitätsterm. Sie hätten massenhaft triviale Übereinstimmungen erzeugt
und jeden Effekt verdünnt. Diese Namen (Liste `PROOF_METHOD` in
`build_slots.py`) sind jetzt keine Kandidaten mehr; bei betroffenen Theoremen
wird zufällig unter den übrigen Lemmas gewählt. Dieselbe Liste gilt in der
Auswertung: schreibt das Modell einen dieser Namen, fällt die Lücke in
*kein Lemma*.

Neuer Stand: 2.154 brauchbare Lücken, 1.000 gezogen, 475 Module. Menschliche
Wahl: explizite Nutzung **Median 9**; nicht in MathlibGraph **9,0 %**.

**Korrektur zu L1:** Der dort genannte Anteil von 24,8 % „additiven
Zwillingen" war falsch gedeutet. Er bestand größtenteils aus `rfl`, das als
Kern-Deklaration ebenfalls nicht in MathlibGraph steht. Der echte Anteil
fehlender Lemmas liegt bei 9 %.

**L3 — Lauf 1 verworfen: Tokenisierungsfehler, entdeckt vor jeder
Auswertung.** Bei der Vollständigkeitsprüfung der Rohdaten fiel auf, dass die
Fortsetzungen kaum Leerzeichen enthielten (Median 1,4 % der Zeichen, im
Präfix 16,7 %). Das Modell schrieb etwa
`theoremalgebra_eq:_=algebraOfLiesOvervw:=` — es kopierte das Präfix ohne
Leerzeichen und ohne `‹ ›`.

Ursache, im Quelltext nachvollzogen: mlx-lm 0.31.3 verlangt transformers ≥ 5.
transformers 5 baut Tokenizer der Klasse `LlamaTokenizerFast` nach eigenem
Muster (Metaspace-Vortokenisierung) und übernimmt aus `tokenizer.json` nur
Vokabular und Merges. DeepSeek-Prover meldet genau diese Klasse, hat aber ein
Byte-Level-Vokabular. Alles, was dieses Vokabular nur in Byte-Form kennt —
Leerzeichen, Zeilenumbrüche, jedes Nicht-ASCII-Zeichen wie ∀ → ⟨ ⟩ ℝ —, fiel
im Prompt ohne Fehlermeldung weg. Die Ausgabe wurde richtig dekodiert; der
Fehler war nur an den Fortsetzungen zu erkennen.

Angesehen wurden: Zeilenzahl, Leerzeichenanteile, Präfixende und Fortsetzung
von etwa 15 Lücken zur Diagnose. **Nicht** berechnet: Kategorien, D oder
irgendein Vergleich mit der menschlichen Wahl. Lauf 1 liegt unverändert in
`ungueltig_lauf1/` und wird nicht ausgewertet.

**Lauf 2** folgt demselben Verfahren. Die Prompt-Token kommen jetzt direkt aus
der `tokenizer.json` des Modells (Bibliothek `tokenizers`), mit vorangestelltem
BOS; die Ausgabe wird mit demselben Tokenizer dekodiert. Neu ist ein
**Selbsttest vor dem Laden des Modells**: Für alle 1.000 Präfixe muss
decode(encode(p)) = p gelten, sonst bricht das Skript ohne Generierung ab. Als
Beleg der Diagnose rechnet es die Tokenisierung von Lauf 1 nach und vergleicht
die Promptlängen. mlx-lm ist auf 0.31.3 festgelegt, die Version, deren
Quelltext geprüft wurde. Zusätzlich gespeichert, explorativ und nicht Teil der
Hypothesenprüfung: erzeugte Token-IDs, deren Log-Wahrscheinlichkeiten und die
fünf wahrscheinlichsten Token im ersten Schritt.

---

## Stufe 2 — festgelegt nach Lauf 2, vor der Lean-Prüfung

Explorativ, wie oben angekündigt. Geschrieben, nachdem die Ergebnisse von
Stufe 1 vorlagen, aber bevor Lean eine einzige Ersatzwahl geprüft hat.

**Umfang:** alle 305 Lücken der Kategorie *anderes Lemma*. Mathlib genau in
der Fassung, aus der die Lücken stammen (`d0a050ad6`), mit mathlibs eigenen
Optionen (`maxSynthPendingDepth=3`, `autoImplicit=false`). Die Datei wird
hinter dem Theorem abgeschnitten.

**Variante S (Ersatz):** Der Name, den der Mensch schrieb, wird durch die
Wahl des Modells ersetzt: führende `←` oder `@` der Fortsetzung plus der
Name, wie das Modell ihn schrieb. Der Rest des Beweises bleibt der des
Menschen. Gemessen wird also, ob die Wahl an genau dieser Stelle trägt.
Nicht gemessen wird, ob das Modell mit ihr einen anderen Beweis hätte führen
können.

**Kontrolle D (129 Lücken in simp/grind-Hinweislisten):** Das Listenelement
wird ganz gestrichen. Klappt der Beweis auch ohne den Hinweis, sagt ein
erfolgreicher Ersatz nichts über die Wahl des Modells.

**Kontext** je Lücke: Hinweisliste (129), rw-Liste (111), Term/Argument (65).

**Auswertung, vorab festgelegt:**
1. Anteil S = ok, gesamt und je Kontext. Bei Hinweislisten nur dort, wo
   D scheitert (der Hinweis war nötig).
2. D-Wert (Popularität aus Stufe 1) der tragenden gegen die scheiternden
   Ersatzwahlen: Differenz der Mittelwerte mit Bootstrap-Intervall. Ist D
   unter den tragenden Wahlen kleiner, bremst die formale Prüfung die
   Homogenisierung.
3. Selbsttest: Mindestens 3 von 4 unveränderten Probedateien müssen fehlerfrei
   sein, sonst wird nicht ausgewertet. Status `basis` (Fehler vor dem
   Theorem) und `timeout` fallen aus der Auswertung heraus und werden
   gezählt.
