# Ergebnis: das Lückenexperiment (Lauf 2)

Ausgewertet exakt wie in `PRAEREGISTRIERUNG_LUECKEN.md` festgelegt. Das
Auswertungsskript ist byte-gleich mit der vorab abgelegten Fassung (md5
`e25b71dd…`). Es wurde einmal auf Lauf 2 angewendet. Lauf 1 ist wegen des
Tokenisierungsfehlers verworfen (Abweichung L3) und nicht ausgewertet.

**Proband:** DeepSeek-Prover-V2-7B (`mlx-community/…-4bit`), Apple M4,
mlx-lm 0.31.3, greedy, 32 Token, Prompt-Token direkt aus `tokenizer.json`.
Selbsttest: 1000/1000 Präfixe verlustfrei.
**Daten:** 1.000 Lücken aus Theoremen, die erst nach dem 1. August 2026 in
mathlib kamen.

## Kategorien

| Kategorie | Anzahl | Anteil |
|---|---|---|
| gleich (dasselbe Lemma wie der Mensch) | 119 | 11,9 % |
| anderes Lemma | 305 | 30,5 % |
| kein Lemma (Taktik, Hypothese …) | 311 | 31,1 % |
| erfunden (Name existiert nicht) | 211 | 21,1 % |
| Punktnotation | 54 | 5,4 % |

Abbruchkriterium (< 200 Lemma-Wahlen) nicht erreicht: 424.

## Primärtest: H1 bestätigt

Dₛ = log(1 + Nutzung Modellwahl) − log(1 + Nutzung Menschenwahl), explizite
Nutzung in LeanDojo v2, über *gleich* + *anderes Lemma* (n = 424):

> **mittleres D = +1,16**, 95 %-KI [+0,93; +1,39],
> Permutations-p < 0,0001, **Faktor exp(D) = 3,2**.
> Median +0,29; D > 0 in 220, D < 0 in 76, D = 0 in 128 Lücken
> (Vorzeichentest p = 2e-17).

Die Schwelle „bedeutsam" (|D| ≥ 0,25) ist weit überschritten.

## Sekundär

1. **Nur Abweichungen** (n = 305): D = +1,61 [+1,31; +1,91], Faktor 5,0.
   Die Wahl des Modells ist in 72 % der Fälle populärer (220 zu 76).
   Median der Nutzung: Modellwahl 80, Menschenwahl 10.
2. **Gesamter Eingangsgrad MathlibGraph** (n = 361): D = +0,86 [+0,62; +1,11],
   p < 0,0001.
3. **Kategorienanteile:** siehe oben. An 52 % der Stellen, an denen ein Mensch
   ein vorhandenes Lemma benannte, benennt das Modell keines oder ein
   erfundenes.
4. **Vergleichsanker:** Faktor 3,2 (Abweichungen: 5,0) gegenüber 6–7 in der
   Zitationsstudie von Algaba u. a.

Häufigste Ersatzwahlen des Modells: `mul_comm` (13), `mul_assoc` (9),
`add_comm` (8), `mul_one` (7), `sub_eq_zero` (4). Beispiele: Mensch
`Filter.eventually_inf_principal` (9×) → Modell `dist_comm` (192×); Mensch
`AffineSubspace.ext_of_direction_eq` (6×) → Modell `le_antisymm` (1.206×).

## Explorativ, nicht vorab festgelegt

**Wo entsteht der Effekt?** Aufgeteilt nach der Popularität des menschlichen
Lemmas:

| menschliches Lemma | n | gleich | erfunden | D (alle Lemma-Wahlen) | D (Abweichungen) | populärer |
|---|---|---|---|---|---|---|
| selten (≤ 3 Nutzungen) | 362 | 4 % | 25 % | +2,78 | +3,17 | 87 % |
| mittel (4–29) | 305 | 12 % | 22 % | +1,35 | +1,85 | 77 % |
| häufig (> 29) | 333 | 20 % | 16 % | −0,16 | −0,27 | 52 % |

Nur Lücken, deren menschliches Lemma mindestens 10 Nutzungen hatte:
D = +0,18 [−0,05; +0,41], unter den Abweichungen 59 % populärer (p = 0,024).

**Lesart:** Der Effekt sitzt fast ganz an Stellen, an denen der Mensch ein
seltenes, spezifisches Lemma benutzt hat. Dort greift das Modell zu
Allerweltsalgebra oder erfindet einen Namen. Ist das menschliche Lemma selbst
verbreitet, gibt es kaum einen Unterschied. Die Aufteilung nach der
menschlichen Wahl enthält Regression zur Mitte (sie drückt das obere Terzil
nach unten). Deshalb gilt der Primärtest über alle Lücken. Die Aufteilung
zeigt aber, woher der Effekt kommt.

## Einordnung

- **Gegenrichtung zu den Maintainern:** Bei Überarbeitungen ersetzen
  Maintainer explizit genannte Lemmas durch seltener genannte, spezifischere
  (Δlog −0,62, Schritt 22). Das Modell geht an denselben Stellen in die
  entgegengesetzte Richtung (+1,16).
- **Nichtwissen oder Vorliebe?** Offen. Die Aufteilung spricht eher für
  Nichtwissen: seltene Lemmas kennt ein 7B-Modell nicht, dann greift es zum
  Häufigen. Die Vorab-Festlegung nannte beides „für die Wirkung auf eine
  Bibliothek gleich". Das ist zu stark: In eine Bibliothek kommen nur Wahlen,
  die Lean akzeptiert. **Stufe 2** (Lean-Prüfung der 305 Ersatzwahlen)
  entscheidet, ob hier Homogenisierung oder bloß Scheitern vorliegt.

## Stufe 2: Trägt die Ersatzwahl? (Lean-Prüfung, explorativ, vorab festgelegt)

Alle 305 Ersatzwahlen, mathlib `d0a050ad6`, mathlibs eigene Optionen.
Selbsttest 4/4 unveränderte Dateien fehlerfrei. Keine Zeitüberschreitung,
kein Fehler vor dem Theorem.

| Kontext | Ersatz trägt | davon trivial (Hinweis war überflüssig) |
|---|---|---|
| simp/grind-Hinweisliste | 13 / 129 | 13 |
| rw-Liste | 1 / 111 | – |
| Term/Argument | 1 / 65 | – |
| **gesamt** | **15 / 305 (4,9 %)** | |

**Wo das menschliche Lemma gebraucht wurde, trägt die Wahl des Modells so gut
wie nie:** in Hinweislisten, deren Hinweis nötig war (die Streichung scheitert),
0 von 114; in rw-Listen und Termen 2 von 176. Die beiden Treffer sind
Beinahe-Synonyme: `Quotient.inductionOn` statt `Quotient.inductionOn'`,
`mul_left_iterate` statt `mul_left_iterate_apply`.

Häufigste Fehler: in rw-Listen „Muster nicht gefunden" (58 von 110), in Termen
Typfehler (35 von 64), in Hinweislisten offene Ziele (56 von 116).

Der vorab geplante Vergleich der Popularität tragender gegen scheiternder
Wahlen ist mit 2 tragenden Wahlen nicht rechenbar.

**Folgerung für die Deutung von Stufe 1:** Die populären Ersatzwahlen sind
fast durchweg **Fehler, keine alternativen Beweiswege**. Der Befund spricht
für Nichtwissen: An Stellen, die ein spezifisches Lemma verlangen, kennt das
Modell es nicht und greift zum Häufigen. Formale Prüfung filtert diese Wahlen
vollständig heraus. Eine Bibliothek würde dadurch also nicht homogener. Der
Engpass liegt woanders: **das spezifische, selten benutzte Lemma zu finden**.
Genau hier setzt ein Suchverfahren nach Passung statt nach Popularität an.
Die Prüfung ist streng: Der Rest des menschlichen Beweises bleibt stehen. Ob
das Modell mit seiner Wahl einen anderen Beweis hätte führen können, misst sie
nicht.

## Grenzen

- Ein Proband, 4-Bit-quantisiert. Die Quantisierung kann generische Wahlen
  begünstigen. Goedel-Prover-V2-8B braucht ~20 GB RAM, der Mac hat 16 GB.
- Reine Textfortsetzung ohne Chat-Format. So wird der Beweiser in
  Suchverfahren oft nicht benutzt.
- Popularität = explizite Nutzung im Mai 2025, dem Zeitraum der Trainingsdaten
  des Modells.
