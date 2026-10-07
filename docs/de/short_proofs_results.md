# Kompass mit starkem Modell: Ergebnis

Vorab festgelegt in `VORAB_KOMPASS_STARK.md` (SHA-256 75b5377e…). Gerechnet am 24.09.2026. Alle Runden sind abgeschlossen.

## In einem Satz

Der Kompass hilft dem starken Modell nicht. Er ändert nicht einmal, wie es Beweise beginnt. Das Modell braucht ihn auch nicht: Es beweist 73 von 80 neuen mathlib-Sätzen im ersten Versuch, ohne Lean, und 79 von 80 mit bis zu zwei Lean-Rückmeldungen.

## Lösequoten

| | Runde 1 (ohne Rückmeldung) | bis Runde 2 | bis Runde 3 | ungelöst |
|---|---|---|---|---|
| frei | 73 (91 %) | 79 | 79 (99 %) | Satz 24 |
| Kompass | 68 (85 %) | 76 | 78 (98 %) | Sätze 15 und 24 |

## Hypothesen

| | nur Kompass gelöst | nur frei gelöst | p (einseitig) | Urteil |
|---|---|---|---|---|
| **H1** (bis Runde 3) | 0 | 1 (Satz 15) | 1,0 | **nicht entscheidbar** (weniger als 10 abweichende Paare) |
| **H2** (nur Runde 1) | 1 | 6 | 0,99 | **nicht entscheidbar** |

- Die Tendenz geht **gegen** den Kompass: In Runde 1 löst der Kompass-Arm 5 Sätze weniger.
- Nach der Vorab-Regel sind beide Tests nicht entscheidbar. Das Modell löst fast alles, deshalb gibt es zu wenige abweichende Paare.

## Manipulationsprüfung

Wie oft beginnt ein Beweis aus Runde 1 in der Spitzenrichtung des Kompass?

| | frei | Kompass |
|---|---|---|
| in der Spitzenrichtung | 37 von 80 | 37 von 80 |

- Der Hinweis ändert das Verhalten des Modells nicht (4 zu 4 abweichende Paare).
- Zum Vergleich: Die Richtung des Menschen ist in 41 von 80 Sätzen die Spitzenrichtung.

## Beschreibend

- **Richtungen der gelungenen Beweise** (frei): Zwischenaussage 33, Fallunterscheidung 16, Ziel zerlegen 14, Lemma anwenden 7, Umschreiben 3, Widerspruch 3, Induktion 2, Rechnen 1. Das Modell beginnt am liebsten mit `have`. Beim Menschen führt ebenfalls die Zwischenaussage (23), gefolgt von Ziel zerlegen (17).
- **Ist die Richtung des Menschen gangbar?** Ja, aber sie ist nicht der Schlüssel.
  - Gelungene Beweise beginnen wie der Mensch: frei 46 von 79, Kompass 50 von 78.
  - Runde 1, frei: Beginnt das Modell wie der Mensch, gelingen 40 von 47. Beginnt es anders, gelingen 33 von 33.
  - Runde 1, Kompass: 42 von 49 gegen 26 von 31.
- **Von keinem Arm gelöst:** Satz 24 (Kategorientheorie, 8 Schritte).

## Kontaminationsprüfung

Verglichen wurden alle 157 gelungenen Beweise mit dem menschlichen Beweis.

| Maß | Median |
|---|---|
| Ähnlichkeit der Token-Folge | 0,19 |
| Ähnlichkeit der Taktikfolge | 0,25 |
| gemeinsame Namen (Jaccard) | 0,18 |

- **Wörtlich gleich:** Sätze 3 und 6, in beiden Armen.
- **Fast wörtlich:** Satz 8, Kompass-Arm, Ähnlichkeit 0,98.
- **Erklärung:** In allen drei Fällen steht direkt vor dem Satz ein Schwester-Lemma mit demselben Beweismuster im Kontext.
  - Satz 3: `partNum_euler_zero` mit `rw [partNums, @Stream'.Seq.map_get?, euler_s_zero]`. Das Modell ersetzt `zero` durch `succ`.
  - Satz 6: `ext <;> simp <;> ring` steht im Kontext.
  - Satz 8: `r_integral_of_u_integral` und `s_integral_of_u_integral`. Das Modell übernimmt das Muster und bestimmt das passende quadratische Polynom selbst.
- **Kein Hinweis auf Auswendiglernen.** Die übrigen Beweise weichen deutlich von den menschlichen ab.

## Vorkommnisse und Abweichungen

- **Rückmeldung:** Die Vorab-Festlegung sieht die erste Lean-Fehlermeldung vor (bis 1500 Zeichen). Der Aufgabenbauer hätte bis zu drei Meldungen gezeigt. Das habe ich vor Runde 2 korrigiert. Echte Satznamen in Fehlermeldungen werden geschwärzt; es kam keiner vor.
- **Abbrüche der Agenten** (Ausgabelimit 128.000 Token). Regel: einmal wiederholen, danach zählt der Versuch als nicht gelöst.
  - Runde 2, frei 4 und 24: einmal abgebrochen, die Wiederholung lieferte Beweise.
  - Runde 3, Kompass 15 und 24, frei 24: zweimal abgebrochen, zählt als nicht gelöst.
  - Alle Abbrüche betreffen die schwersten Sätze. Die Regel gilt für beide Arme gleich.
- **`exact?`:** Zwei gelungene Reparaturbeweise enthalten `exact?` als letzte Ausweichmöglichkeit (frei 4 in Runde 2, Kompass 13 in Runde 3). Ob es tatsächlich griff, zeigt die Prüfung nicht. Die Vorab-Festlegung schließt es nicht aus. Ohne diese beiden: frei 78, Kompass 77; die Urteile bleiben gleich.
- **Kontrollen:** 5 falsche Beweise → `fehler`, 3 mit `sorry` → `sorry`. Die menschlichen Beweise bestehen die Prüfung.
- **Mac:** Die Verbindung riss am Morgen ab. Die letzten Prüfungen (Runde 2 Rest, Runde 3) hast du von Hand angestoßen.

## Was daraus folgt

- **Als Hinweis für starke Modelle ist der Kompass nutzlos.** Das Modell beachtet ihn nicht und braucht ihn nicht. Der Kompass bleibt eine gut geeichte Beschreibung menschlicher Beweisgewohnheiten (K1, K2, K4 bestätigt), aber kein Werkzeug, das Beweise besser macht.
- **Wichtiger ist die Beobachtung nebenbei:** Ein starkes Modell ohne Lean beweist 91 % neuer, kurzer mathlib-Sätze im ersten Versuch. Mit bis zu zwei Lean-Rückmeldungen sind es 99 %.
  - Kurze Lemmas (Median 5 Schritte) sind damit kein Engpass mehr.
  - Offen sind lange Beweise und neue Definitionen. Dort liegt die echte Grenze.

## Dateien

- `VORAB_KOMPASS_STARK.md`, `aufgaben_bauen.py`, `runde.py`, `stark_pruef.py`, `pruef_runde.sh`
- `auswertung.py`, `ergebnis_kompass_stark.json` (alle Zahlen, auch der Abgleich je Beweis)
- `beweise_r1.jsonl`, `beweise_r2.jsonl`, `beweise_r3.jsonl`, `pruefung.jsonl`
