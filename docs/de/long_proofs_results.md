# Starkes Modell an langen Beweisen: Ergebnis (bis Runde 2)

Vorab festgelegt in `VORAB_LANG.md` (SHA-256 ef8dbf4f…). Gerechnet am 27.09.2026.

**Abweichung:** Vorab festgelegt waren bis zu drei Runden. Runde 3 wurde auf Wunsch des Nutzers nicht mehr gerechnet, weil das Ergebnis nach Runde 2 keinen Durchbruch erwarten ließ und das Ausgabenlimit bereits einmal erreicht war. Alle Urteile unten gelten deshalb „bis Runde 2“.

## In einem Satz

Ein starkes Modell ohne Lean beweist 54 % neuer, langer mathlib-Sätze (25–142 Schritte) im ersten Versuch und 72 % mit einer Lean-Rückmeldung. Die Grenze liegt bei Beweisen ab 50 Schritten (3 von 9). Die Gliederung des menschlichen Beweises hilft nicht.

## Lösequoten (57 Sätze)

| | Runde 1 | bis Runde 2 | 95 %-Intervall |
|---|---|---|---|
| frei | 31 (54 %) | 41 (72 %) | 59–82 % |
| Skizze | 27 (47 %) | 42 (74 %) | 61–83 % |

Je Längenband, bis Runde 2:

| Band (Schritte des menschlichen Beweises) | Sätze | frei | Skizze |
|---|---|---|---|
| 25–34 | 32 | 24 (75 %) | 23 (72 %) |
| 35–49 | 16 | 14 (88 %) | 14 (88 %) |
| ab 50 | 9 | 3 (33 %) | 5 (56 %) |

Zum Vergleich kurze Sätze (Kompass-Test, 3–25 Schritte): 91 % im ersten Versuch, 99 % bis Runde 2.

## Hypothesen

| | Test | Ergebnis | Urteil |
|---|---|---|---|
| **L1:** Quote sinkt mit der Länge (frei) | Cochran-Armitage, einseitig | z = −1,76, p = 0,039 | **bestätigt** (bis Runde 2) |
| **L2:** Die Skizze hilft (bis Runde 2) | McNemar, einseitig | nur Skizze 3, nur frei 2; p = 0,50 | **nicht entscheidbar** (5 abweichende Paare) |
| **L3:** Die Skizze hilft in Runde 1 | McNemar, einseitig | nur Skizze 4, nur frei 8; p = 0,93 | **nicht bestätigt** |

- **L1:** Der Rückgang kommt vor allem aus dem Band ab 50 Schritten. Das mittlere Band liegt sogar über dem ersten. Die Grenze ist also eher eine Stufe bei sehr langen Beweisen als ein gleichmäßiger Abfall.
- **L2/L3:** Die Gliederung aus dem menschlichen Beweis bringt nichts. In Runde 1 schneidet der Skizze-Arm eher schlechter ab.

## Beschreibend

- **Länge der gelungenen Beweise:** Median 77 Zeilen (frei) und 92 Zeilen (Skizze).
- **Menschliche Beweislänge:** gelöste und ungelöste Sätze unterscheiden sich im Median kaum (33 gegen 33,5 Schritte, frei).
- **Fehlerarten aller gescheiterten Versuche:**
  - unbekannte Namen: 20;
  - Typfehler und fehlende Instanzen: 19;
  - offene Ziele: 7;
  - gescheiterte Taktiken: 4;
  - Zeitlimit: 1;
  - sonstige: 21.
- **Keine Suchtaktiken:** Kein gelungener Beweis nutzt `exact?` oder `apply?`.

## Kontaminationsprüfung

- **Vergleich mit dem menschlichen Beweis:** 83 gelungene Beweise, Median-Ähnlichkeit 0,15. Keiner ist wörtlich gleich.
- **Einziger auffälliger Fall:** Satz 4 (frei) mit 0,85. Direkt davor steht im Kontext das Schwester-Lemma `variation_vectorMeasure_Ioi`; ihm ähnelt der Beweis des Modells zu 0,69.

## Vorkommnisse

- **Kontamination durch Konfliktprüfung (Runde 1):** Meine Konfliktprüfung übersah Namen mit Punkt. Dadurch sah ein Agent den menschlichen Beweis von Satz 0 im Kontext von Satz 1 und schrieb ihn ab; der Agent hat das selbst gemeldet.
  - Beide betroffenen Versuche wurden verworfen und mit korrigierter Prüfung wiederholt.
  - Im Kompass-Test hat derselbe Fehler nichts übersehen.
- **Abbrüche:**
  - Runde 1: frei 0 zweimal abgebrochen, zählt als nicht gelöst.
  - Runde 2: 13 Aufgaben ohne Beweis (frei 0, 1, 7, 14, 21, 43, 56; Skizze 0, 1, 2, 7, 14, 45). Zuerst griff das Ausgabenlimit der Organisation, in der Wiederholung das Längenlimit der Antwort. Sie zählen als nicht gelöst.
- **„basis“ bei Skizze 14 (Runde 1):** Die unveränderte Datei prüft fehlerfrei. Der Fehler kam also vom Beweis des Modells und zählt als Fehlschlag.
- **Kontrollen:** falsche Beweise → `fehler`, `sorry` → `sorry`, in beiden Runden.

## Was daraus folgt

- Kurze neue Lemmas sind für ein starkes Modell gelöst (99 %). Lange Beweise schafft es zu etwa drei Vierteln, sehr lange (ab 50 Schritten) zu etwa einem Drittel.
- Eine Gliederung vom Menschen, wie sie ein Werkzeug „Mensch skizziert, Modell füllt aus“ liefern würde, hilft in dieser Form nicht. Die gescheiterten Versuche scheitern meist an Details: falsche Namen, Typen, Instanzen. Dass dort der eigentliche Engpass liegt, ist eine Deutung; zeigen müsste es ein Vergleich mit besserem Bibliothekszugriff.
- Das legt nahe, dass für Werkzeuge der direkte Lean-Zugriff während des Schreibens mehr bringt als Hinweise zur Struktur; geprüft ist das nicht. Der Kompass-Test kam zum selben Schluss.
- Ein Durchbruch ist das nicht. Der Test wird wie vereinbart nicht fortgesetzt.
