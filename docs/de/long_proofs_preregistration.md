# Starkes Modell an langen Beweisen: Vorab-Festlegung

Festgelegt am 24.09.2026 gegen 18:00 Uhr (MESZ), bevor eine Aufgabe gebaut, ein Beweis geschrieben oder geprüft wurde.

Stand der Kenntnis zu diesem Zeitpunkt:
- Kompass-Test (kurze Beweise, 3–25 Schritte, Median 5), Arm frei: 73 von 80 in Runde 1, 79 von 80 bis Runde 3.
- Nur Strukturzahlen der Kandidaten (unten). Kein menschlicher Beweis dieser Sätze angesehen. Die Skizzen-Regel ist nur an künstlichen Beweisen getestet.

## Frage

1. **Grenze:** Wo liegt die Grenze eines starken Modells ohne Lean bei längeren Beweisen?
2. **Werkzeug:** Verschiebt eine Gliederung des Beweises diese Grenze? Das ist der Kern eines möglichen Werkzeugs: Der Mathematiker gibt die Gliederung, das Modell füllt sie aus.

## Sätze

- Alle mathlib-Sätze aus d0a050ad6, die neu seit Juni 2026 sind, Auswahl wie im Kompass-Test:
  - ohne Umbenennungen;
  - Deklaration vor Zeile 2500, Aussage kürzer als 600 Zeichen, ohne `sorry`;
  - aber mit menschlichem Beweis ab **25** Taktikschritten.
- Das sind **57 Sätze** (Strukturzählung vom 24.09.): 32 mit 25–34 Schritten, 16 mit 35–49, 9 ab 50 (bis 142).
- **Code:**

  | Datei | SHA-256 (Anfang) |
  |---|---|
  | `kandidaten.py` | d9ac5590… |
  | `skizze.py` | 33978738… |
  | `aufgaben_lang.py` | 535e5b46… |

- **Kontext** wie im Kompass-Test: Dateianfang bis zum Satz, gekürzt auf die ersten 3000 und die letzten 12.000 Zeichen. Der Name ist durch `ziel` ersetzt.

## Zwei Arme je Satz, sonst identisch

- **frei:** nur die Aufgabe, mit demselben Aufgabentext wie im Kompass-Test.
- **Skizze:** dazu die Gliederung des menschlichen Beweises auf oberster Ebene (`skizze.py`).
  - Jede Zeile der obersten Ebene wird mit den tiefer eingerückten Zeilen danach zu genau einer Zeile der Gliederung.
  - Bei `have`, `obtain`, `suffices` und `show` bleibt die Aussage stehen. Ihr Beweis wird durch `…` ersetzt.
  - Bei allen anderen Zeilen bleibt nur das erste Wort, also die Taktik, gefolgt von `…`. Fälle nach `induction … with` behalten ihr Muster.
  - Kommentare fallen weg.

## Runden und Prüfung

- **Runden:** bis zu 3 je Arm, wie im Kompass-Test.
  - Runde 1 ohne Rückmeldung.
  - Runden 2 und 3 mit dem vorigen Versuch und der ersten Lean-Fehlermeldung, bis 1500 Zeichen, Satznamen geschwärzt.
  - Der Arm bleibt dabei gleich, die Skizze also auch.
- **Agenten:** Claude-Subagenten wie im Kompass-Test, höchstens 4 Aufgaben je Agent, nur ein Arm je Agent. Aufgaben, deren Satz im Kontext einer anderen vorkommt, kommen nie zum selben Agenten.
- **Abbrüche** (Ausgabelimit): einmal wiederholen, danach zählt der Versuch als nicht gelöst.
- **Prüfung:** `stark_pruef.py` auf dem Mac, Zeitlimit 600 s je Beweis.

## Erfolg

- Lean meldet keinen Fehler, und der Beweis enthält kein `sorry`, `admit` oder `native_decide`.
- Ein Satz gilt in einem Arm als gelöst, wenn eine der bis zu drei Runden gelingt.
- Sätze mit Status `basis` fallen weg.

## Hypothesen

- **L1 (primär): Die Lösequote sinkt mit der Länge.**
  - Arm frei, gelöst bis Runde 3.
  - Drei Bänder: 25–34, 35–49, ab 50 Schritte.
  - Test: Cochran-Armitage-Trendtest, einseitig. **BESTÄTIGT** bei p < 0,05.
- **L2 (primär): Die Skizze hilft.**
  - Test: exakter McNemar-Test, einseitig (Skizze besser als frei), gelöst bis Runde 3.
  - **BESTÄTIGT** bei p < 0,05.
  - Bei weniger als 10 abweichenden Paaren lautet das Urteil **NICHT ENTSCHEIDBAR**.
- **L3 (sekundär):** L2 für Runde 1 allein.

## Beschreibend

- Lösequote je Band, Arm und Runde, mit Wilson-Intervallen.
- Vergleich mit den kurzen Beweisen aus dem Kompass-Test (Arm frei).
- Länge gelungener Beweise im Vergleich zum menschlichen Beweis.
- Fehlerarten der letzten Versuche.
- `exact?` und `apply?` in gelungenen Beweisen.
- Abbrüche der Agenten.
- **Kontaminationsprüfung** wie im Kompass-Test: Taktikfolge und benutzte Namen im Vergleich zum menschlichen Beweis.

## Kontaminationsschutz

- **Während der Generierung ist verschlüsselt:**
  - alle Quellen neuer Beweise, wie im Kompass-Test;
  - die exakten Abhängigkeiten;
  - die Aufgaben- und Kontextdateien dieses Tests.

  Aufgaben späterer Runden werden nur gebaut, während kein Agent läuft.
- **Getrennte Verzeichnisse:** Die Aufgaben der beiden Arme liegen in getrennten Verzeichnissen.

## Grenzen

- 57 Sätze reichen nur für große Effekte.
- Die Skizze stammt aus dem menschlichen Beweis. Ein echter Nutzer würde eine gröbere Gliederung schreiben.
- Das Modell hat beim Schreiben keinen Lean-Zugriff, nur die Rückmeldung zwischen den Runden.
