# Kompass mit starkem Beweismodell: Vorab-Festlegung

Festgelegt am 24.09.2026, bevor ein Beweis geschrieben oder geprüft wurde.

## Frage

Hilft die Kompass-Verteilung einem starken Beweismodell? Gemeint ist die Verteilung über Beweisrichtungen, wie Menschen in mathlib solche Aussagen beginnen. Getestet wird an mathlib-Sätzen, die das Modell nicht kennen kann.

## Modell und Aufbau

- **Beweismodell:** Claude als Subagent derselben Sitzung. Konfiguriert ist `claude-opus-5-5`. Es hat keinen Werkzeugzugriff außer dem Lesen seiner Aufgabendatei und dem Schreiben der Antwort. Die Anweisung verbietet Internet und Dateisuche.
- **Sätze:** 80 Sätze aus mathlib d0a050ad6. Das Modell hat den Wissensstand Mai 2026.
  - Nur Namen, die in keinem Monatsstand bis 2026-06 vorkommen, also neu seit Juni 2026.
  - Ohne Umbenennungen: Die Aussage (ohne Namen, Leerraum normalisiert) darf im Quelltext von 2026-06 nicht vorkommen.
  - Menschlicher Beweis mit 3 bis 25 Taktikschritten, Deklaration vor Zeile 2500 der Datei, Aussage kürzer als 600 Zeichen.
  - Gezogen mit Seed 0, geschichtet nach Gebiet (proportional).
- **Kontext:**
  - Dateianfang bis zum Satz, gekürzt auf die ersten 3000 und die letzten 12.000 Zeichen.
  - Der Satz selbst mit dem Namen `ziel` statt des echten Namens.
  - Der menschliche Beweis wird nie gezeigt.
- **Zwei Arme je Satz**, sonst identisch:
  - **frei:** nur die Aufgabe.
  - **kompass:** dazu ein Hinweisblock: die Kompass-Verteilung (die drei wahrscheinlichsten Richtungen mit Prozent und den Signalen in der Aussage) und eine kurze Legende, welche Taktiken zu welcher Richtung gehören.
- **Runden:** bis zu drei.
  - Runde 1 ohne Rückmeldung.
  - Runden 2 und 3 mit dem vorigen Versuch und der ersten Lean-Fehlermeldung (bis 1500 Zeichen).
  - Der Arm bleibt dabei gleich, also auch der Hinweis.
- **Prüfung:** Lean auf dem Mac (`stark_pruef.py`, wie im Orakel-Lauf). Der menschliche Beweis wird durch den des Modells ersetzt und die Datei hinter dem Satz abgeschnitten. Zeitlimit 300 s.

## Erfolg

Lean `ok`, kein `sorry`, kein `native_decide`. Ein Satz gilt in einem Arm als gelöst, wenn eine der bis zu drei Runden gelingt. Sätze mit Status `basis` (Fehler vor dem Satz) fallen weg.

## Hypothesen

- **H1 (primär):** Mit Kompass werden mehr Sätze gelöst als frei (bis Runde 3).
  - Test: exakter McNemar-Test, einseitig, auf den Paaren je Satz.
  - Bestätigt bei p < 0,05.
  - Gibt es weniger als 10 abweichende Paare, heißt das Urteil „nicht entscheidbar“.
- **H2 (sekundär):** dasselbe für Runde 1 allein, also ohne Lean-Rückmeldung.
- **Manipulationsprüfung:** Wie oft beginnt der Beweis in der Kompass-Spitzenrichtung, mit und ohne Kompass?

## Deskriptiv

- Lösequote gesamt und je Runde.
- Ist die Richtung des Menschen für das Modell gangbar?
- Welche Richtungen nehmen die gelungenen Beweise?

## Kontaminationsschutz

- Die Quellen, die die neuen Beweise oder ihre Abhängigkeiten enthalten, sind während der Generierung verschlüsselt: mathlib-Checkout, Quelltext-Schnitte ab 2026-07, Parser-Schnitte ab 2026-07, exakte Abhängigkeiten, Kompass-Daten.
- Der Satzname wird ersetzt.
- **Prüfung danach:** Jeder gelungene Beweis wird mit dem menschlichen verglichen, nach Taktikfolge und benutzten Lemmas. Wörtliche Übereinstimmung wird gemeldet.

## Grenzen

- Es ist nur ein Modell. Der Hinweis ist weich formuliert: Das Modell darf ihn ignorieren.
- 80 Sätze reichen nur für einen großen Effekt. Ein kleiner Effekt des Kompass ist nicht ausschließbar.
