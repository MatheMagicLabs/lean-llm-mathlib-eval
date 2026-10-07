#!/usr/bin/env bash
# Lückenexperiment, Stufe 2: Lean prüft die Ersatzwahlen des Modells.
#
#   bash ~/scripts/luecken/stufe2/stufe2.sh
#
# Beim ersten Start wird ~/luecken_mathlib angelegt: mathlib genau in der
# Fassung, aus der die Lücken stammen (d0a050ad6, 21.09.2026), dazu der
# vorgebaute Cache (einige GB, 10-30 Minuten). Danach prüft Lean 305 Ersatz-
# wahlen und 129 Kontrollen, zwei gleichzeitig. Dauer grob 2-4 Stunden.
#
# Der Mac darf dabei nicht einschlafen: Netzteil anschließen, Deckel offen
# lassen. Das Skript hält den Mac mit `caffeinate` wach, solange es läuft.
# Wiederaufnehmbar: abbrechen und neu starten ist harmlos.
set -euo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
SHA="d0a050ad63b8e88c61363831b0dc6d3d69e99b53"
MDIR="${LUECKEN_MATHLIB:-$HOME/luecken_mathlib}"
export PATH="$HOME/.elan/bin:$PATH"

FREE_GB=$(df -k "$HOME" | awk 'NR==2 {print int($4/1048576)}')
echo "Freier Platz: ${FREE_GB} GB"
if [ ! -d "$MDIR/.lake" ] && [ "$FREE_GB" -lt 15 ]; then
  echo "Zu wenig Platz: mathlib mit Cache braucht etwa 10 GB, bitte mindestens 15 GB frei."
  exit 1
fi

if ! command -v lake >/dev/null 2>&1; then
  echo "Lean (elan) fehlt, installiere nach ~/.elan …"
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi
echo "elan: $(elan --version 2>/dev/null || echo '?')"

if [ ! -d "$MDIR/.git" ]; then
  echo "hole mathlib ${SHA:0:9} nach $MDIR …"
  mkdir -p "$MDIR"
  git -C "$MDIR" init -q
  git -C "$MDIR" remote add origin https://github.com/leanprover-community/mathlib4.git
  git -C "$MDIR" fetch -q --depth 1 origin "$SHA"
  git -C "$MDIR" checkout -q FETCH_HEAD
fi
HEAD_NOW="$(git -C "$MDIR" rev-parse HEAD)"
if [ "$HEAD_NOW" != "$SHA" ]; then
  echo "$MDIR steht auf ${HEAD_NOW:0:9}, erwartet ${SHA:0:9}. Bitte Ordner löschen oder umbenennen."
  exit 1
fi

cd "$MDIR"
echo "Lean-Version: $(cat lean-toolchain)"
echo "lade den vorgebauten Cache (beim ersten Mal mehrere GB) …"
lake exe cache get

PY="$HOME/luecken_env/bin/python"
[ -x "$PY" ] || PY="$(command -v python3)"
echo; echo "=== Lean-Prüfung startet ==="
caffeinate -i "$PY" "$DIR/stufe2_lauf.py" --mathlib "$MDIR" --patches "$DIR/patches.jsonl" \
  --out "$DIR/stufe2_ergebnisse.jsonl" --workers "${WORKERS:-2}"
echo; echo "Fertig. Ergebnisdatei: $DIR/stufe2_ergebnisse.jsonl"
echo "Sagen Sie Claude Bescheid."
