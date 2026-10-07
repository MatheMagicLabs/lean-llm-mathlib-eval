#!/usr/bin/env bash
# Lean prüft eine Runde des Tests an langen Beweisen (Aufruf: bash pruef_lang.sh <runde>)
set -uo pipefail
export PATH="$HOME/.elan/bin:$PATH"
R="$1"
D="$HOME/scripts/luecken/lang"
PY="$HOME/luecken_env/bin/python"
MDIR="${LUECKEN_MATHLIB:-$HOME/luecken_mathlib}"
[ -s "$D/beweise_r$R.jsonl" ] || { echo "beweise_r$R.jsonl fehlt"; exit 1; }
"$PY" "$HOME/scripts/luecken/kompass_stark/stark_pruef.py" --mathlib "$MDIR" --patches "$D/aufgaben_lang.jsonl" \
  --beweise "$D/beweise_r$R.jsonl" --out "$D/pruefung.jsonl" --workers 4 --timeout 600
touch "$D/fertig_r$R"
echo "fertig Runde $R"
