#!/usr/bin/env bash
# Lückenexperiment auf dem Mac starten -- LAUF 2 (Tokenisierung korrigiert).
#
#   bash ~/scripts/luecken/start.sh          # Selbsttest, 5 Lücken als Test, dann alle
#   bash ~/scripts/luecken/start.sh goedel   # optional: zweiter Beweiser
#
# Lauf 1 war ungültig: transformers 5 hat beim DeepSeek-Tokenizer Leerzeichen,
# Zeilenumbrüche und Sonderzeichen aus dem Prompt entfernt. Lauf 2 tokenisiert
# direkt mit der tokenizer.json des Modells und prüft das vor dem Start an
# allen 1.000 Präfixen. Das Modell ist schon geladen, es wird nichts Großes
# heruntergeladen. Wiederaufnehmbar: abbrechen und neu starten ist harmlos.
set -euo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
ENV="$HOME/luecken_env"

if [ "$(uname -m)" != "arm64" ]; then
  echo "Dieses Skript braucht einen Mac mit Apple Silicon (MLX)."; exit 1
fi
RAM_GB=$(( $(sysctl -n hw.memsize) / 1073741824 ))
echo "Chip: $(sysctl -n machdep.cpu.brand_string)   RAM: ${RAM_GB} GB"

case "${1:-deepseek}" in
  deepseek) MODEL="mlx-community/DeepSeek-Prover-V2-7B-4bit"; TAG="deepseek_v2_7b" ;;
  goedel)   MODEL="Goedel-LM/Goedel-Prover-V2-8B";            TAG="goedel_v2_8b"
            if [ "$RAM_GB" -lt 24 ]; then
              echo "Goedel ohne Quantisierung braucht ~20 GB RAM, hier sind ${RAM_GB} GB."; exit 1
            fi ;;
  *) echo "unbekannt: $1 (deepseek | goedel)"; exit 1 ;;
esac

# Python finden: bevorzugt ein normales python3 >= 3.10
PY=""
for c in python3.12 python3.11 python3.10 "$HOME/miniconda3/bin/python3" python3; do
  if command -v "$c" >/dev/null 2>&1; then
    if "$c" -c 'import sys; sys.exit(0 if sys.version_info >= (3,10) else 1)' 2>/dev/null; then
      PY="$(command -v "$c")"; break
    fi
  fi
done
[ -n "$PY" ] || { echo "Kein python3 >= 3.10 gefunden."; exit 1; }
echo "Python: $PY ($("$PY" --version))"

if [ ! -x "$ENV/bin/python" ]; then
  echo "lege Umgebung an: $ENV"
  "$PY" -m venv "$ENV"
  "$ENV/bin/python" -m pip install -q --upgrade pip
fi
# genau die Version, deren Quelltext für Lauf 2 geprüft wurde
"$ENV/bin/python" -m pip install -q "mlx-lm==0.31.3"
"$ENV/bin/python" -c 'import mlx_lm, transformers, tokenizers; print(f"mlx-lm {mlx_lm.__version__}   transformers {transformers.__version__}   tokenizers {tokenizers.__version__}")'

OUT="$DIR/ergebnisse_${TAG}_lauf2.jsonl"
LAUF1="$DIR/ungueltig_lauf1/ergebnisse_${TAG}.jsonl"
if [ ! -s "$OUT" ]; then
  echo; echo "=== Selbsttest und 5 Lücken als Probe ==="
  "$ENV/bin/python" "$DIR/luecken_lauf.py" --slots "$DIR/slots.jsonl" \
      --out "$OUT" --model "$MODEL" --limit 5 --lauf1 "$LAUF1"
  echo; echo "Probe lief. Jetzt alle 1.000 Lücken (M-Chip: grob 30-45 Minuten)."
fi
"$ENV/bin/python" "$DIR/luecken_lauf.py" --slots "$DIR/slots.jsonl" \
    --out "$OUT" --model "$MODEL"
echo; echo "Fertig. Ergebnisdatei: $OUT"
echo "Sagen Sie Claude Bescheid."
