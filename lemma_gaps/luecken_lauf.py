#!/usr/bin/env python3
"""
Lückenexperiment, Stufe 1 -- LAUF 2 (Tokenisierung korrigiert).

Nur Generierung, keine Auswertung. Pro Lücke wird die rohe Fortsetzung
gespeichert; welches Lemma darin steckt, entscheidet die Auswertung, für alle
Probanden mit demselben Code.

Warum Lauf 2
------------
In Lauf 1 kamen die Prompt-Token aus transformers >= 5 (AutoTokenizer).
DeepSeek-Prover meldet seinen Tokenizer als `LlamaTokenizerFast`; transformers 5
baut diese Klasse selbst nach (Metaspace-Vortokenisierung) und übernimmt aus
tokenizer.json nur Vokabular und Merges. Das Vokabular ist aber Byte-Level-BPE.
Folge: Leerzeichen, Zeilenumbrüche und alle Nicht-ASCII-Zeichen (∀ → ⟨ ⟩ ℝ …)
fielen im Prompt stillschweigend weg. Das Modell sah zerstörten Lean-Code.

Jetzt:
  * Prompt-Token direkt aus der tokenizer.json des Modells
    (tokenizers.Tokenizer.from_file), BOS vorangestellt
  * Ausgabe mit demselben Tokenizer dekodiert
  * SELBSTTEST vor dem Laden des Modells: für ALLE Präfixe muss
    decode(encode(x)) == x gelten, sonst Abbruch ohne Generierung

Unverändert (PRAEREGISTRIERUNG_LUECKEN.md):
  * reine Textfortsetzung, kein Chat-Template, keine Anweisung
  * greedy (Temperatur 0), höchstens 32 neue Token
  * Leerzeichen am Präfixende werden entfernt

Zusätzlich gespeichert (explorativ, nicht Teil der Hypothesenprüfung):
  erzeugte Token-IDs, Log-Wahrscheinlichkeit jedes erzeugten Tokens,
  die fünf wahrscheinlichsten Token im ersten Schritt.

Wiederaufnehmbar: bereits bearbeitete Lücken werden übersprungen. Eine
Ausgabedatei aus einem anderen Lauf wird nicht fortgesetzt.

    python3 luecken_lauf.py --slots slots.jsonl --out ergebnisse_lauf2.jsonl \
        --model mlx-community/DeepSeek-Prover-V2-7B-4bit
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys
import time
from pathlib import Path

MARK = "tokenizer.json direkt (Lauf 2)"


def env_info():
    info = {"python": sys.version.split()[0], "platform": platform.platform()}
    for k, cmd in (("chip", ["sysctl", "-n", "machdep.cpu.brand_string"]),
                   ("ram_bytes", ["sysctl", "-n", "hw.memsize"])):
        try:
            info[k] = subprocess.check_output(cmd, text=True,
                                                  stderr=subprocess.DEVNULL).strip()
        except Exception:
            info[k] = "?"
    for mod in ("mlx", "mlx_lm", "transformers", "tokenizers"):
        try:
            m = __import__(mod)
            info[mod] = getattr(m, "__version__", "?")
        except Exception:
            info[mod] = "nicht installiert"
    return info


# ---------------------------------------------------------------- Tokenizer
def model_dir(name):
    """Lokaler Ordner des Modells (derselbe, aus dem mlx_lm lädt)."""
    p = Path(name)
    if p.exists():
        return p
    from huggingface_hub import snapshot_download
    try:                                             # schon geladen: kein Netz nötig
        return Path(snapshot_download(name, local_files_only=True))
    except Exception:
        pass
    try:
        from mlx_lm.utils import _download          # mlx-lm 0.31.x
        return Path(_download(name))
    except Exception:
        return Path(snapshot_download(name))


def _kinds(spec):
    """Typen einer (evtl. verschachtelten) tokenizers-Komponente, z. B. ['ByteLevel']."""
    if not spec:
        return []
    if isinstance(spec, list):
        return [k for s in spec for k in _kinds(s)]
    inner = [k for key in ("pretokenizers", "normalizers", "decoders")
             for k in _kinds(spec.get(key))]
    return inner or [spec.get("type", "?")]


def load_raw_tokenizer(mdir):
    from tokenizers import Tokenizer
    tj = mdir / "tokenizer.json"
    raw = Tokenizer.from_file(str(tj))
    spec = json.load(open(tj, encoding="utf-8"))
    cfg = {}
    if (mdir / "tokenizer_config.json").exists():
        cfg = json.load(open(mdir / "tokenizer_config.json", encoding="utf-8"))
    name = lambda x: x.get("content") if isinstance(x, dict) else x
    bos, eos = name(cfg.get("bos_token")), name(cfg.get("eos_token"))
    bos_id = raw.token_to_id(bos) if bos else None
    eos_id = raw.token_to_id(eos) if eos else None
    add_bos = cfg.get("add_bos_token", True)
    info = dict(tokenizer_json_sha256=hashlib.sha256(tj.read_bytes()).hexdigest(),
                tokenizer_class=cfg.get("tokenizer_class"),
                normalizer=_kinds(spec.get("normalizer")),
                pre_tokenizer=_kinds(spec.get("pre_tokenizer")),
                decoder=_kinds(spec.get("decoder")),
                bos=bos, bos_id=bos_id, eos=eos, eos_id=eos_id,
                add_bos=bool(add_bos and bos_id is not None))
    return raw, info


def encode(raw, info, text):
    ids = raw.encode(text, add_special_tokens=False).ids
    return ([info["bos_id"]] if info["add_bos"] else []) + ids


def selftest(raw, info, slots):
    """decode(encode(p)) muss für jedes Präfix exakt p ergeben."""
    norm = None
    try:
        norm = raw.normalizer
    except Exception:
        pass
    bad, changed_by_norm = [], 0
    for s in slots:
        p = s["prefix"].rstrip(" \t")
        target = p
        if norm is not None:
            target = norm.normalize_str(p)
            changed_by_norm += target != p
        ids = raw.encode(p, add_special_tokens=False).ids
        back = raw.decode(ids, skip_special_tokens=False)
        if back != target:
            bad.append((s["id"], p, back))
    return bad, changed_by_norm


def compare_with_transformers(raw, info, mdir, slots, lauf1_file=None):
    """Was hat das Modell in Lauf 1 gesehen? (AutoTokenizer wie mlx_lm)"""
    out = {}
    try:
        from transformers import AutoTokenizer
        hf = AutoTokenizer.from_pretrained(str(mdir))
    except Exception as e:
        return {"fehler": repr(e)[:200]}
    out["transformers_klasse"] = type(hf).__name__
    lost_chars, n_diff, example = 0, 0, None
    n_old = {}
    for s in slots:
        p = s["prefix"].rstrip(" \t")
        old = hf.encode(p)
        new = encode(raw, info, p)
        n_old[s["id"]] = len(old)
        if old != new:
            n_diff += 1
            seen = raw.decode([t for t in old if t != info["bos_id"]],
                              skip_special_tokens=False)
            lost_chars += max(len(p) - len(seen), 0)
            if example is None:
                example = (s["id"], p[-120:], seen[-120:])
    out.update(praefixe_anders=n_diff, praefixe=len(slots),
               verlorene_zeichen=lost_chars,
               zeichen=sum(len(s["prefix"].rstrip(" \t")) for s in slots),
               beispiel=example)
    if lauf1_file and os.path.exists(lauf1_file):
        same = total = 0
        for l in open(lauf1_file, encoding="utf-8"):
            try:
                o = json.loads(l)
            except json.JSONDecodeError:
                continue
            if "id" in o and o["id"] in n_old:
                total += 1
                same += o.get("n_prompt") == n_old[o["id"]]
        out["lauf1_promptlaenge_reproduziert"] = f"{same}/{total}"
    return out


# ---------------------------------------------------------------- Modell
def make_generate(model_name):
    import mlx.core as mx
    from mlx_lm import load
    from mlx_lm.generate import generate_step
    model, tok = load(model_name)
    try:
        from mlx_lm.sample_utils import make_sampler
        sampler = make_sampler(temp=0.0)
    except Exception:
        sampler = None                      # generate_step nimmt dann argmax
    eos_extra = set()
    try:
        eos_extra = set(int(t) for t in tok.eos_token_ids)
    except Exception:
        pass

    def run(ids, n, eos_ids):
        eos_all = set(eos_ids) | eos_extra
        out, lps, top = [], [], None
        gen = generate_step(mx.array(ids), model, max_tokens=n, sampler=sampler)
        for step, (t, logprobs) in enumerate(gen):
            t = int(t)
            if step == 0:
                try:
                    idx = mx.argsort(logprobs)[-5:].tolist()[::-1]
                    top = [[int(i), round(float(logprobs[i].item()), 4)] for i in idx]
                except Exception:
                    top = None
            if t in eos_all:
                break
            out.append(t)
            try:
                lps.append(round(float(logprobs[t].item()), 4))
            except Exception:
                lps.append(None)
            if len(out) >= n:
                break
        return out, lps, top
    return run


# ---------------------------------------------------------------- Ablauf
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--slots", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--model", default="mlx-community/DeepSeek-Prover-V2-7B-4bit")
    ap.add_argument("--max-new", type=int, default=32)
    ap.add_argument("--limit", type=int, default=0, help="nur die ersten N (Test)")
    ap.add_argument("--lauf1", default="", help="Ergebnisdatei von Lauf 1 (nur Diagnose)")
    a = ap.parse_args()

    slots = [json.loads(l) for l in open(a.slots, encoding="utf-8")]
    all_slots = slots
    if a.limit:
        slots = slots[:a.limit]

    done = set()
    if os.path.exists(a.out) and os.path.getsize(a.out) > 0:
        with open(a.out, encoding="utf-8") as fh:
            first = json.loads(fh.readline())
            if first.get("tokenisierung") != MARK:
                sys.exit(f"ABBRUCH: {a.out} stammt aus einem anderen Lauf "
                         f"(keine Markierung '{MARK}'). Bitte anderen --out wählen.")
            for l in fh:
                try:
                    o = json.loads(l)
                    if "id" in o:
                        done.add(o["id"])
                except json.JSONDecodeError:
                    pass
    todo = [s for s in slots if s["id"] not in done]
    print(f"{len(slots)} Lücken, {len(done)} schon erledigt, {len(todo)} offen", flush=True)
    if not todo:
        print("nichts zu tun.")
        return

    # 1) Tokenizer direkt aus tokenizer.json + Selbsttest, BEVOR das Modell lädt
    mdir = model_dir(a.model)
    raw, info = load_raw_tokenizer(mdir)
    print(f"Tokenizer: tokenizer.json  Vortokenisierung {info['pre_tokenizer']}  "
          f"Dekoder {info['decoder']}  BOS {info['bos']!r}={info['bos_id']}  "
          f"EOS {info['eos']!r}={info['eos_id']}", flush=True)
    bad, n_norm = selftest(raw, info, all_slots)
    if bad:
        sid, p, back = bad[0]
        print(f"\nSELBSTTEST FEHLGESCHLAGEN: {len(bad)} von {len(all_slots)} Präfixen "
              f"kommen nicht unverändert zurück.\n  Lücke {sid}\n  Präfix:  {p[-150:]!r}\n"
              f"  zurück:  {back[-150:]!r}\nKeine Generierung. Bitte diese Ausgabe an Claude.")
        sys.exit(2)
    print(f"Selbsttest bestanden: alle {len(all_slots)} Präfixe verlustfrei "
          f"(Normalisierung änderte {n_norm}).", flush=True)
    selbsttest = dict(praefixe=len(all_slots), verlustfrei=len(all_slots),
                      durch_normalisierung_geaendert=n_norm)

    vergleich = None
    if not done:
        vergleich = compare_with_transformers(raw, info, mdir, all_slots, a.lauf1)
        if "fehler" not in vergleich:
            print(f"Zum Vergleich, AutoTokenizer wie in Lauf 1 ({vergleich['transformers_klasse']}): "
                  f"{vergleich['praefixe_anders']} von {vergleich['praefixe']} Präfixen anders "
                  f"tokenisiert, {vergleich['verlorene_zeichen']} von {vergleich['zeichen']} "
                  f"Zeichen verloren.", flush=True)
            if vergleich.get("lauf1_promptlaenge_reproduziert"):
                print(f"  Promptlängen von Lauf 1 damit reproduziert: "
                      f"{vergleich['lauf1_promptlaenge_reproduziert']}", flush=True)
            if vergleich.get("beispiel"):
                sid, p, seen = vergleich["beispiel"]
                print(f"  Beispiel Lücke {sid}\n    Text:          {p[-90:]!r}\n"
                      f"    Lauf 1 sah:    {seen[-90:]!r}", flush=True)

    # 2) Modell laden und generieren
    print(f"\nlade {a.model} …", flush=True)
    run = make_generate(a.model)
    eos_ids = [info["eos_id"]] if info["eos_id"] is not None else []
    with open(a.out, "a", encoding="utf-8") as fh:
        if not done:
            fh.write(json.dumps({"meta": env_info(), "model": a.model,
                                 "max_new": a.max_new, "decoding": "greedy",
                                 "tokenisierung": MARK, "tokenizer": info,
                                 "selbsttest": selbsttest,
                                 "vergleich_lauf1_tokenisierung": vergleich,
                                 "started": time.strftime("%Y-%m-%d %H:%M:%S")},
                                ensure_ascii=False) + "\n")
        t0 = time.time()
        for i, s in enumerate(todo):
            prefix = s["prefix"].rstrip(" \t")
            ids = encode(raw, info, prefix)
            t = time.time()
            gen, lps, top = run(ids, a.max_new, eos_ids)
            cont = raw.decode(gen, skip_special_tokens=False)
            fh.write(json.dumps({"id": s["id"], "cont": cont, "ids": gen, "lp": lps,
                                 "top5_schritt1": top, "n_prompt": len(ids),
                                 "sec": round(time.time() - t, 2)},
                                ensure_ascii=False) + "\n")
            fh.flush()
            if i < 5:
                seen = raw.decode(ids[-24:], skip_special_tokens=False).replace("\n", "⏎")
                print(f"  [{s['id']}] Modell sieht …{seen[-70:]}  ⟶  {cont[:60]!r}", flush=True)
            elif (i + 1) % 25 == 0 or i + 1 == len(todo):
                el = time.time() - t0
                rest = el / (i + 1) * (len(todo) - i - 1)
                print(f"  {i+1}/{len(todo)}  {el/60:.1f} min  noch ~{rest/60:.0f} min", flush=True)
    print(f"\nfertig -> {a.out}")


if __name__ == "__main__":
    main()
