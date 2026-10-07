#!/usr/bin/env python3
"""
Kompass mit starkem Modell: Lean prüft die Beweise (aus orakel_pruef.py; längere Fehlermeldungen,
Zeile relativ zum Beweis, bis zu 3 Fehler für die Reparaturrunden).
Der menschliche Beweis (ab `:=`) wird durch den des Modells ersetzt, die Datei
hinter dem Theorem abgeschnitten. Geprüft wird mit denselben Optionen, mit
denen mathlib selbst gebaut wird. (Grundgerüst aus stufe2_lauf.py.)

Status je Prüfung:
  ok        keine Fehlermeldung, kein sorry
  sorry     keine Fehlermeldung, aber `sorry` (zählt nicht als Beweis)
  fehler    Fehler ab der Kopfzeile des Theorems
  basis     Fehler nur VOR dem Theorem (Umgebung/Abschneiden, nicht der Beweis)
  timeout   länger als --timeout Sekunden
  absturz   Lean endete mit Fehlercode, ohne Meldung

Selbsttest zuerst: die unveränderte, abgeschnittene Datei (Variante O) für
die ersten Theoreme muss fehlerfrei sein, sonst Abbruch.

Wiederaufnehmbar: bereits geprüfte (Theorem, Variante) werden übersprungen.
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import json
import os
import re
import subprocess
import sys
import threading
import time
from pathlib import Path

LEAN_OPTS = ["-DmaxSynthPendingDepth=3", "-DautoImplicit=false", "-Dpp.unicode.fun=true"]
TEXT_MSG = re.compile(r"^(?P<file>.+?):(?P<line>\d+):(?P<col>\d+): (?P<sev>error|warning|info)\b")


def build_file(mdir: Path, p: dict, v: dict | None) -> tuple[str, int]:
    """Datei mit dem Beweis des Modells (v) bzw. unverändert abgeschnitten (v = None)."""
    text = (mdir / p["path"]).read_text(encoding="utf-8")
    lines = text.split("\n")
    cut_off = sum(len(l) + 1 for l in lines[:p["cut_line"]])
    if v is None:
        return text[:cut_off], p["decl_line"]
    if text[p["beweis_start"]:p["beweis_start"] + 2] != ":=":
        raise ValueError("':=' nicht an der erwarteten Stelle")
    return text[:p["beweis_start"]] + ":= by\n" + v["beweis"] + "\n", p["decl_line"]


def parse_messages(out: str):
    msgs = []
    for line in out.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith("{"):
            try:
                o = json.loads(line)
                pos = o.get("pos") or {}
                msgs.append(dict(sev=o.get("severity", "?"), line=pos.get("line", 0),
                                 text=str(o.get("data", ""))[:1500]))
                continue
            except json.JSONDecodeError:
                pass
        m = TEXT_MSG.match(line)
        if m:
            msgs.append(dict(sev=m["sev"], line=int(m["line"]), text=line[m.end():][:1500]))
    return msgs


def check(mdir: Path, work: Path, p: dict, vname: str, v: dict | None, timeout: int):
    src, decl_line = build_file(mdir, p, v)
    f = work / f"r{p['id']}_{re.sub(r'[^A-Za-z0-9]', '', vname)}.lean"
    f.write_text(src, encoding="utf-8")
    t = time.time()
    proc = subprocess.Popen(["lake", "env", "lean", *LEAN_OPTS, "--json", str(f)], cwd=mdir,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                            start_new_session=True)       # eigene Prozessgruppe
    try:
        so, se = proc.communicate(timeout=timeout)
        out, code = so + "\n" + se, proc.returncode
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, 9)                        # lake UND lean beenden
        except OSError:
            pass
        proc.communicate()
        try:
            f.unlink()
        except OSError:
            pass
        return dict(id=p["id"], v=vname, status="timeout", sec=round(time.time() - t, 1))
    msgs = parse_messages(out)
    errs = [m for m in msgs if m["sev"] == "error"]
    sorry = any(m["sev"] == "warning" and "sorry" in m["text"] and m["line"] >= decl_line for m in msgs)
    if not errs:
        status = ("sorry" if sorry else "ok") if code == 0 else "absturz"
    elif any(m["line"] >= decl_line for m in errs):
        status = "fehler"
    else:
        status = "basis"
    first = next((m for m in errs if m["line"] >= decl_line), errs[0] if errs else None)
    by_zeile = src[:p["beweis_start"]].count("\n") + 1 if v is not None else decl_line
    res = dict(id=p["id"], v=vname, status=status, n_err=len(errs),
               erste_meldung=(first or {}).get("text", "") if status != "ok" else "",
               zeile=(first or {}).get("line"), sec=round(time.time() - t, 1),
               fehler=[dict(zeile_im_beweis=m["line"] - by_zeile, text=m["text"])
                       for m in errs if m["line"] >= decl_line][:3])
    if status == "absturz":
        res["ausgabe"] = out[-600:]
    try:
        f.unlink()
    except OSError:
        pass
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mathlib", required=True)
    ap.add_argument("--patches", required=True)
    ap.add_argument("--beweise", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--selbsttest", type=int, default=4, help="Anzahl unveränderter Probedateien")
    ap.add_argument("--limit", type=int, default=0)
    a = ap.parse_args()

    mdir = Path(a.mathlib).expanduser().resolve()
    work = mdir / ".stufe2_tmp"
    work.mkdir(exist_ok=True)
    patches = [json.loads(l) for l in open(a.patches, encoding="utf-8")]
    gen, max_new = {}, None
    for l in open(a.beweise, encoding="utf-8"):
        o = json.loads(l)
        if "marke" in o:
            max_new = o.get("max_new")
        if "arm" in o:
            b = o["beweis"]
            # Bei Abbruch durch die Token-Grenze ist die letzte Zeile unvollständig
            # (z. B. "  <;"): sie wird entfernt, der Rest geprüft.
            if not o.get("endgueltig") and max_new and o.get("n_gen", 0) >= max_new and "\n" in b:
                b = b[:b.rfind("\n")].rstrip()
            gen.setdefault(o["id"], []).append(dict(v=f"{o['arm']}#{o['k']}", beweis=b))
    for p in patches:
        p["variants"] = gen.get(p["id"], [])
    patches = [p for p in patches if p["variants"]]
    if a.limit:
        patches = patches[:a.limit]

    done = set()
    if os.path.exists(a.out) and os.path.getsize(a.out) > 0:
        data = open(a.out, "rb").read()
        if not data.endswith(b"\n"):           # halbe letzte Zeile (harter Abbruch) entfernen
            open(a.out, "wb").write(data[:data.rfind(b"\n") + 1])
    if os.path.exists(a.out):
        for l in open(a.out, encoding="utf-8"):
            try:
                o = json.loads(l)
                if o.get("status") not in ("timeout", "skriptfehler"):   # die werden wiederholt
                    done.add((o["id"], o["v"]))
            except (json.JSONDecodeError, KeyError):
                pass

    # 1) Selbsttest: unveränderte Dateien müssen sich prüfen lassen
    probe_ids = [p["id"] for p in patches[:a.selbsttest]]
    probe = [p for p in patches[:a.selbsttest] if (p["id"], "O") not in done]
    if probe:
        print(f"Selbsttest: {len(probe)} unveränderte Dateien …", flush=True)
        with open(a.out, "a", encoding="utf-8") as fh:
            for p in probe:
                r = check(mdir, work, p, "O", None, a.timeout)
                fh.write(json.dumps(r, ensure_ascii=False) + "\n"); fh.flush()
                print(f"  Theorem {p['id']:>4}  {p['path']}  -> {r['status']}  ({r['sec']} s)"
                      + (f"   {r.get('erste_meldung', '')[:150]}" if r["status"] != "ok" else ""),
                      flush=True)
    status_o = {}
    for l in open(a.out, encoding="utf-8"):
        o = json.loads(l)
        if o.get("v") == "O" and o["id"] in probe_ids:
            status_o[o["id"]] = o["status"]
    n_ok = sum(1 for s_ in status_o.values() if s_ == "ok")
    if probe_ids and n_ok < max(1, len(probe_ids) - 1):
        print(f"\nSELBSTTEST FEHLGESCHLAGEN: nur {n_ok} von {len(probe_ids)} unveränderten Dateien "
              f"fehlerfrei ({status_o}). Die Umgebung prüft mathlib nicht korrekt. Keine weiteren "
              "Prüfungen. Bitte diese Ausgabe an Claude.")
        sys.exit(2)
    print(f"Selbsttest bestanden ({n_ok} von {len(probe_ids)} unveränderten Dateien fehlerfrei).\n",
          flush=True)

    # 2) Beweise des Modells
    jobs = [(p, v["v"], v) for p in patches for v in p["variants"] if (p["id"], v["v"]) not in done]
    a.workers = max(a.workers, min(4, (os.cpu_count() or 4) // 2))   # Modellbeweise prüfen sich langsamer
    print(f"{len(jobs)} Beweise zu prüfen, {a.workers} parallel.", flush=True)
    lock = threading.Lock()
    t0, n, stats = time.time(), 0, {}
    with open(a.out, "a", encoding="utf-8") as fh, cf.ThreadPoolExecutor(a.workers) as ex:
        futs = {ex.submit(check, mdir, work, p, vn, v, a.timeout): (p, vn) for p, vn, v in jobs}
        for fut in cf.as_completed(futs):
            p, vn = futs[fut]
            try:
                r = fut.result()
            except Exception as e:                      # noqa: BLE001
                r = dict(id=p["id"], v=vn, status="skriptfehler", fehler=repr(e)[:300])
            with lock:
                fh.write(json.dumps(r, ensure_ascii=False) + "\n"); fh.flush()
                n += 1
                arm = vn.split("#")[0]
                stats[(arm, r["status"])] = stats.get((arm, r["status"]), 0) + 1
                if n % 10 == 0 or n == len(jobs):
                    el = time.time() - t0
                    ok = sum(v for (_, st), v in stats.items() if st == "ok")
                    print(f"  {n}/{len(jobs)}  {el/60:.0f} min, noch ~{el/n*(len(jobs)-n)/60:.0f} min"
                          f"   bewiesen bisher: {ok}", flush=True)
    print(f"\nfertig -> {a.out}")
    for k in sorted(stats):
        print(f"  {k[0]:<26} {k[1]:<10} {stats[k]}")


if __name__ == "__main__":
    main()
