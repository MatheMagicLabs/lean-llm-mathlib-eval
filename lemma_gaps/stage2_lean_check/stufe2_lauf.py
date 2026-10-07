#!/usr/bin/env python3
"""
Lückenexperiment, Stufe 2: Lean-Prüfung der Ersatzwahlen (explorativ).

Für jede Lücke, in der das Modell ein ANDERES existierendes Lemma gewählt hat
als der Mensch, wird die Wahl des Modells an die Stelle der menschlichen
gesetzt (Variante S) und die Datei mit Lean geprüft. In simp/grind-
Hinweislisten zusätzlich die Kontrolle D: der Hinweis ganz gestrichen.

Die Datei wird hinter dem betroffenen Theorem abgeschnitten (spätere
Deklarationen braucht es nicht). Geprüft wird mit denselben Optionen, mit
denen mathlib selbst gebaut wird.

Status je Prüfung:
  ok        keine Fehlermeldung
  fehler    Fehler ab der Kopfzeile des Theorems (die Datei endet danach)
  basis     Fehler nur VOR dem Theorem (Umgebung/Abschneiden, nicht die Wahl)
  timeout   länger als --timeout Sekunden
  absturz   Lean endete mit Fehlercode, ohne Meldung

Selbsttest zuerst: die unveränderte, abgeschnittene Datei (Variante O) für
die ersten Lücken muss fehlerfrei sein, sonst Abbruch.

Wiederaufnehmbar: bereits geprüfte (Lücke, Variante) werden übersprungen.
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
    """Text der geänderten, abgeschnittenen Datei und Zeilennummer des Theorems."""
    text = (mdir / p["path"]).read_text(encoding="utf-8")
    lines = text.split("\n")
    cut_off = sum(len(l) + 1 for l in lines[:p["cut_line"]])
    if v is None:                                     # Variante O: unverändert
        return text[:cut_off], p["decl_line"]
    if text[v["start"]:v["end"]] != v["expect"]:
        raise ValueError(f"erwarteter Text fehlt an der Stelle: {v['expect']!r}")
    return text[:v["start"]] + v["repl"] + text[v["end"]:cut_off], p["decl_line"]


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
                                 text=str(o.get("data", ""))[:400]))
                continue
            except json.JSONDecodeError:
                pass
        m = TEXT_MSG.match(line)
        if m:
            msgs.append(dict(sev=m["sev"], line=int(m["line"]), text=line[m.end():][:400]))
    return msgs


def check(mdir: Path, work: Path, p: dict, vname: str, v: dict | None, timeout: int):
    src, decl_line = build_file(mdir, p, v)
    f = work / f"s{p['id']}_{vname}.lean"
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
    if not errs:
        status = "ok" if code == 0 else "absturz"
    elif any(m["line"] >= decl_line for m in errs):
        status = "fehler"
    else:
        status = "basis"
    first = next((m for m in errs if m["line"] >= decl_line), errs[0] if errs else None)
    res = dict(id=p["id"], v=vname, status=status, n_err=len(errs),
               erste_meldung=(first or {}).get("text", "") if status != "ok" else "",
               zeile=(first or {}).get("line"), sec=round(time.time() - t, 1))
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
    ap.add_argument("--out", required=True)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--timeout", type=int, default=1200)
    ap.add_argument("--selbsttest", type=int, default=4, help="Anzahl unveränderter Probedateien")
    ap.add_argument("--limit", type=int, default=0)
    a = ap.parse_args()

    mdir = Path(a.mathlib).expanduser().resolve()
    work = mdir / ".stufe2_tmp"
    work.mkdir(exist_ok=True)
    patches = [json.loads(l) for l in open(a.patches, encoding="utf-8")]
    if a.limit:
        patches = patches[:a.limit]

    done = set()
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
                print(f"  Lücke {p['id']:>4}  {p['path']}  -> {r['status']}  ({r['sec']} s)"
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

    # 2) Ersatz S und Kontrolle D
    jobs = [(p, v["v"], v) for p in patches for v in p["variants"] if (p["id"], v["v"]) not in done]
    print(f"{len(jobs)} Prüfungen offen ({sum(1 for j in jobs if j[1] == 'S')} Ersatz, "
          f"{sum(1 for j in jobs if j[1] == 'D')} Kontrolle), {a.workers} parallel.", flush=True)
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
                stats[(vn, r["status"])] = stats.get((vn, r["status"]), 0) + 1
                if n % 10 == 0 or n == len(jobs):
                    el = time.time() - t0
                    s_ok = stats.get(("S", "ok"), 0)
                    s_all = sum(v for (vv, _), v in stats.items() if vv == "S")
                    print(f"  {n}/{len(jobs)}  {el/60:.0f} min, noch ~{el/n*(len(jobs)-n)/60:.0f} min"
                          f"   Ersatz ok bisher: {s_ok}/{s_all}", flush=True)
    print(f"\nfertig -> {a.out}")
    for k in sorted(stats):
        print(f"  {k[0]}  {k[1]:<12} {stats[k]}")


if __name__ == "__main__":
    main()
