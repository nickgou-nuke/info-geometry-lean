#!/usr/bin/env python3
"""Aggregate runner for the Hestenes/Krein complex axis multi-system packet.

Does not run lake, does not update dependencies, and does not touch caches/configs.
"""
from __future__ import annotations
import json
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[2]
RESULTS = ROOT / "results.json"

def find_cmd(*candidates: str) -> str | None:
    for c in candidates:
        if c.startswith("/") and Path(c).exists():
            return c
        got = shutil.which(c)
        if got:
            return got
    return None

def run(name: str, cmd: list[str], marker: str, cwd: Path | None = None, timeout: int = 120) -> dict:
    if not cmd[0]:
        return {"name": name, "status": "missing", "cmd": cmd, "marker": marker}
    try:
        proc = subprocess.run(cmd, cwd=cwd or ROOT, text=True, capture_output=True, timeout=timeout)
        out = (proc.stdout or "") + (proc.stderr or "")
        ok = proc.returncode == 0 and marker in out
        return {"name": name, "status": "ok" if ok else "fail", "returncode": proc.returncode,
                "cmd": cmd, "marker": marker, "output_tail": out[-4000:]}
    except subprocess.TimeoutExpired as e:
        stdout = e.stdout.decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        stderr = e.stderr.decode(errors="replace") if isinstance(e.stderr, bytes) else (e.stderr or "")
        return {"name": name, "status": "timeout", "cmd": cmd, "marker": marker,
                "output_tail": (stdout + stderr)[-4000:]}

python3 = find_cmd("python3")
sage = find_cmd("sage", "/home/goutev/miniforge3/envs/sage/bin/sage")
gap = find_cmd("gap", "/home/goutev/miniforge3/envs/sage/bin/gap")
singular = find_cmd("Singular", "/home/goutev/miniforge3/envs/sage/bin/Singular")
m2 = find_cmd("M2", "Macaulay2")
coqc = find_cmd("coqc")
isabelle = find_cmd("isabelle")

jobs = [
    ("sympy", [python3 or "", str(ROOT / "sympy_hk_complex_axis.py")], "SYMPY_HK_COMPLEX_AXIS_OK", ROOT, 120),
    ("sage", [sage or "", str(ROOT / "sage_hk_complex_axis.sage")], "SAGE_HK_COMPLEX_AXIS_OK", ROOT, 120),
    ("gap", [gap or "", str(ROOT / "gap_hk_complex_axis.g")], "GAP_HK_COMPLEX_AXIS_OK", ROOT, 120),
    ("singular", [singular or "", "-q", str(ROOT / "singular_hk_complex_axis.sing")], "SINGULAR_HK_COMPLEX_AXIS_OK", ROOT, 120),
    ("macaulay2_dmodules", [m2 or "", "--script", str(ROOT / "macaulay2_hk_complex_axis.m2")], "MACAULAY2_DMODULES_HK_COMPLEX_AXIS_OK", ROOT, 180),
    ("coq", [coqc or "", str(ROOT / "HestenesKreinComplexAxis.v")], "", ROOT, 120),
    ("isabelle", [isabelle or "", "build", "-D", str(ROOT)], "", ROOT, 180),
    ("lean_owner_source_audit", [python3 or "", str(ROOT / "lean_owner_source_audit.py")], "LEAN_OWNER_SOURCE_AUDIT_OK", ROOT, 120),
]

results = []
for name, cmd, marker, cwd, timeout in jobs:
    if name in {"coq", "isabelle"}:
        # These tools signal proof success by exit code; no stable stdout marker required.
        marker_for_run = marker or "__EXIT_CODE_ONLY__"
        res = run(name, cmd, marker_for_run, cwd, timeout)
        if res.get("returncode") == 0 and res.get("status") == "fail":
            res["status"] = "ok"
    else:
        res = run(name, cmd, marker, cwd, timeout)
    results.append(res)

RESULTS.write_text(json.dumps(results, indent=2))
for r in results:
    print(f"{r['name']}: {r['status']}")
    if r['status'] != 'ok':
        print(r.get('output_tail','')[-1200:])
if not all(r["status"] == "ok" for r in results):
    raise SystemExit(1)
print("HK_COMPLEX_AXIS_MULTI_SYSTEM_OK")
