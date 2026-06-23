#!/usr/bin/env python3
"""Bounded Macaulay2 Bernstein-Sato probes for the D=4 de Rham audit lane.

This complements the heavy `deRham` / `Dlocalize + rationalFunctionExt` runs with
smaller D-module probes that can still yield exact certificates without asking
Macaulay2 to complete the full localization of the 8-variable complement.

Current probes:
1. global Bernstein-Sato polynomial of each individual quadric factor;
2. generalized Bernstein-Sato polynomial of the three-factor ideal
   `{q(a), q(b), q(a-b)}`;
3. optional global Bernstein-Sato polynomial of the full product
   `f = q(a) q(b) q(a-b)` under a bounded timeout.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[3]
ARTIFACT_DIR = ROOT / "artifacts" / "de_rham_klein_quadric"
DEFAULT_OUTPUT = ARTIFACT_DIR / "m2_surgical_probe.json"


def now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def normalize_output(data: str | bytes | None) -> str:
    if data is None:
        return ""
    if isinstance(data, bytes):
        return data.decode(errors="replace")
    return data


def run_m2_script(m2_path: str, script_text: str, timeout: int) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as td:
        script_path = Path(td) / "_m2_surgical_probe.m2"
        script_path.write_text(script_text, encoding="utf-8")
        start = time.time()
        try:
            cp = subprocess.run(
                [m2_path, "--script", str(script_path)],
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                timeout=timeout,
                check=False,
            )
            elapsed = time.time() - start
            return {
                "status": "ok" if cp.returncode == 0 else "error",
                "returncode": cp.returncode,
                "timed_out": False,
                "elapsed_seconds": round(elapsed, 3),
                "stdout": cp.stdout,
                "script_path": str(script_path),
            }
        except subprocess.TimeoutExpired as exc:
            elapsed = time.time() - start
            return {
                "status": "timeout",
                "returncode": 124,
                "timed_out": True,
                "elapsed_seconds": round(elapsed, 3),
                "stdout": normalize_output(exc.stdout),
                "script_path": str(script_path),
            }


def factor_scripts() -> dict[str, str]:
    common_header = """
needsPackage \"BernsteinSato\";
R = QQ[a1,a2,a3,a4,b1,b2,b3,b4];
qa = a1^2 + a2^2 + a3^2 + a4^2;
qb = b1^2 + b2^2 + b3^2 + b4^2;
qab = (a1-b1)^2 + (a2-b2)^2 + (a3-b3)^2 + (a4-b4)^2;
""".strip()

    factor_script = common_header + """
for pair in {{\"qa\",qa},{\"qb\",qb},{\"qab\",qab}} list (
  name := pair#0;
  poly := pair#1;
  << \"SURGICAL:factor:start:\" << name << endl;
  time bpoly = globalBFunction poly;
  << \"SURGICAL:factor:raw:\" << name << \"=\" << toString bpoly << endl;
  << \"SURGICAL:factor:factored:\" << name << \"=\" << toString factorBFunction bpoly << endl;
);
"""

    components_script = common_header + """
<< \"SURGICAL:components:start\" << endl;
time bgen = generalB {qa,qb,qab};
<< \"SURGICAL:components:raw=\" << toString bgen << endl;
<< \"SURGICAL:components:factored=\" << toString factorBFunction bgen << endl;
"""

    product_script = common_header + """
f = qa*qb*qab;
<< \"SURGICAL:product:start\" << endl;
time bprod = globalBFunction f;
<< \"SURGICAL:product:raw=\" << toString bprod << endl;
<< \"SURGICAL:product:factored=\" << toString factorBFunction bprod << endl;
"""

    return {
        "global_b_each_factor": factor_script,
        "generalB_components": components_script,
        "global_b_product": product_script,
    }


def parse_factor_probe(stdout: str) -> dict[str, Any]:
    raw = dict(re.findall(r"SURGICAL:factor:raw:([^=\n]+)=([^\n]+)", stdout))
    factored = dict(re.findall(r"SURGICAL:factor:factored:([^=\n]+)=([^\n]+)", stdout))
    return {
        "raw": raw,
        "factored": factored,
        "completed_factors": sorted(set(raw) & set(factored)),
    }


def parse_single_probe(stdout: str, prefix: str) -> dict[str, Any]:
    out: dict[str, Any] = {}
    m_raw = re.search(rf"SURGICAL:{prefix}:raw=([^\n]+)", stdout)
    m_factored = re.search(rf"SURGICAL:{prefix}:factored=([^\n]+)", stdout)
    if m_raw:
        out["raw"] = m_raw.group(1)
    if m_factored:
        out["factored"] = m_factored.group(1)
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT), help="JSON artifact path")
    parser.add_argument(
        "--factor-timeout",
        type=int,
        default=60,
        help="Timeout in seconds for the per-factor global Bernstein-Sato probe",
    )
    parser.add_argument(
        "--components-timeout",
        type=int,
        default=60,
        help="Timeout in seconds for the generalized Bernstein-Sato components probe",
    )
    parser.add_argument(
        "--product-timeout",
        type=int,
        default=120,
        help="Timeout in seconds for the full-product global Bernstein-Sato probe",
    )
    args = parser.parse_args()

    m2_path = shutil.which("M2") or shutil.which("m2-stack") or shutil.which("Macaulay2")
    artifact_path = Path(args.output)
    artifact_path.parent.mkdir(parents=True, exist_ok=True)

    payload: dict[str, Any] = {
        "schema": "de_rham_klein_quadric.m2_surgical_probe.v1",
        "generatedAt": now_iso(),
        "cwd": str(ROOT),
        "engine": "Macaulay2/BernsteinSato",
        "probes": {},
    }

    if m2_path is None:
        payload["status"] = "missing-backend"
        payload["message"] = "M2 binary not found in PATH"
        artifact_path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
        print(artifact_path)
        print(json.dumps({"status": payload["status"]}))
        return 1

    payload["m2_path"] = m2_path

    scripts = factor_scripts()
    probe_timeouts = {
        "global_b_each_factor": args.factor_timeout,
        "generalB_components": args.components_timeout,
        "global_b_product": args.product_timeout,
    }

    for name, script_text in scripts.items():
        result = run_m2_script(m2_path, script_text, probe_timeouts[name])
        row: dict[str, Any] = {
            "status": result["status"],
            "returncode": result["returncode"],
            "timed_out": result["timed_out"],
            "elapsed_seconds": result["elapsed_seconds"],
            "timeout_seconds": probe_timeouts[name],
            "script_path": result["script_path"],
            "stdout_tail": "\n".join(result["stdout"].splitlines()[-12:]),
        }
        if name == "global_b_each_factor":
            row["parsed"] = parse_factor_probe(result["stdout"])
        elif name == "generalB_components":
            row["parsed"] = parse_single_probe(result["stdout"], "components")
        else:
            row["parsed"] = parse_single_probe(result["stdout"], "product")
        row["is_verified"] = bool(row["parsed"]) and row["status"] == "ok"
        payload["probes"][name] = row

    payload["status"] = "ok"
    payload["summary"] = {
        "completed": [k for k, v in payload["probes"].items() if v["status"] == "ok"],
        "timed_out": [k for k, v in payload["probes"].items() if v["status"] == "timeout"],
        "errored": [k for k, v in payload["probes"].items() if v["status"] == "error"],
        "verified": [k for k, v in payload["probes"].items() if v["is_verified"]],
    }

    artifact_path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    print(artifact_path)
    print(json.dumps(payload["summary"], sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
