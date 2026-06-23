#!/usr/bin/env python3
"""Reproducible external audit wrapper for the MDPAS/Souriau de Rham lane.

This wrapper runs three bounded Macaulay2-backed audit configurations for the
Klein-quadric-like complement used as the external de Rham obstruction lane:

1. `deRham(0, f)` probe,
2. full `deRham(f)` probe,
3. `Dlocalize + rationalFunctionExt` probe.

It preserves the finite-field, Singular, and Sage cross-checks provided by the
underlying harness and writes a manifest pointing at the generated JSON
artifacts.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HARNESS = ROOT / "scripts" / "experiments" / "DeRhamKleinQuadric" / "audit_rank32.py"
ARTIFACT_DIR = ROOT / "artifacts" / "de_rham_klein_quadric"
MANIFEST = ARTIFACT_DIR / "mdpas_global_audit_manifest.json"

RUNS = {
    "degree0": [
        "--fields", "3,5,7",
        "--self-check",
        "--m2-derham",
        "--m2-degree", "0",
        "--m2-timeout", "120",
        "--out", str(ARTIFACT_DIR / "mdpas_degree0_audit.json"),
    ],
    "full_derham": [
        "--fields", "3,5,7",
        "--m2-derham",
        "--m2-timeout", "120",
        "--out", str(ARTIFACT_DIR / "mdpas_full_derham_audit.json"),
    ],
    "dlocalize_ext": [
        "--fields", "3,5,7",
        "--m2-derham",
        "--m2-method", "dlocalize-ext",
        "--m2-timeout", "120",
        "--out", str(ARTIFACT_DIR / "mdpas_dlocalize_ext_audit.json"),
    ],
}


def run_one(name: str, args: list[str]) -> dict:
    cmd = ["python3", str(HARNESS), *args]
    proc = subprocess.run(
        cmd,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    out_path = Path(args[-1])
    payload = json.loads(out_path.read_text()) if out_path.exists() else None
    return {
        "command": cmd,
        "returncode": proc.returncode,
        "artifact": str(out_path),
        "summary": payload.get("summary") if payload is not None else None,
        "tail": "\n".join(proc.stdout.splitlines()[-6:]),
    }


def main() -> None:
    ARTIFACT_DIR.mkdir(parents=True, exist_ok=True)
    manifest = {name: run_one(name, args) for name, args in RUNS.items()}
    MANIFEST.write_text(json.dumps(manifest, indent=2))
    print(MANIFEST)
    print(json.dumps({name: row["summary"] for name, row in manifest.items()}, indent=2))


if __name__ == "__main__":
    main()
