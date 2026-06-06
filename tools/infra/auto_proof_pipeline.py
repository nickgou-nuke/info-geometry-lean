#!/usr/bin/env python3
"""Run the resurrected auto proof lane as an auditable local pipeline.

The pipeline is intentionally staged:
1. strict SymPy witness extraction/execution
2. optional Lean single-file compile checks
3. optional vacuity-linter checks

It writes a JSON report and does not write to ArangoDB. Use
tools/infra/aiclaw_auto_arango.py for isolated proof-memory ingestion.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DEFAULT_REPORT = Path("artifacts/auto_sympy/pipeline_report.json")
DEFAULT_WITNESS_MANIFEST = Path("artifacts/auto_sympy/resurrected_witnesses.json")


def run(cmd: list[str], timeout: int) -> dict[str, Any]:
    try:
        proc = subprocess.run(cmd, text=True, capture_output=True, timeout=timeout)
        return {
            "cmd": cmd,
            "returncode": proc.returncode,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
            "result": "pass" if proc.returncode == 0 else "fail",
        }
    except subprocess.TimeoutExpired as exc:
        return {
            "cmd": cmd,
            "returncode": None,
            "stdout": exc.stdout or "",
            "stderr": exc.stderr or "",
            "result": "timeout",
        }


def lean_checks(proof_dir: Path, timeout: int) -> list[dict[str, Any]]:
    records = []
    if not proof_dir.exists():
        return records
    for path in sorted(proof_dir.glob("*.lean")):
        record = run(["lake", "env", "lean", str(path)], timeout)
        record["file"] = str(path)
        records.append(record)
    return records


def vacuity_checks(proof_dir: Path, timeout: int) -> list[dict[str, Any]]:
    records = []
    linter = Path("scripts/vacuity-linter.py")
    if not proof_dir.exists() or not linter.exists():
        return records
    for path in sorted(proof_dir.glob("*.lean")):
        record = run([sys.executable, str(linter), "--json", str(path)], timeout)
        record["file"] = str(path)
        if record["returncode"] == 0:
            try:
                record["json"] = json.loads(record["stdout"])
            except json.JSONDecodeError:
                record["json_parse_error"] = True
        records.append(record)
    return records


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", default=None, help="Knowledge base JSON passed to auto_sympy_witnesses.py.")
    parser.add_argument("--proof-dir", default="proofs")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--witness-manifest", default=str(DEFAULT_WITNESS_MANIFEST))
    parser.add_argument("--witness-timeout", type=int, default=30)
    parser.add_argument("--lean-timeout", type=int, default=45)
    parser.add_argument("--skip-lean", action="store_true")
    parser.add_argument("--skip-vacuity", action="store_true")
    parser.add_argument("--strict", action="store_true", help="Exit nonzero on witness or Lean failures.")
    args = parser.parse_args()

    witness_cmd = [
        sys.executable,
        "tools/infra/auto_sympy_witnesses.py",
        "--run",
        "--manifest",
        args.witness_manifest,
        "--timeout",
        str(args.witness_timeout),
    ]
    if args.source:
        witness_cmd.extend(["--source", args.source])

    witness_run = run(witness_cmd, timeout=max(60, args.witness_timeout * 20))
    witness_manifest: dict[str, Any] | None = None
    manifest_path = Path(args.witness_manifest)
    if manifest_path.exists():
        witness_manifest = json.loads(manifest_path.read_text(encoding="utf-8"))

    proof_dir = Path(args.proof_dir)
    lean = [] if args.skip_lean else lean_checks(proof_dir, args.lean_timeout)
    vacuity = [] if args.skip_vacuity else vacuity_checks(proof_dir, 10)

    report = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "witness_run": witness_run,
        "witness_manifest": witness_manifest,
        "lean": lean,
        "vacuity": vacuity,
    }
    report_path = Path(args.report)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    witness_failed = False
    if witness_manifest:
        witness_failed = bool(witness_manifest.get("summary", {}).get("failed"))
    lean_failed = any(item["result"] != "pass" for item in lean)

    print(
        json.dumps(
            {
                "report": str(report_path),
                "witness_failed": witness_failed,
                "lean_failed": lean_failed,
                "lean_checked": len(lean),
                "vacuity_checked": len(vacuity),
            },
            indent=2,
        )
    )
    if args.strict and (witness_failed or lean_failed):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
