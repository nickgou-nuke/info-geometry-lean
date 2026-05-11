#!/usr/bin/env python3
"""Optional wrapper for Rethlas reference/proof verification outputs."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    ROOT = Path(__file__).resolve().parents[3]
    sys.path.insert(0, str(ROOT))

from tools.infra.verification_contract import VerificationRecord, read_json_lines


LANE = "bee_rethlas_refs"


def _row_to_contract(row: dict[str, Any]) -> dict[str, Any] | None:
    verdict = str(row.get("verdict") or "").strip().lower()
    if not verdict:
        return None

    report = row.get("verification_report")
    summary = ""
    if isinstance(report, dict):
        summary = str(report.get("summary") or "")

    # Declare failure whenever the verdict is "wrong".
    ok = verdict == "correct"
    reasons = []
    if not ok:
        repair_hints = row.get("repair_hints")
        if isinstance(repair_hints, str):
            reasons.append(repair_hints)
        if not reasons:
            reasons.append("rethlas_verdict:wrong")
    else:
        reasons.append("rethlas_verdict:correct")

    checks = ["rethlas-verdict"]
    if summary:
        checks.append("rethlas-summary")

    return VerificationRecord(
        decl=str(row.get("decl") or row.get("declaration") or row.get("theorem") or "unknown"),
        module=str(row.get("module") or row.get("file") or ""),
        lane=LANE,
        ok=ok,
        severity=90 if not ok else 0,
        checks=checks,
        reasons=reasons,
        evidence=[
            {
                "path": str(row.get("source_path") or ""),
                "line": 0,
                "snippet": summary,
                "declaration": str(row.get("decl") or ""),
            }
        ],
        provenance={
            "tool": "rethlas",
            "schema": str(row.get("schema") or ""),
            "source": "rethlas_verification_bridge",
            "valid_contract": bool(row.get("valid_contract", True)),
        },
        authority_level="heuristic",
    ).to_payload()


def run(input_path: Path, out_jsonl: Path) -> dict[str, int]:
    rows = []
    for row in read_json_lines(input_path):
        contract_row = _row_to_contract(row)
        if contract_row:
            rows.append(contract_row)
    out_jsonl.parent.mkdir(parents=True, exist_ok=True)
    with out_jsonl.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
    return {"records": len(rows), "passed": sum(1 for row in rows if bool(row.get("ok"))), "failed": sum(1 for row in rows if not bool(row.get("ok")))}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-json", type=Path, required=True, help="Rethlas JSON/JSONL input (bridge format)")
    parser.add_argument("--out-jsonl", type=Path, required=True)
    args = parser.parse_args()
    summary = run(args.input_json, args.out_jsonl)
    print(json.dumps(summary, sort_keys=True))
    return 0 if summary["failed"] == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
