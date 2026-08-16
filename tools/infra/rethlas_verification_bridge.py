#!/usr/bin/env python3
"""Normalize Rethlas verification reports into local audit telemetry.

Rethlas verifies natural-language markdown proof blueprints with a strict JSON
contract.  This bridge preserves that contract as Hive/audit telemetry while
keeping the authority boundary explicit: a Rethlas verdict is an NL proof-audit
signal, not a Lean kernel proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[2]
_SRC = ROOT / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from igf.common.hashing import stable_hash


SCHEMA = "info_geometry.rethlas_verification_report.v1"
SUMMARY_SCHEMA = "info_geometry.rethlas_verification_bridge.summary.v1"


def iter_json_docs(path: Path) -> Iterable[tuple[dict[str, Any], Path]]:
    if path.is_dir():
        for child in sorted(path.rglob("*.json")):
            yield from iter_json_docs(child)
        return
    if not path.exists() or path.suffix.lower() != ".json":
        return
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return
    if isinstance(payload, dict):
        yield payload, path
    elif isinstance(payload, list):
        for row in payload:
            if isinstance(row, dict):
                yield row, path


def _findings(report: dict[str, Any], key: str) -> list[dict[str, Any]]:
    rows = report.get(key)
    if not isinstance(rows, list):
        return []
    out = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        location = str(row.get("location") or "").strip()
        issue = str(row.get("issue") or "").strip()
        if not location or not issue:
            continue
        out.append(
            {
                "location": location,
                "issue": issue,
                "severity": row.get("severity"),
                "evidence": row.get("evidence"),
            }
        )
    return out


def validate_rethlas_payload(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    report = payload.get("verification_report")
    verdict = payload.get("verdict")
    repair_hints = payload.get("repair_hints")

    if not isinstance(report, dict):
        return ["verification_report must be an object"]

    critical_errors = _findings(report, "critical_errors")
    gaps = _findings(report, "gaps")
    has_findings = bool(critical_errors or gaps)

    if verdict not in {"correct", "wrong"}:
        errors.append("verdict must be 'correct' or 'wrong'")
    if verdict == "correct" and has_findings:
        errors.append("verdict='correct' is invalid when critical_errors or gaps are non-empty")
    if verdict == "correct" and repair_hints != "":
        errors.append("repair_hints must be empty when verdict='correct'")
    if verdict == "wrong" and not has_findings:
        errors.append("verdict='wrong' requires at least one critical error or gap")
    if verdict == "wrong" and (not isinstance(repair_hints, str) or not repair_hints.strip()):
        errors.append("repair_hints must be non-empty when verdict='wrong'")
    return errors


def normalize_rethlas_payload(payload: dict[str, Any], source_path: Path) -> dict[str, Any]:
    report = payload.get("verification_report") if isinstance(payload.get("verification_report"), dict) else {}
    critical_errors = _findings(report, "critical_errors")
    gaps = _findings(report, "gaps")
    validation_errors = validate_rethlas_payload(payload)
    normalized = {
        "schema": SCHEMA,
        "id": "",
        "source": "rethlas",
        "source_path": str(source_path),
        "verdict": payload.get("verdict"),
        "valid_contract": not validation_errors,
        "contract_errors": validation_errors,
        "summary": str(report.get("summary") or ""),
        "critical_errors": critical_errors,
        "gaps": gaps,
        "repair_hints": payload.get("repair_hints") if isinstance(payload.get("repair_hints"), str) else "",
        "finding_count": len(critical_errors) + len(gaps),
        "authority": {
            "nl_verification_is_audit_signal": True,
            "not_a_lean_proof": True,
            "lean_remains_proof_authority": True,
        },
    }
    normalized["id"] = stable_hash(
        {
            "source_path": str(source_path),
            "verdict": normalized["verdict"],
            "summary": normalized["summary"],
            "critical_errors": critical_errors,
            "gaps": gaps,
        }
    )
    return normalized


def run_bridge(input_path: Path, output_dir: Path) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    rows = [
        normalize_rethlas_payload(payload, source_path)
        for payload, source_path in iter_json_docs(input_path)
        if "verification_report" in payload or "verdict" in payload
    ]
    out = output_dir / "rethlas_verification_bridge.jsonl"
    with out.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
    summary = {
        "schema": SUMMARY_SCHEMA,
        "input": str(input_path),
        "output": str(out),
        "records": len(rows),
        "valid_contracts": sum(1 for row in rows if row["valid_contract"]),
        "wrong_verdicts": sum(1 for row in rows if row["verdict"] == "wrong"),
        "correct_verdicts": sum(1 for row in rows if row["verdict"] == "correct"),
        "findings": sum(int(row["finding_count"]) for row in rows),
    }
    summary_path = output_dir / "rethlas_verification_bridge_summary.json"
    summary_path.write_text(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="Rethlas verification JSON file or results directory")
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    summary = run_bridge(args.input, args.output_dir)
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
