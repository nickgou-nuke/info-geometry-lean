#!/usr/bin/env python3
"""Adapter lane for LLM closure-debt audit artifacts.

Converts `tools/quality/llm_closure_debt_auditor.py` outputs into
VerificationRecord JSONL rows for unified verification merge.
"""

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


LANE = "bee_llm_semantic_audit"


def _coerce_rows(payload: Any) -> list[dict[str, Any]]:
    if isinstance(payload, dict):
        files = payload.get("files")
        if isinstance(files, list):
            return [row for row in files if isinstance(row, dict)]
        return [payload]
    if isinstance(payload, list):
        return [row for row in payload if isinstance(row, dict)]
    return []


def _load_input(path: Path) -> list[dict[str, Any]]:
    # Supports jsonl row streams and full json payloads.
    if path.suffix.lower() == ".jsonl":
        return read_json_lines(path)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return []
    return _coerce_rows(payload)


def _decl_from_finding(file_row: dict[str, Any], finding: dict[str, Any], idx: int) -> str:
    module = str(file_row.get("module") or file_row.get("path") or "unknown")
    line = int(finding.get("line_start") or 0)
    category = str(finding.get("category") or "finding")
    return f"{module}::{line}:{category}:{idx}"


def _severity_score(finding: dict[str, Any]) -> int:
    level = str(finding.get("severity") or "advisory").strip().lower()
    if level == "hard":
        return 95
    if level == "soft":
        return 75
    return 40


def _ok(finding: dict[str, Any]) -> bool:
    level = str(finding.get("severity") or "advisory").strip().lower()
    return level not in {"hard", "soft"}


def _evidence(file_row: dict[str, Any], finding: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "path": str(file_row.get("path") or ""),
            "line": int(finding.get("line_start") or 0),
            "snippet": str(finding.get("snippet") or ""),
            "declaration": str(file_row.get("module") or file_row.get("path") or ""),
        }
    ]


def _row_to_contracts(file_row: dict[str, Any]) -> list[dict[str, Any]]:
    findings = file_row.get("findings")
    if not isinstance(findings, list):
        return []

    module = str(file_row.get("module") or "")
    out: list[dict[str, Any]] = []

    for idx, finding in enumerate(findings):
        if not isinstance(finding, dict):
            continue

        category = str(finding.get("category") or "llm-finding")
        source = str(finding.get("source") or "llm")
        ok = _ok(finding)
        reasons = [str(finding.get("why") or "")]
        fix = str(finding.get("fix_strategy") or "")
        if fix:
            reasons.append(f"fix:{fix}")

        checks = [f"llm-audit:{category}", f"llm-source:{source}"]

        payload = VerificationRecord(
            decl=_decl_from_finding(file_row, finding, idx),
            module=module,
            lane=LANE,
            ok=ok,
            severity=_severity_score(finding),
            checks=checks,
            reasons=[r for r in reasons if r],
            evidence=_evidence(file_row, finding),
            provenance={
                "tool": "llm_closure_debt_auditor",
                "source": "llm_file_by_file_reasoning",
                "confidence": float(finding.get("confidence") or 0.0),
                "file_status": str(file_row.get("status") or ""),
            },
            authority_level="heuristic",
        ).to_payload()
        out.append(payload)

    return out


def run(input_path: Path, out_jsonl: Path) -> dict[str, int]:
    rows = _load_input(input_path)
    contracts: list[dict[str, Any]] = []
    for row in rows:
        contracts.extend(_row_to_contracts(row))

    out_jsonl.parent.mkdir(parents=True, exist_ok=True)
    with out_jsonl.open("w", encoding="utf-8") as handle:
        for row in contracts:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")

    return {
        "records": len(contracts),
        "passed": sum(1 for row in contracts if bool(row.get("ok"))),
        "failed": sum(1 for row in contracts if not bool(row.get("ok"))),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-json", type=Path, required=True, help="LLM closure-debt JSON/JSONL input")
    parser.add_argument("--out-jsonl", type=Path, required=True)
    args = parser.parse_args()

    summary = run(args.input_json, args.out_jsonl)
    print(json.dumps(summary, sort_keys=True))
    return 0 if summary["failed"] == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
