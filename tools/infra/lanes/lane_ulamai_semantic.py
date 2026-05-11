#!/usr/bin/env python3
"""Deterministic semantic guard lane adapter (ULAMAI-like deterministic checks)."""

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


LANE = "bee_semantic_guard"


RISKY_CLASSES = {
    "blocked",
    "vacuous_or_surrogate",
    "needs_review_named_bridge",
    "needs_review_external_audit_failed",
    "audit_missing",
    "explicit_axiom",
    "kernel_definition",
    "diagnostic_only",
    "graph_only",
}


def _extract_decl(row: dict[str, Any]) -> str:
    for key in (
        "name",
        "decl",
        "declaration",
        "fullName",
        "full_name",
        "theorem",
        "target_decl",
    ):
        value = row.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return "unknown"


def _extract_class(row: dict[str, Any]) -> str:
    for key in ("classification", "class", "status", "reason_class", "category"):
        value = row.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""


def _evidence(row: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "path": str(row.get("file") or row.get("path") or ""),
            "line": int(row.get("line") or row.get("line_number") or 0),
            "snippet": str(row.get("source_block") or ""),
            "declaration": _extract_decl(row),
        }
    ]


def row_to_contract(row: dict[str, Any]) -> dict[str, Any]:
    decl = _extract_decl(row)
    classification = _extract_class(row)
    blocked = bool(classification in RISKY_CLASSES or row.get("blocked") or row.get("unsafe"))
    module = str(row.get("module") or row.get("module_name") or "")
    reasons = []
    if classification:
        reasons.append(f"classification:{classification}")
    reasons.extend(str(item) for item in (row.get("reasons") or []) if isinstance(item, (str, int, float)))
    checks = ["semantic-guard"]
    if classification:
        checks.append(f"semantic:{classification}")
    return VerificationRecord(
        decl=decl,
        module=module,
        lane=LANE,
        ok=not blocked,
        severity=100 if classification in {"blocked", "explicit_axiom", "needs_review_external_audit_failed"} else (80 if blocked else 0),
        checks=checks,
        reasons=reasons or ["passed"],
        evidence=_evidence(row),
        provenance={
            "tool": "ulamai_semantic_guard",
            "version": str(row.get("schema") or ""),
            "source": "deterministic_semantic_guard",
            "mode": "heuristic_default",
        },
        authority_level="heuristic",
    ).to_payload()


def run(input_path: Path, out_jsonl: Path) -> dict[str, int]:
    rows = [row_to_contract(row) for row in read_json_lines(input_path)]
    out_jsonl.parent.mkdir(parents=True, exist_ok=True)
    with out_jsonl.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
    return {"records": len(rows), "passed": sum(1 for row in rows if bool(row.get("ok"))), "failed": sum(1 for row in rows if not bool(row.get("ok")))}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-json", type=Path, required=True, help="Source mathliness-like or semantic audit artifact (JSON/JSONL)")
    parser.add_argument("--out-jsonl", type=Path, required=True)
    args = parser.parse_args()
    summary = run(args.input_json, args.out_jsonl)
    print(json.dumps(summary, sort_keys=True))
    return 0 if summary["failed"] == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
