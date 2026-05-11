#!/usr/bin/env python3
"""Adapter lane for Lean-native semantic conductivity/audit artifacts."""

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


LANE = "bee_lean_conductivity"


DECL_KEYS = (
    "decl",
    "declaration",
    "declaration_name",
    "name",
    "fullName",
    "full_name",
    "theorem",
    "target_decl",
    "target_name",
)


def _to_float(value: Any, *, default: float = 0.0) -> float:
    try:
        return float(value)
    except Exception:
        return default


def _first_string(row: dict[str, Any], keys: tuple[str, ...] = DECL_KEYS) -> str:
    for key in keys:
        value = row.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    nested = row.get("target_info") or row.get("solution_info") or row.get("targetInfo") or row.get("solutionInfo")
    if isinstance(nested, dict):
        nested_name = nested.get("name")
        if isinstance(nested_name, str) and nested_name.strip():
            return nested_name.strip()
    return ""


def _resolve_rows(payload: Any) -> list[dict[str, Any]]:
    if isinstance(payload, list):
        return [row for row in payload if isinstance(row, dict)]
    if isinstance(payload, dict):
        declarations = payload.get("declarations")
        if isinstance(declarations, list):
            return [row for row in declarations if isinstance(row, dict)]
        return [payload]
    return []


def _read_rows(path: Path | None) -> list[dict[str, Any]]:
    if path is None:
        return []
    all_rows: list[dict[str, Any]] = []
    text = path.read_text(encoding="utf-8")
    try:
        payload = json.loads(text)
    except Exception:
        payload = None

    if payload is None:
        all_rows.extend(read_json_lines(path))
    else:
        all_rows.extend(_resolve_rows(payload))

    return [row for row in all_rows if isinstance(row, dict)]


def _judgment_penalty(judgment: str) -> float:
    normalized = str(judgment or "").strip().lower()
    if normalized in {"regression", "wormhole"}:
        return 1.0
    if normalized == "capstone_coherence":
        return 0.05
    if normalized and normalized != "vertical" and normalized != "primitive_translator":
        return 0.1
    return 0.0


def _depth_penalty(row: dict[str, Any]) -> float:
    penalty = 0.0
    for key in (
        "reachesAboveDirect",
        "reachesAboveClosure",
        "reachesBelowPrevDirect",
        "reachesBelowPrevClosure",
    ):
        if bool(row.get(key)):
            penalty += 0.2 if "Above" in key else 0.15
    return penalty


def _conductor_score(row: dict[str, Any]) -> tuple[float, float, list[str]]:
    # score ∈ [0.0, 1.0], represented as earned/total with total=1.0
    total = 1.0
    reasons: list[str] = []

    depth = int(_to_float(row.get("targetDepthNat") if row.get("targetDepthNat") is not None else row.get("depthNat"), default=0.0))
    direct_count = int(_to_float(row.get("directTaggedDepCount"), default=0.0))

    if depth > 0 and direct_count == 0:
        reasons.append("no-direct-tagged-deps-at-depth")
    score = 1.0
    score -= _judgment_penalty(row.get("judgment", ""))
    score -= _depth_penalty(row)

    if depth > 0 and direct_count == 0:
        score -= 0.2
    if not direct_count and depth == 0:
        score -= 0.0

    if score < 0:
        score = 0.0
    if score > total:
        score = total

    earned = score
    return earned, total, reasons


def _evidence(row: dict[str, Any], *, default_decl: str) -> list[dict[str, Any]]:
    return [
        {
            "path": str(row.get("module") or row.get("file") or row.get("source") or ""),
            "line": 0,
            "snippet": json.dumps(
                {
                    "depth": row.get("depth") or row.get("depthNat"),
                    "targetDepthNat": row.get("targetDepthNat"),
                    "judgment": row.get("judgment"),
                    "directTaggedDepCount": row.get("directTaggedDepCount"),
                },
                ensure_ascii=True,
                sort_keys=True,
            ),
            "declaration": default_decl,
        }
    ]


def row_to_contract(row: dict[str, Any]) -> dict[str, Any] | None:
    decl = _first_string(row)
    if not decl:
        return None

    score_earned, score_total, reasons = _conductor_score(row)
    ok = score_earned >= 0.7
    reasons = reasons or ["conductivity:pass"]
    if not ok:
        reasons.append(f"conductivity:{score_earned:.4g}/{score_total}")

    severity = 100 if not ok else 0
    checks = ["conductivity"]
    judgment = str(row.get("judgment") or "")
    if judgment:
        checks.append(f"judgment:{judgment}")
    if row.get("directTaggedDepCount") is not None:
        checks.append("conductivity:dependencies")

    return VerificationRecord(
        decl=decl,
        module=str(row.get("module") or ""),
        lane=LANE,
        ok=ok,
        severity=severity,
        checks=checks,
        reasons=reasons,
        evidence=_evidence(row, default_decl=decl),
        provenance={
            "tool": "lean_conductivity",
            "schema": str(row.get("schema") or ""),
            "source": "representation_depth_from_graph",
            "kind": str(row.get("kind") or ""),
            "depth": str(row.get("depth") or ""),
        },
        authority_level="lean-authority",
    ).to_payload() | {"score": {"earned": score_earned, "total": score_total}}


def _write_rows(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")


def run(input_path: Path, output: Path) -> dict[str, int]:
    rows = [row_to_contract(row) for row in _read_rows(input_path)]
    rows = [row for row in rows if row]
    _write_rows(output, rows)
    return {
        "records": len(rows),
        "passed": sum(1 for row in rows if bool(row.get("ok"))),
        "failed": sum(1 for row in rows if not bool(row.get("ok"))),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-json", type=Path, required=True, help="Lean-native conductivity artifact (JSON/JSONL)")
    parser.add_argument("--out-jsonl", type=Path, required=True, help="Unified contract JSONL output")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    summary = run(args.input_json, args.out_jsonl)
    print(json.dumps(summary, sort_keys=True))
    return 0 if summary["failed"] == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
