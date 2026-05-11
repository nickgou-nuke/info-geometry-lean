#!/usr/bin/env python3
"""Adapter for SocraticQuestionPacket and related Socratic artifacts."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    ROOT = Path(__file__).resolve().parents[3]
    sys.path.insert(0, str(ROOT))

from tools.infra.verification_contract import VerificationRecord, read_json_lines


LANE = "bee_socratic"

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

DECL_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'\\.]*$")


def _first_string(row: dict[str, Any], keys: tuple[str, ...] = DECL_KEYS) -> str:
    for key in keys:
        value = row.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""


def _looks_like_decl(value: str) -> bool:
    candidate = value.strip()
    if not candidate:
        return False
    if ":" in candidate:
        return False
    if not DECL_RE.match(candidate):
        return False
    # Heuristic: skip obvious task/packet ids and opaque IDs.
    lowered = candidate.lower()
    if lowered.startswith("pkt_") or lowered.startswith("question_") or lowered.startswith("task_"):
        return False
    return True


def _pick_decl_from_value(value: Any) -> str:
    if not isinstance(value, str):
        return ""
    candidate = value.strip()
    if not _looks_like_decl(candidate):
        return ""
    return candidate


def _decl_candidates(row: dict[str, Any]) -> list[str]:
    candidates: list[str] = []
    direct = _first_string(row)
    if direct:
        candidates.append(direct)

    nested_decl = row.get("target")
    if isinstance(nested_decl, dict):
        direct_nested = _first_string(nested_decl, keys=("theorem", "name", "declaration", "decl", "target_name", "target_decl"))
        if direct_nested:
            candidates.append(direct_nested)

    for key in ("target_packet_ids", "input_packet_ids", "blocked_packet_refs"):
        value = row.get(key)
        if isinstance(value, (list, tuple)):
            for item in value:
                decl = _pick_decl_from_value(item)
                if decl:
                    candidates.append(decl)
        elif isinstance(value, str):
            decl = _pick_decl_from_value(value)
            if decl:
                candidates.append(decl)

    for key in ("question", "question_id", "target_scope", "status_note"):
        decl = _pick_decl_from_value(_first_string(row, keys=(key,)))
        if decl:
            candidates.append(decl)

    # De-duplicate while preserving order.
    seen: set[str] = set()
    out: list[str] = []
    for item in candidates:
        if item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def _row_status(row: dict[str, Any]) -> str:
    value = str(row.get("status") or row.get("state") or "").strip().lower()
    if value:
        return value
    return "answered" if str(row.get("resolved", "")).strip().lower() == "true" else "open"


def _row_to_contract(row: dict[str, Any], decl: str) -> dict[str, Any]:
    status = _row_status(row)
    question_type = str(row.get("question_type") or row.get("inquiry_type") or "other").strip().lower() or "other"
    source = str(row.get("source") or row.get("kind") or "")
    question = str(row.get("question") or row.get("content") or "").strip()
    checks = [f"socratic-question:{source or 'packet'}", f"status:{status or 'unknown'}"]
    if question_type:
        checks.append(f"question-type:{question_type}")

    status_ok = status in {"answered", "archived", "resolved", "converted_to_evidence"}
    ok = bool(status_ok and row.get("resolved") is not False)
    if row.get("resolved") is False and status in {"open", "draft"}:
        ok = False
    reasons: list[str] = []
    if question:
        reasons.append(question)
    if status:
        reasons.append(f"socratic-status:{status}")
    if question_type:
        reasons.append(f"socratic-question-type:{question_type}")
    if not reasons:
        reasons.append("socratic-lane:question-emitted")

    severity_map = {
        "answered": 0,
        "archived": 10,
        "resolved": 0,
        "converted_to_evidence": 5,
        "draft": 70,
        "open": 70,
        "blocked": 90,
        "converted_to_critique": 80,
        "exhausted": 85,
    }
    severity = severity_map.get(status, 70 if not ok else 0)
    if not ok and status == "open" and question_type == "falsification_pressure":
        severity = max(severity, 80)

    return VerificationRecord(
        decl=decl,
        module=str(row.get("module") or row.get("module_name") or row.get("path") or ""),
        lane=LANE,
        ok=ok,
        severity=severity,
        checks=checks,
        reasons=reasons,
        evidence=[
            {
                "path": str(row.get("path") or row.get("source_path") or ""),
                "line": int(row.get("line") or 0),
                "snippet": question,
                "declaration": decl,
            }
        ],
        provenance={
            "tool": "socratic",
            "schema": str(row.get("schema") or ""),
            "authority": str(row.get("authority") or "semantic"),
            "source": str(source or "socratic_packet"),
            "question_type": str(question_type or ""),
            "status": status,
        },
        authority_level="heuristic",
    ).to_payload()


def _read_input_rows(path: Path | None) -> list[dict[str, Any]]:
    if path is None:
        return []
    if path.suffix.lower() == ".jsonl":
        return read_json_lines(path)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return []
    if isinstance(payload, dict):
        return [payload]
    if isinstance(payload, list):
        return [row for row in payload if isinstance(row, dict)]
    return []


def _write_rows(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")


def run(input_path: Path, out_jsonl: Path) -> dict[str, int]:
    rows: list[dict[str, Any]] = []
    for source in _read_input_rows(input_path):
        decls = _decl_candidates(source)
        if not decls and source.get("declaration"):
            decls = [_first_string(source)]
        for decl in decls:
            contract_row = _row_to_contract(source, decl=decl)
            if contract_row:
                rows.append(contract_row)

    _write_rows(out_jsonl, rows)
    return {
        "records": len(rows),
        "passed": sum(1 for row in rows if bool(row.get("ok"))),
        "failed": sum(1 for row in rows if not bool(row.get("ok"))),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-json", type=Path, required=True, help="Socratic packet JSON/JSONL input.")
    parser.add_argument("--out-jsonl", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    summary = run(args.input_json, args.out_jsonl)
    print(json.dumps(summary, sort_keys=True))
    return 0 if summary["failed"] == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
