#!/usr/bin/env python3
"""Adapter lane for Paperclip/managed-employee control telemetry."""

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


LANE = "bee_paperclip"

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

PASS_STATUSES = {
    "passed",
    "pass",
    "resolved",
    "completed",
    "complete",
    "closed",
    "success",
    "succeeded",
    "approved",
    "running",
    "heartbeat",
    "alive",
    "stable",
    "resolved_with_warning",
}

FAIL_STATUSES = {
    "open",
    "blocked",
    "rejected",
    "failed",
    "failing",
    "fail",
    "missing",
    "error",
    "errored",
    "timeout",
    "escalate",
    "critical",
}

CRITICAL_FAIL_STATUSES = {
    "blocked",
    "rejected",
    "critical",
    "failing",
    "failed",
    "timeout",
}


def _first_string(row: dict[str, Any], keys: tuple[str, ...] = DECL_KEYS) -> str:
    for key in keys:
        value = row.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""


def _normalize_decl(value: str) -> str:
    if not value:
        return ""
    value = value.strip()
    if ":" in value:
        return ""
    return value


def _first_string_decl(row: dict[str, Any], keys: tuple[str, ...] = DECL_KEYS) -> str:
    return _normalize_decl(_first_string(row, keys))


def _collect_decl_rows(row: dict[str, Any]) -> list[str]:
    decls: list[str] = []
    direct = _first_string_decl(row)
    if direct:
        decls.append(direct)

    for key in ("target", "declaration", "decl", "goal", "target_name", "target_decl"):
        nested = row.get(key)
        if isinstance(nested, dict):
            value = _first_string_decl(nested)
            if value:
                decls.append(value)

    for key in ("declarations", "targets", "target_declarations", "checks"):
        value = row.get(key)
        if isinstance(value, (list, tuple)):
            for item in value:
                if isinstance(item, str):
                    normalized = _normalize_decl(item)
                    if normalized:
                        decls.append(normalized)
                elif isinstance(item, dict):
                    value_item = _first_string_decl(item)
                    if value_item:
                        decls.append(value_item)
        elif isinstance(value, dict):
            value_item = _first_string_decl(value)
            if value_item:
                decls.append(value_item)

    seen: set[str] = set()
    out: list[str] = []
    for item in decls:
        if item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def _status(row: dict[str, Any]) -> str:
    return str(row.get("status") or row.get("state") or row.get("result") or "").strip().lower()


def _status_ok_and_severity(row: dict[str, Any]) -> tuple[bool, int]:
    status = _status(row)
    if row.get("ok") is not None:
        ok_value = bool(row.get("ok"))
        if ok_value:
            return True, 0
        return False, 90

    if row.get("passed") is not None:
        passed = bool(row.get("passed"))
        if passed:
            return True, 0
        return False, 80

    if status in PASS_STATUSES:
        return True, 0
    if status in FAIL_STATUSES:
        if status in CRITICAL_FAIL_STATUSES:
            return False, 90
        return False, 70
    if row.get("severity") is not None:
        try:
            return bool(float(row.get("severity")) < 80), int(float(row.get("severity")))
        except Exception:
            pass
    if row.get("error") or row.get("message"):
        return False, 80
    return True, 0


def _evidence(row: dict[str, Any], default_decl: str) -> list[dict[str, Any]]:
    return [
        {
            "path": str(
                row.get("path")
                or row.get("file")
                or row.get("source_path")
                or row.get("project")
                or ""
            ),
            "line": int(row.get("line") or row.get("line_number") or 0),
            "snippet": str(row.get("snippet") or row.get("message") or row.get("task_body") or ""),
            "declaration": default_decl,
        }
    ]


def _row_to_contract(row: dict[str, Any], decl: str) -> dict[str, Any]:
    ok, severity = _status_ok_and_severity(row)
    status = _status(row)
    checks = ["paperclip-control"]
    if status:
        checks.append(f"paperclip-status:{status}")
    if row.get("ticket"):
        checks.append("paperclip-ticket")

    reasons: list[str] = []
    if row.get("message"):
        reasons.append(str(row.get("message")))
    if row.get("error"):
        reasons.append(str(row.get("error")))
    if status:
        reasons.append(f"paperclip-status:{status}")
    if not reasons:
        reasons.append(f"paperclip-ok:{ok}")

    provenance = {
        "tool": "paperclip",
        "schema": str(row.get("schema") or ""),
        "source": str(row.get("source") or row.get("adapter") or "paperclip"),
        "task_id": str(row.get("task_id") or row.get("id") or ""),
        "severity_hint": row.get("severity") if row.get("severity") is not None else "",
    }

    return VerificationRecord(
        decl=decl,
        module=str(row.get("module") or row.get("project") or ""),
        lane=LANE,
        ok=ok,
        severity=severity,
        checks=checks,
        reasons=[item for item in reasons if item],
        evidence=_evidence(row, default_decl=decl),
        provenance=provenance,
        authority_level="heuristic",
    ).to_payload()


def _read_rows(path: Path | None) -> list[dict[str, Any]]:
    if path is None:
        return []

    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        payload = None

    if payload is not None:
        if isinstance(payload, dict):
            for container_key in ("rows", "events", "items"):
                if container_key in payload:
                    container = payload.get(container_key)
                    if isinstance(container, list):
                        return [row for row in container if isinstance(row, dict)]
                    return []
            return [payload] if isinstance(payload, dict) else []
        if isinstance(payload, list):
            return [row for row in payload if isinstance(row, dict)]

    return read_json_lines(path)


def run(input_path: Path, out_jsonl: Path) -> dict[str, int]:
    rows: list[dict[str, Any]] = []
    for source in _read_rows(input_path):
        for decl in _collect_decl_rows(source):
            rows.append(_row_to_contract(source, decl=decl))

    out_jsonl.parent.mkdir(parents=True, exist_ok=True)
    with out_jsonl.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")

    return {
        "records": len(rows),
        "passed": sum(1 for row in rows if bool(row.get("ok"))),
        "failed": sum(1 for row in rows if not bool(row.get("ok"))),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-json", type=Path, required=True, help="Paperclip/adapter input JSON/JSONL")
    parser.add_argument("--out-jsonl", type=Path, required=True, help="Unified contract JSONL output")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    summary = run(args.input_json, args.out_jsonl)
    print(json.dumps(summary, sort_keys=True))
    return 0 if summary["failed"] == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
