#!/usr/bin/env python3
"""Validate unified verification payloads and verifier contract records."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.verification_contract import read_json_lines

REPORT_SCHEMA = "info_geometry.hive_multichecker_report.v1"
CONTRACT_SCHEMA = "info_geometry.verification_result.v1"

def _add(errors: list[str], msg: str) -> None:
    errors.append(msg)


def _is_mapping(value: Any) -> bool:
    return isinstance(value, dict)


def validate_contract_row(row: dict[str, Any], context: str) -> list[str]:
    errors: list[str] = []
    if row.get("schema") != CONTRACT_SCHEMA:
        _add(errors, f"{context}: schema must be {CONTRACT_SCHEMA}")
    if not isinstance(row.get("decl"), str) or not row["decl"]:
        _add(errors, f"{context}: decl missing or not a string")
    if not isinstance(row.get("lane"), str) or not row["lane"]:
        _add(errors, f"{context}: lane missing or not a string")
    if not isinstance(row.get("ok"), bool):
        _add(errors, f"{context}: ok missing or not a bool")
    checks = row.get("checks")
    if not isinstance(checks, list):
        _add(errors, f"{context}: checks missing or not a list")
    reasons = row.get("reasons")
    if reasons is not None and not isinstance(reasons, list):
        _add(errors, f"{context}: reasons must be a list")
    provenance = row.get("provenance")
    if provenance is not None and not isinstance(provenance, dict):
        _add(errors, f"{context}: provenance must be a map")
    return errors


def validate_jsonl(path: Path) -> list[str]:
    errors: list[str] = []
    for idx, row in enumerate(read_json_lines(path)):
        errors.extend(validate_contract_row(row, f"{path}:{idx}"))
    return errors


def validate_report(payload: dict[str, Any], path: Path | None = None) -> list[str]:
    errors: list[str] = []
    context = str(path) if path else "<payload>"
    if payload.get("schema") != REPORT_SCHEMA:
        _add(errors, f"{context}: schema must be {REPORT_SCHEMA}")
    for field in ("policy", "summary", "declarations"):
        if not _is_mapping(payload.get(field)) if field != "declarations" else not isinstance(payload.get(field), list):
            _add(errors, f"{context}: missing or invalid {field}")
    for idx, declaration in enumerate(payload.get("declarations", [])):
        decl_context = f"{context}:declarations[{idx}]"
        if not isinstance(declaration, dict):
            _add(errors, f"{decl_context}: must be an object")
            continue
        for field in ("decl", "module", "kind", "ok", "tools", "checks", "policy"):
            if field == "checks":
                if not isinstance(declaration.get(field), list):
                    _add(errors, f"{decl_context}: {field} must be a list")
            elif field == "tools":
                if not isinstance(declaration.get(field), dict):
                    _add(errors, f"{decl_context}: {field} must be a map")
            elif field == "policy":
                if not isinstance(declaration.get(field), dict):
                    _add(errors, f"{decl_context}: {field} must be a map")
            else:
                if field != "ok" and not isinstance(declaration.get(field), str):
                    _add(errors, f"{decl_context}: {field} must be a string")
                if field == "ok" and not isinstance(declaration.get(field), bool):
                    _add(errors, f"{decl_context}: ok must be a bool")
    return errors


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-json", type=Path, help="Unified report JSON path")
    parser.add_argument("--contract-json", type=Path, action="append", default=[], help="Lane contract row JSON/JSONL path")
    parser.add_argument("--jsonl", type=Path, action="append", default=[], help="Contract or declaration JSONL input")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    errors: list[str] = []
    for path in args.jsonl:
        if not path.exists():
            errors.append(f"{path}: file does not exist")
            continue
        errors.extend(validate_jsonl(path))
    for path in args.contract_json:
        if not path.exists():
            errors.append(f"{path}: file does not exist")
            continue
        errors.extend(validate_jsonl(path))
    if args.report_json:
        if not args.report_json.exists():
            errors.append(f"{args.report_json}: file does not exist")
        else:
            try:
                payload = json.loads(args.report_json.read_text(encoding="utf-8"))
            except Exception as exc:
                errors.append(f"{args.report_json}: invalid JSON: {exc}")
            else:
                errors.extend(validate_report(payload, args.report_json))

    if errors:
        print("\n".join(errors))
        return 2

    print("verification schema validation ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
