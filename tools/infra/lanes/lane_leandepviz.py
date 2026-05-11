#!/usr/bin/env python3
"""Adapter lane for LeanDepViz-style checker artifacts."""

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


LANE_PARANOIA = "bee_pauli_policy"
LANE_SAFEVERIFY = "bee_ref_impl"
LANE_KERNEL = "bee_kernel_replay"

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
    "problem",
)


def _first_string(row: dict[str, Any], keys: tuple[str, ...] = DECL_KEYS) -> str:
    for key in keys:
        value = row.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    nested = row.get("target_info") or row.get("solution_info") or row.get("targetInfo") or row.get("solutionInfo")
    if isinstance(nested, dict):
        nested_name = nested.get("name") or nested.get("constInfo", {}).get("name")
        if isinstance(nested_name, str) and nested_name.strip():
            return nested_name.strip()
    return ""


def _evidence(row: dict[str, Any], *, default_decl: str) -> list[dict[str, Any]]:
    return [
        {
            "path": str(row.get("source_path") or row.get("source") or ""),
            "line": int(row.get("line") or 0),
            "snippet": str(row.get("snippet") or row.get("kernel_summary") or ""),
            "declaration": str(row.get("declaration") or row.get("theorem") or default_decl),
        }
    ]


def _paranoia_to_contract(row: dict[str, Any]) -> dict[str, Any]:
    decl = _first_string(row) or str(row.get("theorem") or "unknown")
    findings = row.get("findings", [])
    checks = [str(item.get("check") or "leanparanoia") for item in findings if isinstance(item, dict)]
    if not checks:
        checks = ["leanparanoia"]
    reasons = [str(item.get("message") or item) for item in findings] or (
        ["failed" if not row.get("success") else "passed"]
    )
    return VerificationRecord(
        decl=decl,
        module=str(row.get("module") or row.get("moduleName") or ""),
        lane=LANE_PARANOIA,
        ok=bool(row.get("success")),
        severity=95 if not row.get("success") else 0,
        checks=checks,
        reasons=reasons,
        evidence=_evidence(row, default_decl=decl),
        provenance={
            "tool": "leanparanoia",
            "version": str(row.get("schema") or ""),
            "cmd": row.get("command"),
            "source": "leanparanoia_audit_bridge",
        },
        authority_level="policy",
    ).to_payload()


def _safeverify_to_contract(row: dict[str, Any]) -> dict[str, Any]:
    decl = _first_string(row) or str(row.get("declaration") or "unknown")
    passed = bool(row.get("success"))
    failure = str(row.get("failure_mode") or row.get("failureMode") or ("SafeVerify failed" if not passed else ""))
    return VerificationRecord(
        decl=decl,
        module=str(row.get("module") or row.get("moduleName") or ""),
        lane=LANE_SAFEVERIFY,
        ok=passed,
        severity=100 if not passed else 0,
        checks=["kind", "type", "axioms", "target-submission"],
        reasons=[failure] if not passed else ["passed"],
        evidence=_evidence(row, default_decl=decl),
        provenance={
            "tool": "safeverify",
            "version": str(row.get("schema") or ""),
            "source": "safeverify_audit_bridge",
            "target_olean": str(row.get("target_olean") or ""),
            "submission_olean": str(row.get("submission_olean") or ""),
        },
        authority_level="policy",
    ).to_payload()


def _kernel_to_contract(row: dict[str, Any]) -> dict[str, Any]:
    decl = str(row.get("verification_key") or _first_string(row) or "unknown")
    passed = str(row.get("verification_outcome") or row.get("proof_status") or "unknown") == "passed"
    reasons = []
    if passed:
        reasons.append("kernel-check:passed")
    else:
        if row.get("error_excerpt"):
            reasons.append(str(row.get("error_excerpt")))
        elif row.get("lean_output"):
            reasons.append(str(row.get("lean_output")))
        else:
            reasons.append("kernel-check:failed")
    return VerificationRecord(
        decl=decl,
        module=str(row.get("module") or row.get("module_name") or ""),
        lane=LANE_KERNEL,
        ok=passed,
        severity=100 if not passed else 0,
        checks=["kernel", "verification_outcome"],
        reasons=reasons,
        evidence=_evidence(row, default_decl=decl),
        provenance={
            "tool": "lean-verification-packet",
            "schema": str(row.get("schema") or ""),
            "verification_outcome": str(row.get("verification_outcome") or ""),
            "proof_status": str(row.get("proof_status") or ""),
            "source": "hive_lean_verification",
        },
        authority_level="lean-authority",
    ).to_payload()


def _read_rows(path: Path | None) -> list[dict[str, Any]]:
    return read_json_lines(path) if path else []


def _write_rows(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")


def _summary(path: Path, rows: list[dict[str, Any]]) -> None:
    passed = sum(1 for row in rows if bool(row.get("ok")))
    failed = sum(1 for row in rows if not bool(row.get("ok")))
    summary = {
        "lane": "lane_leandepviz",
        "records": len(rows),
        "passed": passed,
        "failed": failed,
        "passed_ratio": (float(passed) / len(rows)) if rows else 0.0,
    }
    path.write_text(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")


def run(paranoia_path: Path | None, safeverify_path: Path | None, kernel_path: Path | None, output: Path) -> dict[str, int]:
    rows: list[dict[str, Any]] = []
    rows.extend(_paranoia_to_contract(row) for row in _read_rows(paranoia_path))
    rows.extend(_safeverify_to_contract(row) for row in _read_rows(safeverify_path))
    rows.extend(_kernel_to_contract(row) for row in _read_rows(kernel_path))
    _write_rows(output, rows)
    return {"records": len(rows), "passed": sum(1 for row in rows if bool(row.get("ok"))), "failed": sum(1 for row in rows if not bool(row.get("ok")))}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--leanparanoia-jsonl", type=Path, help="LeanParanoia normalized json/jsonl")
    parser.add_argument("--safeverify-jsonl", type=Path, help="SafeVerify normalized json/jsonl")
    parser.add_argument("--kernel-jsonl", type=Path, help="Lean verification packet JSON/JSONL")
    parser.add_argument("--out-jsonl", type=Path, required=True, help="Unified contract JSONL output")
    parser.add_argument("--out-summary", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if not any((args.leanparanoia_jsonl, args.safeverify_jsonl, args.kernel_jsonl)):
        print("At least one of --leanparanoia-jsonl / --safeverify-jsonl / --kernel-jsonl is required")
        return 2
    summary = run(args.leanparanoia_jsonl, args.safeverify_jsonl, args.kernel_jsonl, args.out_jsonl)
    if args.out_summary:
        _summary(args.out_summary, read_json_lines(args.out_jsonl))
    print(json.dumps(summary, sort_keys=True))
    return 0 if summary["failed"] == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
