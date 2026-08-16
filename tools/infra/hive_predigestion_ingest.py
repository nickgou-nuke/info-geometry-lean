#!/usr/bin/env python3
"""Materialize Hive queue tasks from predigested claim packets.

The output tasks are intentionally non-authoritative. They ask Hive workers to
map, test, formalize, or reject semantic claims; they do not assert them.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Iterable


CLAIM_SCHEMA = "info_geometry.predigested_claim.v1"
TASK_SCHEMA = "hive.packet.predigestion_task.v1"

TASK_KINDS = {
    "formalize_claim",
    "map_claim_to_owner_surface",
    "extract_hidden_hypotheses",
    "construct_counterexample_or_guard",
    "find_existing_repo_support",
}
AUTHORITIES = {"proposal"}

AUTHORITY_BOUNDARY = {
    "task_is_not_authority": True,
    "semantic_artifact_can_propose": True,
    "only_lean_checked_artifacts_can_assert": True,
}
REQUIRED_GATES = ["lean_checked", "build_checked", "audit_checked"]


def canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))


# [lossless-compact] stable_hash folded into igf.common.hashing.stable_hash
from igf.common.hashing import stable_hash


def require_enum(value: str, allowed: set[str], name: str) -> str:
    if value not in allowed:
        raise SystemExit(f"invalid {name}: {value!r}; expected one of {sorted(allowed)}")
    return value


# [lossless-compact] iter_jsonl folded into igf.common.json_io.iter_jsonl
from igf.common.json_io import iter_jsonl


def validate_claim(row: dict[str, Any]) -> None:
    if row.get("schema") != CLAIM_SCHEMA:
        raise SystemExit(f"invalid claim schema: {row.get('schema')!r}")
    if row.get("authority") not in {"source_text", "semantic", "proposal"}:
        raise SystemExit(f"claim authority is too strong for predigestion ingest: {row.get('authority')!r}")
    boundary = row.get("authority_boundary")
    if not isinstance(boundary, dict) or not boundary.get("lean_remains_proof_authority"):
        raise SystemExit("claim packet is missing Lean authority boundary")


def make_task(claim: dict[str, Any], *, task_kind: str, authority: str = "proposal") -> dict[str, Any]:
    task_kind = require_enum(task_kind, TASK_KINDS, "task_kind")
    authority = require_enum(authority, AUTHORITIES, "authority")
    validate_claim(claim)
    payload = {
        "claim": claim.get("claim") or "",
        "risk": claim.get("risk") or "informal",
        "repo_owner_candidates": claim.get("repo_owner_candidates") or [],
        "lean_target_candidates": claim.get("lean_target_candidates") or [],
        "source_ref": claim.get("source_ref") or {},
    }
    task = {
        "schema": TASK_SCHEMA,
        "id": "",
        "task_kind": task_kind,
        "claim_id": claim.get("id"),
        "source_kind": claim.get("source_kind"),
        "authority": authority,
        "status": "queued",
        "payload": payload,
        "required_gates": list(REQUIRED_GATES),
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
    }
    task["id"] = stable_hash(
        {
            "schema": TASK_SCHEMA,
            "task_kind": task_kind,
            "claim_id": task["claim_id"],
            "payload": payload,
            "authority": authority,
        }
    )
    return task


def build_tasks(claims_path: Path, *, task_kind: str) -> list[dict[str, Any]]:
    return [make_task(claim, task_kind=task_kind) for claim in iter_jsonl(claims_path)]


# [lossless-compact] write_jsonl folded into igf.common.json_io.write_jsonl
from igf.common.json_io import write_jsonl


def summary_for(rows: list[dict[str, Any]], *, claims_path: Path, out: Path) -> dict[str, Any]:
    by_task_kind: dict[str, int] = {}
    by_source_kind: dict[str, int] = {}
    for row in rows:
        by_task_kind[row["task_kind"]] = by_task_kind.get(row["task_kind"], 0) + 1
        source_kind = str(row.get("source_kind") or "")
        by_source_kind[source_kind] = by_source_kind.get(source_kind, 0) + 1
    return {
        "schema": "hive.packet.predigestion_task.summary.v1",
        "claims": str(claims_path),
        "output": str(out),
        "records": len(rows),
        "by_task_kind": by_task_kind,
        "by_source_kind": by_source_kind,
        "authority_boundary": dict(AUTHORITY_BOUNDARY),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--claims", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--summary-out", type=Path)
    parser.add_argument("--task-kind", required=True, choices=sorted(TASK_KINDS))
    args = parser.parse_args()

    rows = build_tasks(args.claims, task_kind=args.task_kind)
    write_jsonl(args.out, rows)
    summary = summary_for(rows, claims_path=args.claims, out=args.out)
    if args.summary_out:
        args.summary_out.parent.mkdir(parents=True, exist_ok=True)
        args.summary_out.write_text(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
