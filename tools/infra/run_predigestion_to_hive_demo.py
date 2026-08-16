#!/usr/bin/env python3
"""Run a reproducible predigestion-to-Hive dry run.

This is an operational smoke/demo lane: it builds advisory predigestion claim
packets, materializes non-authoritative Hive queue tasks, and writes a compact
summary. It does not promote claims and does not assert mathematical truth.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.infra.build_predigestion_packets import (
    AUTHORITY_BOUNDARY as CLAIM_AUTHORITY_BOUNDARY,
    SOURCE_KINDS,
    RISKS,
    build_packets,
    canonical_json,
    summary_for as claim_summary_for,
    write_jsonl as write_claim_jsonl,
)
from tools.infra.hive_predigestion_ingest import (
    AUTHORITY_BOUNDARY as TASK_AUTHORITY_BOUNDARY,
    TASK_KINDS,
    build_tasks,
    summary_for as task_summary_for,
    write_jsonl as write_task_jsonl,
)


SCHEMA = "info_geometry.predigestion_to_hive_demo.v1"


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")


# [lossless-compact] read_jsonl folded into igf.common.json_io.read_jsonl
from igf.common.json_io import read_jsonl


def sample_rows(rows: list[dict[str, Any]], limit: int) -> list[dict[str, Any]]:
    if limit <= 0:
        return []
    return rows[:limit]


def run_demo(
    *,
    input_path: Path,
    source_kind: str,
    task_kind: str,
    output_dir: Path,
    risk: str | None = None,
    sample_limit: int = 3,
) -> dict[str, Any]:
    if source_kind not in SOURCE_KINDS:
        raise SystemExit(f"invalid source_kind: {source_kind!r}")
    if risk is not None and risk not in RISKS:
        raise SystemExit(f"invalid risk: {risk!r}")
    if task_kind not in TASK_KINDS:
        raise SystemExit(f"invalid task_kind: {task_kind!r}")

    output_dir.mkdir(parents=True, exist_ok=True)
    claims_path = output_dir / "claims.jsonl"
    claim_summary_path = output_dir / "claims_summary.json"
    tasks_path = output_dir / "hive_predigestion_tasks.jsonl"
    task_summary_path = output_dir / "hive_predigestion_tasks_summary.json"
    summary_path = output_dir / "predigestion_to_hive_demo_summary.json"
    sample_tasks_path = output_dir / "sample_hive_queue_packets.json"

    claim_rows = build_packets(input_path, source_kind=source_kind, risk=risk)
    write_claim_jsonl(claims_path, claim_rows)
    claim_summary = claim_summary_for(claim_rows, input_path=input_path, out=claims_path)
    write_json(claim_summary_path, claim_summary)

    task_rows = build_tasks(claims_path, task_kind=task_kind)
    write_task_jsonl(tasks_path, task_rows)
    task_summary = task_summary_for(task_rows, claims_path=claims_path, out=tasks_path)
    write_json(task_summary_path, task_summary)

    sample_tasks = sample_rows(task_rows, sample_limit)
    write_json(sample_tasks_path, {"schema": "hive.packet.predigestion_task.sample.v1", "tasks": sample_tasks})

    summary = {
        "schema": SCHEMA,
        "input": str(input_path),
        "source_kind": source_kind,
        "risk_override": risk,
        "task_kind": task_kind,
        "artifacts": {
            "claims": str(claims_path),
            "claims_summary": str(claim_summary_path),
            "tasks": str(tasks_path),
            "tasks_summary": str(task_summary_path),
            "sample_tasks": str(sample_tasks_path),
        },
        "counts": {
            "claims": len(claim_rows),
            "tasks": len(task_rows),
            "sample_tasks": len(sample_tasks),
        },
        "by_risk": claim_summary.get("by_risk", {}),
        "by_authority": claim_summary.get("by_authority", {}),
        "by_task_kind": task_summary.get("by_task_kind", {}),
        "by_source_kind": task_summary.get("by_source_kind", {}),
        "authority_boundary": {
            "demo_is_dry_run": True,
            "claims_are_advisory": True,
            "tasks_are_non_authoritative": True,
            "semantic_artifact_can_propose": CLAIM_AUTHORITY_BOUNDARY["semantic_artifact_can_propose"],
            "lean_remains_proof_authority": CLAIM_AUTHORITY_BOUNDARY["lean_remains_proof_authority"],
            "only_lean_checked_artifacts_can_assert": TASK_AUTHORITY_BOUNDARY["only_lean_checked_artifacts_can_assert"],
        },
    }
    write_json(summary_path, summary)
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="Source chunk JSONL")
    parser.add_argument("--source-kind", required=True, choices=sorted(SOURCE_KINDS))
    parser.add_argument("--task-kind", required=True, choices=sorted(TASK_KINDS))
    parser.add_argument("--risk", choices=sorted(RISKS), help="Override risk for all emitted claims")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--sample-limit", type=int, default=3)
    args = parser.parse_args()

    summary = run_demo(
        input_path=args.input,
        source_kind=args.source_kind,
        task_kind=args.task_kind,
        output_dir=args.output_dir,
        risk=args.risk,
        sample_limit=args.sample_limit,
    )
    print(json.dumps(summary, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
