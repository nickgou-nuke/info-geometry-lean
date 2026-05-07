#!/usr/bin/env python3
"""Deterministic MotherBee scheduler v1 over the local Hive packet ledger.

MotherBee v1 is intentionally a dispatcher, not a worker and not a policy
firewall.  It reads validated packets from the local JSONL store, applies a
small deterministic routing table, and appends BeeTask envelopes back into the
same ledger.  Task state is therefore derivable from append-only packets: no
mutable `is_processed` flag, no SQLite sidecar, no Arango dependency.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

try:
    from tools.infra.hive_local_packet_store import StoreError, append_packet, read_store
    from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet
except ModuleNotFoundError:  # pragma: no cover - direct script execution fallback
    ROOT_FALLBACK = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(ROOT_FALLBACK))
    from tools.infra.hive_local_packet_store import StoreError, append_packet, read_store
    from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet


class MotherBeeError(RuntimeError):
    pass


@dataclass(frozen=True)
class RouteRule:
    rule_id: str
    source_kind: str
    source_statuses: frozenset[str]
    assigned_role: str
    task_kind: str
    allowed_output_kinds: tuple[str, ...]
    forbidden_output_kinds: tuple[str, ...]
    authority_ceiling: str
    instruction: str
    priority: int


FORBIDDEN_AUTHORITY_OUTPUTS = (
    "ExecutionIntentPacket",
    "LeanVerificationPacket",
    "BuildPacket",
    "AuditPacket",
    "PromotionDecisionPacket",
)

ROUTE_RULES = (
    RouteRule(
        rule_id="source-observation-to-socrates-v1",
        source_kind="SourceObservationPacket",
        source_statuses=frozenset({"captured"}),
        assigned_role="SocratesBee",
        task_kind="socratic.question",
        allowed_output_kinds=("SocraticQuestionPacket", "ResiduePacket"),
        forbidden_output_kinds=FORBIDDEN_AUTHORITY_OUTPUTS,
        authority_ceiling="semantic",
        instruction=(
            "Interrogate the source observation for missing hypotheses, hidden owner boundaries, "
            "and weakest-version questions. Emit only semantic packets."
        ),
        priority=50,
    ),
    RouteRule(
        rule_id="theorem-candidate-to-pauli-v1",
        source_kind="TheoremCandidatePacket",
        source_statuses=frozenset({"draft", "legalized", "probe_ready"}),
        assigned_role="PauliBee",
        task_kind="pauli.critique",
        allowed_output_kinds=("PauliCritique", "ResiduePacket"),
        forbidden_output_kinds=FORBIDDEN_AUTHORITY_OUTPUTS,
        authority_ceiling="semantic",
        instruction=(
            "Apply Pauli anti-inflation pressure to the candidate: identify hidden assumptions, "
            "owner-shadow collapse, duplicate branches, and inadmissible authority jumps."
        ),
        priority=40,
    ),
)


def stable_digest(parts: list[str]) -> str:
    return hashlib.sha256("\u241f".join(parts).encode("utf-8")).hexdigest()[:16]


def record_id(record: dict[str, Any]) -> str:
    value = record.get("id")
    if not isinstance(value, str) or not value:
        raise MotherBeeError(f"record missing string id: {record!r}")
    return value


def task_key(rule: RouteRule, target: dict[str, Any]) -> str:
    return stable_digest([rule.rule_id, record_id(target), str(target.get("lineage_id", ""))])


def task_id_for(rule: RouteRule, target: dict[str, Any]) -> str:
    return f"bee_task_{task_key(rule, target)}"


def task_created_at(target: dict[str, Any]) -> str:
    created = target.get("created_at") or target.get("updated_at") or "1970-01-01T00:00:00Z"
    return str(created)


def build_bee_task(rule: RouteRule, target: dict[str, Any], *, store_path: Path, dry_run_task: bool) -> dict[str, Any]:
    tid = task_id_for(rule, target)
    now = task_created_at(target)
    target_id = record_id(target)
    lineage = str(target.get("lineage_id") or f"lineage_{target_id}")
    origin_run = str(target.get("origin_run_id") or "motherbee_v1")
    return {
        "id": tid,
        "kind": "BeeTask",
        "status": "pending",
        "lineage_id": lineage,
        "revision": 1,
        "origin_run_id": origin_run,
        "created_at": now,
        "updated_at": now,
        "task_id": tid,
        "assigned_role": rule.assigned_role,
        "task_kind": rule.task_kind,
        "target_packet_id": target_id,
        "input_packet_ids": [target_id],
        "parent_refs": [target_id],
        "context_refs": [target_id],
        "repulsion_field": [],
        "allowed_output_kinds": list(rule.allowed_output_kinds),
        "forbidden_output_kinds": list(rule.forbidden_output_kinds),
        "authority_ceiling": rule.authority_ceiling,
        "instruction": rule.instruction,
        "priority": rule.priority,
        "store_path": str(store_path),
        "dry_run": dry_run_task,
        "timeout_seconds": 120,
        "motherbee_rule_id": rule.rule_id,
        "scheduler": "MotherBee.v1",
    }


def validate_bee_task(task: dict[str, Any]) -> None:
    errors = validate_packet(task, SCHEMA_BY_KIND["BeeTask"], build_store())
    if errors:
        joined = "\n".join(f"- {err}" for err in errors)
        raise MotherBeeError(f"generated BeeTask failed validation:\n{joined}")


def scheduled_pairs(records: list[dict[str, Any]]) -> set[tuple[str, str, str]]:
    pairs: set[tuple[str, str, str]] = set()
    for record in records:
        if record.get("kind") != "BeeTask":
            continue
        target = record.get("target_packet_id")
        role = record.get("assigned_role")
        task_kind = record.get("task_kind")
        if isinstance(target, str) and isinstance(role, str) and isinstance(task_kind, str):
            pairs.add((target, role, task_kind))
    return pairs


def rule_matches(rule: RouteRule, record: dict[str, Any]) -> bool:
    if record.get("kind") != rule.source_kind:
        return False
    status = record.get("status")
    return isinstance(status, str) and status in rule.source_statuses


def discover_tasks(records: list[dict[str, Any]], *, store_path: Path, dry_run_task: bool) -> list[dict[str, Any]]:
    already = scheduled_pairs(records)
    tasks: list[dict[str, Any]] = []
    for record in records:
        if record.get("kind") == "BeeTask":
            continue
        for rule in ROUTE_RULES:
            if not rule_matches(rule, record):
                continue
            pair = (record_id(record), rule.assigned_role, rule.task_kind)
            if pair in already:
                continue
            task = build_bee_task(rule, record, store_path=store_path, dry_run_task=dry_run_task)
            validate_bee_task(task)
            tasks.append(task)
    tasks.sort(key=lambda task: (-int(task.get("priority", 0)), str(task.get("target_packet_id", "")), str(task.get("id", ""))))
    return tasks


def append_tasks(store_path: Path, tasks: list[dict[str, Any]]) -> list[dict[str, str]]:
    receipts: list[dict[str, str]] = []
    for task in tasks:
        digest, status = append_packet(store_path, task)
        receipts.append({"id": str(task["id"]), "task_id": str(task["task_id"]), "packet_hash": digest, "status": status})
    return receipts


def run_once(store_path: Path, *, limit: int, dry_run: bool, dry_run_task: bool) -> dict[str, Any]:
    records = read_store(store_path)
    tasks = discover_tasks(records, store_path=store_path, dry_run_task=dry_run_task)
    selected = tasks[:limit] if limit > 0 else tasks
    receipts: list[dict[str, str]] = []
    if not dry_run:
        receipts = append_tasks(store_path, selected)
    return {
        "scheduler": "MotherBee.v1",
        "store": str(store_path),
        "dry_run": dry_run,
        "dry_run_task": dry_run_task,
        "planned_count": len(tasks),
        "emitted_count": 0 if dry_run else len(receipts),
        "tasks": selected,
        "receipts": receipts,
    }


def emit_json(data: Any) -> None:
    print(json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False))


def cmd_once(args: argparse.Namespace) -> int:
    try:
        result = run_once(Path(args.store), limit=args.limit, dry_run=args.dry_run, dry_run_task=args.task_dry_run)
    except (MotherBeeError, StoreError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    emit_json(result)
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    sp = p.add_subparsers(dest="cmd", required=True)

    p_once = sp.add_parser("once", help="Plan or append one deterministic batch of BeeTask packets.")
    p_once.add_argument("--store", required=True, help="Path to local packet store JSONL.")
    p_once.add_argument("--limit", type=int, default=1, help="Maximum tasks to append/print; 0 means no limit.")
    p_once.add_argument("--dry-run", action="store_true", help="Print planned tasks without appending them.")
    p_once.add_argument("--task-dry-run", action="store_true", help="Set generated BeeTask.dry_run=true for later BeeRunner validation-only execution.")
    return p.parse_args()


def main() -> None:
    args = parse_args()
    if args.cmd == "once":
        raise SystemExit(cmd_once(args))
    raise SystemExit(2)


if __name__ == "__main__":
    main()
