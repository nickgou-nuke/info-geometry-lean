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

HERMES_LEANSTRAL_TARGET_KINDS = {
    "TheoremCandidatePacket",
    "TranslationPacket",
    "RetrievalHypothesisPacket",
    "ResiduePacket",
}
HERMES_LEANSTRAL_ALLOWED_AUTHORITIES = {"semantic", "proposal"}
HERMES_LEANSTRAL_NEW_INFORMATION_KINDS = {
    "SocraticQuestionPacket",
    "PauliCritique",
    "RetrievalHypothesisPacket",
    "TranslationPacket",
    "TheoremCandidatePacket",
}
HERMES_LEANSTRAL_RULE = RouteRule(
    rule_id="proposal-to-hermes-leanstral-v1",
    source_kind="*",
    source_statuses=frozenset({"draft", "legalized", "probe_ready", "active", "stabilized"}),
    assigned_role="HermesLeanstralBee",
    task_kind="leanstral.autoproof",
    allowed_output_kinds=("RepairAttemptPacket", "AutoproofTracePacket", "TheoremCandidatePacket", "ResiduePacket"),
    forbidden_output_kinds=FORBIDDEN_AUTHORITY_OUTPUTS,
    authority_ceiling="proposal",
    instruction=(
        "Run a bounded local Leanstral proof-proposal loop over the target, preserving every Lean feedback "
        "attempt as first-class RepairAttemptPacket evidence and the episode as AutoproofTracePacket evidence. "
        "Finish with TheoremCandidatePacket or ResiduePacket; do not claim Lean/build/audit authority."
    ),
    priority=30,
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


def packet_refs(value: Any) -> set[str]:
    refs: set[str] = set()
    if isinstance(value, str):
        refs.add(value)
    elif isinstance(value, dict):
        ref = value.get("ref")
        if isinstance(ref, str):
            refs.add(ref)
        for child in value.values():
            refs |= packet_refs(child)
    elif isinstance(value, list):
        for child in value:
            refs |= packet_refs(child)
    return refs


def record_references(record: dict[str, Any], target_id: str) -> bool:
    if record.get("id") == target_id:
        return True
    reference_fields = (
        "target_packet_id",
        "input_packet_ids",
        "parent_refs",
        "context_refs",
        "target_packet_ids",
        "blocked_packet_refs",
        "failure_refs",
        "evidence_refs",
        "symbolic_origin_refs",
        "repo_anchor_refs",
        "seed_refs",
        "candidate_anchor_refs",
        "invariant_refs",
        "target_scope",
    )
    return any(target_id in packet_refs(record.get(field)) for field in reference_fields)


def has_unresolved_high_severity_pauli_block(records: list[dict[str, Any]], target: dict[str, Any]) -> bool:
    target_id = record_id(target)
    for record in records:
        if record.get("kind") != "PauliCritique" or not record_references(record, target_id):
            continue
        severity = str(record.get("severity") or record.get("block_severity") or record.get("pauli_severity") or "").lower()
        unresolved = record.get("resolved") is not True and str(record.get("status", "")) not in {"retired", "archived"}
        if unresolved and severity in {"high", "critical", "blocker"}:
            return True
    return False


def leanstral_attempt_indices(records: list[dict[str, Any]], target: dict[str, Any]) -> list[int]:
    target_id = record_id(target)
    indices: list[int] = []
    for index, record in enumerate(records):
        if not record_references(record, target_id):
            continue
        if record.get("kind") == "BeeTask" and record.get("assigned_role") == "HermesLeanstralBee":
            indices.append(index)
        elif record.get("agent_role") == "HermesLeanstralBee" or record.get("created_by_agent") == "HermesLeanstralBee":
            indices.append(index)
    return indices


def retry_count_for_hermes_leanstral(records: list[dict[str, Any]], target: dict[str, Any]) -> int:
    return len(leanstral_attempt_indices(records, target))


def target_index(records: list[dict[str, Any]], target: dict[str, Any]) -> int:
    target_id = record_id(target)
    for index, record in enumerate(records):
        if record.get("id") == target_id:
            return index
    return -1


def has_new_information_since_last_leanstral_attempt(records: list[dict[str, Any]], target: dict[str, Any]) -> bool:
    kind = str(target.get("kind", ""))
    if bool(target.get("formal_probe")) or str(target.get("route_intent", "")) == "formal_probe":
        return True
    attempts = leanstral_attempt_indices(records, target)
    if not attempts and kind in {"TranslationPacket", "RetrievalHypothesisPacket"}:
        return True
    baseline = max(attempts) if attempts else target_index(records, target)
    target_id = record_id(target)
    for index, record in enumerate(records):
        if index <= baseline:
            continue
        if record.get("id") == target_id:
            continue
        if record.get("kind") in HERMES_LEANSTRAL_NEW_INFORMATION_KINDS and record_references(record, target_id):
            return True
    return False


def extract_lean_goal(target: dict[str, Any]) -> str:
    for key in ("lean_goal", "goal", "formal_goal", "target_surface"):
        value = target.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    formal_target = target.get("formal_target")
    if isinstance(formal_target, dict):
        for key in ("summary", "candidate_shape", "target_kind"):
            value = formal_target.get(key)
            if isinstance(value, str) and value.strip():
                return value.strip()
    return str(target.get("bridge_claim") or target.get("retrieval_summary") or target.get("summary") or record_id(target))


def extract_lean_imports(target: dict[str, Any]) -> list[str]:
    for key in ("lean_imports", "imports", "imports_candidate", "candidate_dependencies"):
        value = target.get(key)
        if isinstance(value, list):
            imports = [str(item).strip() for item in value if str(item).strip()]
            if imports:
                return imports
        if isinstance(value, str) and value.strip():
            return [value.strip()]
    return ["Init"]


def may_route_to_hermes_leanstral(
    records: list[dict[str, Any]],
    target: dict[str, Any],
    *,
    max_retries: int = 2,
) -> bool:
    if target.get("kind") not in HERMES_LEANSTRAL_TARGET_KINDS:
        return False
    if target.get("kind") == "ResiduePacket" and target.get("agent_role") == "HermesLeanstralBee":
        # A residue may be retried only after Pauli/Socratic/Retrieval/Translation adds new information.
        pass
    authority = str(target.get("authority", ""))
    if authority not in HERMES_LEANSTRAL_ALLOWED_AUTHORITIES:
        return False
    status = target.get("status")
    if not isinstance(status, str) or status not in HERMES_LEANSTRAL_RULE.source_statuses:
        return False
    if has_unresolved_high_severity_pauli_block(records, target):
        return False
    if retry_count_for_hermes_leanstral(records, target) >= max_retries:
        return False
    if not has_new_information_since_last_leanstral_attempt(records, target):
        return False
    return True


def build_bee_task(rule: RouteRule, target: dict[str, Any], *, store_path: Path, dry_run_task: bool) -> dict[str, Any]:
    tid = task_id_for(rule, target)
    now = task_created_at(target)
    target_id = record_id(target)
    lineage = str(target.get("lineage_id") or f"lineage_{target_id}")
    origin_run = str(target.get("origin_run_id") or "motherbee_v1")
    task = {
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
    if rule.assigned_role == "HermesLeanstralBee":
        task.update(
            {
                "lean_goal": extract_lean_goal(target),
                "lean_imports": extract_lean_imports(target),
                "max_iterations": 3,
                "lean_timeout": 60,
                "timeout_seconds": 180,
                "retry_count": 0,
                "has_new_information_since_last_leanstral_attempt": True,
            }
        )
    return task


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
        leanstral_pair = (record_id(record), HERMES_LEANSTRAL_RULE.assigned_role, HERMES_LEANSTRAL_RULE.task_kind)
        if leanstral_pair not in already and may_route_to_hermes_leanstral(records, record):
            task = build_bee_task(HERMES_LEANSTRAL_RULE, record, store_path=store_path, dry_run_task=dry_run_task)
            task["retry_count"] = retry_count_for_hermes_leanstral(records, record)
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
