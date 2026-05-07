#!/usr/bin/env python3
"""Bounded BeeTask runner over the local Hive packet store.

This runner is deliberately small: it does not call models, Lean, Arango, or
Hermes.  It enforces the BeeTask/BeeResult IO contract around prebuilt output
packets so MotherBee can later schedule real workers against the same boundary.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from tools.infra.hive_local_packet_store import StoreError, append_packet, load_json, packet_hash, read_store, records_by_id, validate_or_raise
    from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet
except ModuleNotFoundError:  # pragma: no cover - direct script execution fallback
    ROOT_FALLBACK = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(ROOT_FALLBACK))
    from tools.infra.hive_local_packet_store import StoreError, append_packet, load_json, packet_hash, read_store, records_by_id, validate_or_raise
    from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet

AUTHORITY_ORDER = {
    "navigation": 0,
    "semantic": 1,
    "proposal": 2,
    "execution_intent": 3,
    "lean_checked": 4,
    "build_checked": 5,
    "audit_checked": 6,
    "promoted": 7,
}

KIND_AUTHORITY_FLOOR = {
    "SourceObservationPacket": "navigation",
    "SymbolicMotifPacket": "semantic",
    "SocraticQuestionPacket": "semantic",
    "SymbolicSeed": "semantic",
    "FormulationVariant": "semantic",
    "ResonanceCluster": "semantic",
    "PauliCritique": "semantic",
    "InvariantDraft": "semantic",
    "ResiduePacket": "semantic",
    "TheoremCandidatePacket": "proposal",
    "TranslationPacket": "proposal",
    "RetrievalHypothesisPacket": "proposal",
    "ExecutionIntentPacket": "execution_intent",
    "LeanVerificationPacket": "lean_checked",
    "BuildPacket": "build_checked",
    "AuditPacket": "audit_checked",
    "PromotionDecisionPacket": "promoted",
}

ROLE_POLICY = {
    "SourceBee": {
        "task_kinds": {"source.capture"},
        "max_authority": "navigation",
        "allowed_output_kinds": {"SourceObservationPacket"},
    },
    "RetrieverBee": {
        "task_kinds": {"retrieval.context"},
        "max_authority": "proposal",
        "allowed_output_kinds": {"RetrievalHypothesisPacket", "ResiduePacket"},
    },
    "SocratesBee": {
        "task_kinds": {"socratic.question"},
        "max_authority": "semantic",
        "allowed_output_kinds": {"SocraticQuestionPacket", "ResiduePacket"},
    },
    "PauliBee": {
        "task_kinds": {"pauli.critique"},
        "max_authority": "semantic",
        "allowed_output_kinds": {"PauliCritique", "ResiduePacket"},
    },
    "TranslatorBee": {
        "task_kinds": {"candidate.translate", "candidate.formulate"},
        "max_authority": "proposal",
        "allowed_output_kinds": {"TranslationPacket", "TheoremCandidatePacket", "FormulationVariant", "ResiduePacket"},
    },
    "ThinkingBee": {
        "task_kinds": {"candidate.translate", "candidate.formulate"},
        "max_authority": "proposal",
        "allowed_output_kinds": {"TheoremCandidatePacket", "InvariantDraft", "FormulationVariant", "ResiduePacket"},
    },
    "DreamlineBee": {
        "task_kinds": {"dreamline.explore"},
        "max_authority": "semantic",
        "allowed_output_kinds": {"SymbolicMotifPacket", "FormulationVariant", "SocraticQuestionPacket", "ResiduePacket"},
    },
    "ShadowBee": {
        "task_kinds": {"shadow.reroute"},
        "max_authority": "semantic",
        "allowed_output_kinds": {"SymbolicMotifPacket", "FormulationVariant", "SocraticQuestionPacket", "ResiduePacket"},
    },
    "LeanBee": {
        "task_kinds": {"lean.verify"},
        "max_authority": "lean_checked",
        "allowed_output_kinds": {"LeanVerificationPacket"},
        "requires_input_kinds": {"ExecutionIntentPacket"},
    },
    "BuildBee": {
        "task_kinds": {"build.verify"},
        "max_authority": "build_checked",
        "allowed_output_kinds": {"BuildPacket"},
        "requires_input_kinds": {"LeanVerificationPacket"},
    },
    "AuditBee": {
        "task_kinds": {"audit.semantic"},
        "max_authority": "audit_checked",
        "allowed_output_kinds": {"AuditPacket"},
        "requires_input_kinds": {"BuildPacket"},
    },
    "PromotionBee": {
        "task_kinds": {"promotion.decide"},
        "max_authority": "promoted",
        "allowed_output_kinds": {"PromotionDecisionPacket"},
        "requires_input_kinds": {"AuditPacket"},
    },
}


class RunnerError(RuntimeError):
    pass


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def validate_envelope(envelope: dict[str, Any], kind: str) -> None:
    packet = dict(envelope)
    packet["kind"] = kind
    schema_path = SCHEMA_BY_KIND[kind]
    errors = validate_packet(packet, schema_path, build_store())
    if errors:
        joined = "\n".join(f"- {err}" for err in errors)
        raise RunnerError(f"invalid {kind}:\n{joined}")


def role_policy(task: dict[str, Any]) -> dict[str, Any]:
    role = str(task.get("assigned_role", ""))
    policy = ROLE_POLICY.get(role)
    if policy is None:
        raise RunnerError(f"no runner role policy for assigned_role {role}")
    return policy


def validate_task_policy(task: dict[str, Any], input_packets: dict[str, dict[str, Any]] | None = None) -> None:
    role = str(task.get("assigned_role", ""))
    task_kind = str(task.get("task_kind", ""))
    policy = role_policy(task)
    allowed_task_kinds = set(str(x) for x in policy.get("task_kinds", set()))
    if task_kind not in allowed_task_kinds:
        raise RunnerError(f"task_kind {task_kind} is not compatible with assigned_role {role}")
    ceiling = str(task.get("authority_ceiling", ""))
    max_authority = str(policy.get("max_authority", "navigation"))
    if not authority_lte(ceiling, max_authority):
        raise RunnerError(f"BeeTask authority_ceiling {ceiling} exceeds role policy max_authority {max_authority}")
    if input_packets is not None:
        input_kinds = {str(packet.get("kind", "")) for packet in input_packets.values()}
        required = set(str(x) for x in policy.get("requires_input_kinds", set()))
        if required and not required <= input_kinds:
            raise RunnerError(
                f"assigned_role {role} requires input kinds {sorted(required)}; present kinds {sorted(input_kinds)}"
            )


def validate_result_contract(task: dict[str, Any], result: dict[str, Any], outputs: list[dict[str, Any]]) -> None:
    if result.get("task_id") != task.get("task_id"):
        raise RunnerError("BeeResult.task_id does not match BeeTask.task_id")
    if result.get("assigned_role") != task.get("assigned_role"):
        raise RunnerError("BeeResult.assigned_role does not match BeeTask.assigned_role")
    task_inputs = set(str(x) for x in task.get("input_packet_ids", []))
    result_inputs = set(str(x) for x in result.get("input_packet_ids", []))
    if not result_inputs <= task_inputs:
        raise RunnerError("BeeResult.input_packet_ids are not a subset of BeeTask.input_packet_ids")
    if result.get("promotion_allowed") is not False:
        raise RunnerError("BeeResult.promotion_allowed must be false")
    output_ids = [str(packet.get("id", "")) for packet in outputs]
    output_hashes = [packet_hash(packet) for packet in outputs]
    if result.get("output_packet_ids") != output_ids:
        raise RunnerError("BeeResult.output_packet_ids do not match emitted packets")
    if result.get("output_packet_hashes") != output_hashes:
        raise RunnerError("BeeResult.output_packet_hashes do not match emitted packets")
    if len(result.get("output_packet_ids", [])) != len(result.get("output_packet_hashes", [])):
        raise RunnerError("BeeResult output ids/hash lengths differ")
    emitted = set(str(x) for x in result.get("emitted_packet_kinds", []))
    allowed = set(str(x) for x in task.get("allowed_output_kinds", []))
    forbidden = set(str(x) for x in task.get("forbidden_output_kinds", []))
    if not emitted <= allowed:
        raise RunnerError("BeeResult emitted packet kinds exceed BeeTask.allowed_output_kinds")
    role_allowed = set(str(x) for x in role_policy(task).get("allowed_output_kinds", set()))
    if not emitted <= role_allowed:
        raise RunnerError("BeeResult emitted packet kinds exceed role policy allowed_output_kinds")
    if emitted & forbidden:
        raise RunnerError("BeeResult emitted packet kinds include BeeTask.forbidden_output_kinds")
    ceiling = str(task.get("authority_ceiling", ""))
    claimed = str(result.get("authority_claimed", ""))
    if not authority_lte(claimed, ceiling):
        raise RunnerError(f"BeeResult authority {claimed} exceeds BeeTask ceiling {ceiling}")


def authority_lte(actual: str, ceiling: str) -> bool:
    return AUTHORITY_ORDER.get(actual, 999) <= AUTHORITY_ORDER.get(ceiling, -1)


def output_authority(packet: dict[str, Any]) -> str:
    authority = packet.get("authority")
    if isinstance(authority, str) and authority:
        return authority
    kind = str(packet.get("kind", ""))
    return KIND_AUTHORITY_FLOOR.get(kind, "promoted")


def load_input_packets(store_path: Path, input_packet_ids: list[str]) -> dict[str, dict[str, Any]]:
    records = records_by_id(read_store(store_path))
    missing = [packet_id for packet_id in input_packet_ids if packet_id not in records]
    if missing:
        raise RunnerError(f"missing input packets in store: {', '.join(missing)}")
    return {packet_id: records[packet_id] for packet_id in input_packet_ids}


def enforce_output_contract(task: dict[str, Any], output: dict[str, Any]) -> None:
    kind = str(output.get("kind", ""))
    task_allowed = set(str(x) for x in task.get("allowed_output_kinds", []))
    role_allowed = set(str(x) for x in role_policy(task).get("allowed_output_kinds", set()))
    forbidden = set(str(x) for x in task.get("forbidden_output_kinds", []))
    ceiling = str(task.get("authority_ceiling", ""))
    authority = output_authority(output)

    if kind not in task_allowed:
        raise RunnerError(f"output kind not allowed by BeeTask: {kind}")
    if kind not in role_allowed:
        raise RunnerError(f"output kind not allowed by role policy for {task.get('assigned_role')}: {kind}")
    if kind in forbidden:
        raise RunnerError(f"output kind is forbidden by BeeTask: {kind}")
    if not authority_lte(authority, ceiling):
        raise RunnerError(f"output authority {authority} exceeds BeeTask ceiling {ceiling}")
    if kind == "PromotionDecisionPacket":
        raise RunnerError("BeeTask runner may not emit PromotionDecisionPacket")
    validate_or_raise(output)


def build_result(
    task: dict[str, Any],
    *,
    worker_id: str,
    status: str,
    outputs: list[dict[str, Any]],
    output_hashes: list[str],
    errors: list[str] | None = None,
    started_at: float | None = None,
    dry_run: bool = False,
) -> dict[str, Any]:
    now = utc_now()
    started = started_at if started_at is not None else time.monotonic()
    emitted_kinds = [str(packet.get("kind", "")) for packet in outputs]
    claimed = "navigation"
    if outputs:
        claimed = max((output_authority(packet) for packet in outputs), key=lambda a: AUTHORITY_ORDER.get(a, -1))
    return {
        "id": f"bee_result_{task['task_id']}",
        "kind": "BeeResult",
        "status": status,
        "lineage_id": task["lineage_id"],
        "revision": 1,
        "origin_run_id": task["origin_run_id"],
        "created_at": now,
        "updated_at": now,
        "task_id": task["task_id"],
        "worker_id": worker_id,
        "assigned_role": task["assigned_role"],
        "input_packet_ids": list(task.get("input_packet_ids", [])),
        "output_packet_ids": [str(packet.get("id", "")) for packet in outputs],
        "output_packet_hashes": output_hashes,
        "emitted_packet_kinds": emitted_kinds,
        "authority_claimed": claimed,
        "promotion_allowed": False,
        "artifact_paths": [],
        "commands_run": [],
        "errors": list(errors or []),
        "blocker": "; ".join(errors or []) if errors else "",
        "next_action": "none" if status == "done" else "inspect_runner_error",
        "telemetry": {
            "compute_duration_ms": int((time.monotonic() - started) * 1000),
            "tokens_consumed": 0,
            "despair_metric": 0,
            "phase_similarity_delta": 0,
            "proof_state_delta": "not_measured",
            "semantic_novelty": 0,
            "dry_run": dry_run,
        },
    }


def run_task(
    task: dict[str, Any],
    *,
    store_path: Path,
    output_packets: list[dict[str, Any]],
    worker_id: str,
    force_dry_run: bool = False,
) -> dict[str, Any]:
    started = time.monotonic()
    validate_envelope(task, "BeeTask")
    validate_task_policy(task)
    dry_run = bool(task.get("dry_run", False)) or force_dry_run
    input_packets = load_input_packets(store_path, [str(x) for x in task.get("input_packet_ids", [])])
    validate_task_policy(task, input_packets)

    output_hashes: list[str] = []
    for packet in output_packets:
        enforce_output_contract(task, packet)
        output_hashes.append(packet_hash(packet))

    if not dry_run:
        output_hashes = []
        for packet in output_packets:
            digest, _status = append_packet(store_path, packet)
            output_hashes.append(digest)

    result = build_result(
        task,
        worker_id=worker_id,
        status="done",
        outputs=output_packets,
        output_hashes=output_hashes,
        started_at=started,
        dry_run=dry_run,
    )
    validate_envelope(result, "BeeResult")
    validate_result_contract(task, result, output_packets)
    return result


def write_json(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")


def cmd_run(args: argparse.Namespace) -> int:
    task_path = Path(args.task)
    task = load_json(task_path)
    store = Path(args.store or task.get("store_path", ""))
    if not str(store):
        print("ERROR: store path required via --store or BeeTask.store_path", file=sys.stderr)
        return 2
    outputs = [load_json(Path(path)) for path in args.emit_packet]
    try:
        result = run_task(
            task,
            store_path=store,
            output_packets=outputs,
            worker_id=args.worker_id,
            force_dry_run=args.dry_run,
        )
    except (RunnerError, StoreError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    if args.result:
        write_json(Path(args.result), result)
    print(json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False))
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    sp = p.add_subparsers(dest="cmd", required=True)

    p_run = sp.add_parser("run", help="Run a bounded BeeTask over prebuilt output packets.")
    p_run.add_argument("--task", required=True, help="Path to BeeTask JSON.")
    p_run.add_argument("--store", default="", help="Path to local packet store. Defaults to BeeTask.store_path.")
    p_run.add_argument("--emit-packet", action="append", default=[], help="Prebuilt output packet JSON to validate and optionally append.")
    p_run.add_argument("--worker-id", required=True, help="Worker instance id for BeeResult.")
    p_run.add_argument("--result", default="", help="Optional path to write BeeResult JSON.")
    p_run.add_argument("--dry-run", action="store_true", help="Validate only; do not append output packets.")
    return p.parse_args()


def main() -> None:
    args = parse_args()
    if args.cmd == "run":
        raise SystemExit(cmd_run(args))
    raise SystemExit(2)


if __name__ == "__main__":
    main()
