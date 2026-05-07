#!/usr/bin/env python3
"""Recurrent proposal-only Leanstral bee worker.

This worker is the Hive-safe version of the useful Mistral Vibe pattern:
loop bounded model attempts through a verifier, keep the transcript, and stop
with either a proof candidate packet or a residue packet.  It does not call
Mistral Vibe internals, does not edit Lean files, does not run lake build, and
cannot emit authority-gate packets.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable

try:
    from tools.infra.hermes_leanstral_autoproof_loop import make_local_leanstral_proposer, run_autoproof
    from tools.infra.hermes_vibe_coding_agent import LeanstralConfig
    from tools.infra.hive_bee_runner import RunnerError, run_task, validate_envelope, validate_result_contract, write_json
    from tools.infra.hive_local_packet_store import StoreError, load_json
except ModuleNotFoundError:  # pragma: no cover - direct script execution fallback
    ROOT_FALLBACK = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(ROOT_FALLBACK))
    from tools.infra.hermes_leanstral_autoproof_loop import make_local_leanstral_proposer, run_autoproof
    from tools.infra.hermes_vibe_coding_agent import LeanstralConfig
    from tools.infra.hive_bee_runner import RunnerError, run_task, validate_envelope, validate_result_contract, write_json
    from tools.infra.hive_local_packet_store import StoreError, load_json

AutoproofFn = Callable[..., dict[str, Any]]

AUTHORITY_GATE_KINDS = {
    "ExecutionIntentPacket",
    "LeanVerificationPacket",
    "BuildPacket",
    "AuditPacket",
    "PromotionDecisionPacket",
}

VIBE_REUSED_PATTERNS = {
    "prompt_source": "/home/goutev/repos/external_tools/mistral-vibe/vibe/core/prompts/lean.md",
    "loop_source": "/home/goutev/repos/external_tools/mistral-vibe/vibe/core/agent_loop.py",
    "middleware_source": "/home/goutev/repos/external_tools/mistral-vibe/vibe/core/middleware.py",
    "reused_patterns": [
        "bounded turn/attempt limit before STOP",
        "tool/verifier feedback appended into next model turn",
        "do not claim completion without verification",
        "break repeated local failures and emit residue instead of flip-flopping",
        "read-only/fail-closed role separation",
    ],
}


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def source_refs(ids: list[str], *, role: str) -> list[dict[str, Any]]:
    refs = ids or ["task:unanchored"]
    return [{"ref": ref, "kind": "hive_packet", "role": role} for ref in refs]


def extract_goal(task: dict[str, Any]) -> str:
    for key in ("lean_goal", "goal", "formal_goal"):
        value = task.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    instruction = str(task.get("instruction", "")).strip()
    prefixes = ("Prove goal:", "Goal:", "goal:")
    for prefix in prefixes:
        if instruction.startswith(prefix):
            return instruction[len(prefix) :].strip()
    return instruction


def extract_imports(task: dict[str, Any]) -> list[str]:
    value = task.get("lean_imports", task.get("imports", ["Init"]))
    if isinstance(value, list):
        imports = [str(item).strip() for item in value if str(item).strip()]
        return imports or ["Init"]
    if isinstance(value, str) and value.strip():
        return [value.strip()]
    return ["Init"]


def ensure_task_is_bounded(task: dict[str, Any]) -> None:
    if task.get("assigned_role") != "HermesLeanstralBee":
        raise RunnerError("Hermes Leanstral worker only accepts assigned_role HermesLeanstralBee")
    if task.get("task_kind") != "leanstral.autoproof":
        raise RunnerError("Hermes Leanstral worker only accepts task_kind leanstral.autoproof")
    allowed = set(str(x) for x in task.get("allowed_output_kinds", []))
    forbidden = set(str(x) for x in task.get("forbidden_output_kinds", []))
    if allowed & AUTHORITY_GATE_KINDS:
        raise RunnerError("HermesLeanstralBee may not be allowed to emit authority-gate packets")
    if missing_forbidden := AUTHORITY_GATE_KINDS - forbidden:
        raise RunnerError(
            "BeeTask must explicitly forbid authority-gate packets: "
            + ", ".join(sorted(missing_forbidden))
        )
    if str(task.get("authority_ceiling")) != "proposal":
        raise RunnerError("HermesLeanstralBee authority_ceiling must be proposal")


def packet_id_for(task: dict[str, Any], suffix: str) -> str:
    base = str(task.get("task_id") or task.get("id") or "leanstral_task")
    return f"{suffix}_{base}"


def goal_hash(goal: str) -> str:
    return "sha256:" + hashlib.sha256(goal.strip().encode("utf-8")).hexdigest()


def compact_excerpt(value: Any, *, limit: int = 1200) -> str:
    return str(value or "")[:limit]


def packet_envelope(task: dict[str, Any], *, packet_id: str, kind: str, status: str, now: str, authority_origin: str) -> dict[str, Any]:
    return {
        "id": packet_id,
        "kind": kind,
        "status": status,
        "lineage_id": task["lineage_id"],
        "revision": 1,
        "origin_run_id": task["origin_run_id"],
        "created_at": now,
        "updated_at": now,
        "created_by_agent": "HermesLeanstralBee",
        "agent_role": "HermesLeanstralBee",
        "backend": "local_leanstral_openai_compatible",
        "task_id": task["task_id"],
        "authority": "proposal",
        "authority_origin": authority_origin,
        "promotion_allowed": False,
    }


def embedded_trace_for(task: dict[str, Any], autoproof: dict[str, Any], emitted_kind: str) -> dict[str, Any]:
    trace = autoproof.get("autoproof_trace")
    if not isinstance(trace, dict):
        trace = {
            "kind": "AutoproofTracePacket",
            "authority": "proposal",
            "promotion_allowed": False,
            "target": {"goal": str(autoproof.get("goal") or extract_goal(task)), "imports": autoproof.get("imports", extract_imports(task))},
            "budgets": {"max_iterations": autoproof.get("max_iterations", task.get("max_iterations", 0))},
            "result": {"status": str(autoproof.get("status", "unknown")), "emitted_packet_kind": emitted_kind},
            "attempts": [],
            "frontier": {"next_recommended_bee": "RetrieverBee"},
        }
    trace = dict(trace)
    trace.setdefault("kind", "AutoproofTracePacket")
    trace.setdefault("authority", "proposal")
    trace.setdefault("promotion_allowed", False)
    trace["id"] = packet_id_for(task, "autoproof_trace")
    trace["task_id"] = task.get("task_id")
    trace["lineage_id"] = task.get("lineage_id")
    trace["origin_run_id"] = task.get("origin_run_id")
    trace["embedded_only"] = True
    trace["result"] = dict(trace.get("result", {}))
    trace["result"].setdefault("emitted_packet_kind", emitted_kind)
    return trace


def trace_ref_for(task: dict[str, Any]) -> dict[str, Any]:
    return {"packet_id": packet_id_for(task, "autoproof_trace"), "embedded": False}


def trace_attempts(autoproof: dict[str, Any]) -> list[dict[str, Any]]:
    trace = autoproof.get("autoproof_trace")
    if isinstance(trace, dict) and isinstance(trace.get("attempts"), list):
        return [attempt for attempt in trace["attempts"] if isinstance(attempt, dict)]
    iterations = autoproof.get("iterations", [])
    attempts: list[dict[str, Any]] = []
    if isinstance(iterations, list):
        for iteration in iterations:
            if not isinstance(iteration, dict):
                continue
            attempts.append(
                {
                    "attempt_index": int(iteration.get("iteration", len(attempts) + 1)),
                    "mode": str(iteration.get("prompt_kind", "tactic")),
                    "candidate_text": str(iteration.get("candidate", "")),
                    "lean_result": {
                        "accepted": bool(iteration.get("lean_ok", False)),
                        "status": str(iteration.get("lean_status", "failed")),
                        "feedback": str(iteration.get("lean_feedback") or iteration.get("lean_stdout") or iteration.get("error") or ""),
                    },
                    "strategy": str(iteration.get("strategy", "lean_feedback_repair")),
                    "changed_strategy": bool(iteration.get("changed_strategy", False)),
                    "error_signature": str(iteration.get("error_signature", "")),
                    "retrieved_lemmas": [],
                }
            )
    return attempts


def build_repair_attempt_packet(
    task: dict[str, Any],
    autoproof: dict[str, Any],
    attempt: dict[str, Any],
    *,
    now: str,
    episode_id: str,
) -> dict[str, Any]:
    goal = str(autoproof.get("goal") or extract_goal(task))
    max_iterations = int(autoproof.get("max_iterations") or task.get("max_iterations", 1))
    attempt_index = int(attempt.get("attempt_index", 1))
    lean_result = attempt.get("lean_result") if isinstance(attempt.get("lean_result"), dict) else {}
    accepted = bool(lean_result.get("accepted", False))
    lean_status = str(lean_result.get("status", "success" if accepted else "failed"))
    error_sig = str(attempt.get("error_signature", ""))
    candidate_text = str(attempt.get("candidate_text", ""))
    return {
        **packet_envelope(
            task,
            packet_id=packet_id_for(task, f"repair_attempt_{attempt_index}"),
            kind="RepairAttemptPacket",
            status="success" if accepted else "failed",
            now=now,
            authority_origin="bounded_autoproof_attempt",
        ),
        "parent_refs": [str(x) for x in task.get("input_packet_ids", [])],
        "target": {
            "target_packet_id": str(task.get("target_packet_id") or (task.get("input_packet_ids") or ["task:unanchored"])[0]),
            "file": str(task.get("target_file", task.get("file", ""))),
            "module": str(task.get("target_module", task.get("module", ""))),
            "theorem": str(task.get("target_theorem", task.get("theorem", ""))),
            "goal_hash": goal_hash(goal),
        },
        "episode": {
            "episode_id": episode_id,
            "task_id": task["task_id"],
            "assigned_role": "HermesLeanstralBee",
            "attempt_index": attempt_index,
            "max_iterations": max_iterations,
        },
        "candidate": {
            "candidate_kind": str(attempt.get("mode", "tactic")) if str(attempt.get("mode", "tactic")) in {"tactic", "patch", "whole_proof", "theorem_shape", "branch_repair"} else "tactic",
            "candidate_text": candidate_text,
            "strategy": str(attempt.get("strategy", "initial_tactic")),
            "changed_strategy_from_previous": bool(attempt.get("changed_strategy", False)),
            "prompt_mode": "repair" if str(attempt.get("mode", "")) == "repair" else "tactic",
        },
        "lean_probe": {
            "probe_kind": "lean_interact_wrapper",
            "accepted": accepted,
            "status": lean_status if lean_status in {"success", "failed", "timeout", "no_progress", "not_run", "partial"} else ("success" if accepted else "failed"),
            "goal_before": str(attempt.get("goal_before") or goal),
            "goal_after": str(attempt.get("goal_after", "")),
            "stdout_excerpt": compact_excerpt(lean_result.get("stdout") or lean_result.get("feedback", "")),
            "stderr_excerpt": compact_excerpt(lean_result.get("stderr", "")),
            "error_signature": error_sig,
            "diagnostics": [compact_excerpt(lean_result.get("feedback", ""))] if lean_result.get("feedback") else [],
        },
        "retrieval_context": {
            "retrieved_lemmas": [str(x) for x in attempt.get("retrieved_lemmas", [])] if isinstance(attempt.get("retrieved_lemmas", []), list) else [],
            "owner_refs": [str(x) for x in task.get("owner_refs", [])] if isinstance(task.get("owner_refs", []), list) else [],
            "source_refs": [str(x) for x in task.get("input_packet_ids", [])],
        },
        "loop_control": {
            "same_error_repeat_count": 1 if bool(attempt.get("changed_strategy", False)) and error_sig else 0,
            "same_candidate_repeat_count": 0,
            "degeneracy_detected": False,
            "next_action_hint": "emit_candidate" if accepted else "repair",
        },
        "forbidden_uses": ["proof", "promotion", "authority_gate_bypass", "LeanVerificationPacket"],
    }


def build_autoproof_trace_packet(
    task: dict[str, Any],
    autoproof: dict[str, Any],
    attempt_packets: list[dict[str, Any]],
    final_kind: str,
    *,
    now: str,
    episode_id: str,
) -> dict[str, Any]:
    goal = str(autoproof.get("goal") or extract_goal(task))
    trace = autoproof.get("autoproof_trace") if isinstance(autoproof.get("autoproof_trace"), dict) else {}
    frontier = trace.get("frontier", {}) if isinstance(trace.get("frontier"), dict) else {}
    status = "success" if final_kind == "TheoremCandidatePacket" else "exhausted"
    return {
        **packet_envelope(
            task,
            packet_id=packet_id_for(task, "autoproof_trace"),
            kind="AutoproofTracePacket",
            status=status,
            now=now,
            authority_origin="bounded_autoproof_episode",
        ),
        "parent_refs": [packet["id"] for packet in attempt_packets],
        "producer": {
            "bee": "HermesLeanstralBee",
            "worker_id": "hermes-leanstral-bee-local-001",
            "model": str(task.get("model", "leanstral-gguf")),
            "endpoint": "local",
            "task_id": task["task_id"],
        },
        "target": {
            "target_packet_id": str(task.get("target_packet_id") or (task.get("input_packet_ids") or ["task:unanchored"])[0]),
            "file": str(task.get("target_file", task.get("file", ""))),
            "module": str(task.get("target_module", task.get("module", ""))),
            "theorem": str(task.get("target_theorem", task.get("theorem", ""))),
            "owner_refs": [str(x) for x in task.get("owner_refs", [])] if isinstance(task.get("owner_refs", []), list) else [],
        },
        "budgets": {
            "max_iterations": int(autoproof.get("max_iterations") or task.get("max_iterations", 1)),
            "lean_timeout": int(task.get("lean_timeout", 60)),
            "max_same_error_repeats": int(task.get("max_same_error_repeats", 2)),
            "max_same_candidate_repeats": int(task.get("max_same_candidate_repeats", 1)),
        },
        "result": {
            "status": status,
            "emitted_packet_kind": final_kind,
            "verified_by_local_probe": final_kind == "TheoremCandidatePacket",
            "official_lean_verification_packet": None,
        },
        "attempt_packet_ids": [packet["id"] for packet in attempt_packets],
        "frontier": {
            "last_goal_state": str(frontier.get("last_goal_state", "")),
            "last_error_signature": str(frontier.get("last_error_signature", "")),
            "failed_strategies": [str(packet["candidate"]["strategy"]) for packet in attempt_packets if not packet["lean_probe"].get("accepted")],
            "missing_lemmas": [str(x) for x in frontier.get("missing_lemmas", [])] if isinstance(frontier.get("missing_lemmas", []), list) else [],
            "promising_lemmas": [str(x) for x in frontier.get("promising_lemmas", [])] if isinstance(frontier.get("promising_lemmas", []), list) else [],
            "next_recommended_bee": str(frontier.get("next_recommended_bee", "none" if final_kind == "TheoremCandidatePacket" else "RetrieverBee")),
            "new_information_needed": str(frontier.get("new_information_needed", "none" if final_kind == "TheoremCandidatePacket" else "Pauli/Socratic/Retrieval packet before cross-task retry")),
        },
        "forbidden_authority": [
            "ExecutionIntentPacket",
            "LeanVerificationPacket",
            "BuildPacket",
            "AuditPacket",
            "PromotionDecisionPacket",
        ],
    }


def build_candidate_packet(task: dict[str, Any], autoproof: dict[str, Any], trace_packet: dict[str, Any] | None = None) -> dict[str, Any]:
    now = utc_now()
    tactic = str(autoproof.get("verified_tactic", "")).strip()
    goal = str(autoproof.get("goal") or extract_goal(task))
    imports = [str(x) for x in autoproof.get("imports", extract_imports(task))]
    input_ids = [str(x) for x in task.get("input_packet_ids", [])]
    trace = trace_packet or embedded_trace_for(task, autoproof, "TheoremCandidatePacket")
    return {
        "id": packet_id_for(task, "leanstral_candidate"),
        "kind": "TheoremCandidatePacket",
        "status": "probe_ready",
        "lineage_id": task["lineage_id"],
        "revision": 1,
        "origin_run_id": task["origin_run_id"],
        "created_at": now,
        "updated_at": now,
        "created_by_agent": "HermesLeanstralBee",
        "agent_role": "HermesLeanstralBee",
        "backend": "local_leanstral_openai_compatible",
        "task_id": task["task_id"],
        "parent_refs": input_ids,
        "evidence_refs": source_refs(input_ids, role="autoproof_input"),
        "authority": "proposal",
        "representation_class": "translator",
        "representation_depth": "scalar",
        "packet_version": "v1",
        "packet_hash": "pending",
        "symbolic_origin_refs": source_refs(input_ids, role="symbolic_origin"),
        "formal_target": {
            "target_kind": "lean_tactic_goal",
            "summary": goal,
            "candidate_shape": f"by {tactic}",
        },
        "bridge_claim": "Leanstral proposed a tactic and the local Lean interaction wrapper accepted it for the stated goal.",
        "novelty_defense": {
            "summary": "Proposal-only autoproof candidate; requires separate authority-lane packetization before promotion.",
            "pressure_points": ["model proposal is not proof authority", "single-goal wrapper evidence is not lake build evidence"],
        },
        "repo_anchor_refs": source_refs(input_ids, role="repo_anchor"),
        "candidate_dependencies": imports,
        "admissibility_state": "admissible_for_probe",
        "cost_class": "low",
        "promotion_allowed": False,
        "leanstral_autoproof": autoproof,
        "autoproof_trace": trace,
        "autoproof_trace_ref": trace_ref_for(task),
        "vibe_reused_patterns": VIBE_REUSED_PATTERNS,
    }


def build_residue_packet(task: dict[str, Any], autoproof: dict[str, Any], trace_packet: dict[str, Any] | None = None) -> dict[str, Any]:
    now = utc_now()
    iterations = autoproof.get("iterations", [])
    attempts = len(iterations) if isinstance(iterations, list) else 0
    input_ids = [str(x) for x in task.get("input_packet_ids", [])]
    trace = trace_packet or embedded_trace_for(task, autoproof, "ResiduePacket")
    return {
        "id": packet_id_for(task, "leanstral_residue"),
        "kind": "ResiduePacket",
        "status": "active",
        "lineage_id": task["lineage_id"],
        "revision": 1,
        "origin_run_id": task["origin_run_id"],
        "created_at": now,
        "updated_at": now,
        "created_by_agent": "HermesLeanstralBee",
        "agent_role": "HermesLeanstralBee",
        "backend": "local_leanstral_openai_compatible",
        "task_id": task["task_id"],
        "parent_refs": input_ids,
        "authority": "proposal",
        "representation_class": "translator",
        "representation_depth": "scalar",
        "packet_version": "v1",
        "packet_hash": "pending",
        "failure_refs": source_refs(input_ids, role="failed_autoproof_input"),
        "failure_class": "proof_obstruction",
        "stage": "formal_probe",
        "recovery_hint": f"Leanstral exhausted {attempts} attempts without Lean-accepted tactic; inspect leanstral_autoproof.iterations and reroute to Pauli/Socrates or a narrower theorem surface.",
        "return_route": "MotherBee -> PauliBee/SocratesBee -> HermesLeanstralBee",
        "recoverability": "medium" if attempts else "unknown",
        "next_cultivation_hint": "Use the final Lean error as repulsion context; avoid repeating the same local tactic family.",
        "blocked_packet_refs": source_refs(input_ids, role="blocked_packet"),
        "anchor_gap_summary": "No Lean-accepted tactic was found inside the bounded recurrent loop.",
        "leanstral_autoproof": autoproof,
        "autoproof_trace": trace,
        "autoproof_trace_ref": trace_ref_for(task),
        "vibe_reused_patterns": VIBE_REUSED_PATTERNS,
    }


def build_output_packet(task: dict[str, Any], autoproof: dict[str, Any]) -> dict[str, Any]:
    if autoproof.get("status") == "verified" and str(autoproof.get("verified_tactic", "")).strip():
        return build_candidate_packet(task, autoproof)
    return build_residue_packet(task, autoproof)


def build_output_packets(task: dict[str, Any], autoproof: dict[str, Any]) -> list[dict[str, Any]]:
    final_kind = "TheoremCandidatePacket" if autoproof.get("status") == "verified" and str(autoproof.get("verified_tactic", "")).strip() else "ResiduePacket"
    now = utc_now()
    episode_id = packet_id_for(task, "autoproof_episode")
    attempts = trace_attempts(autoproof)
    attempt_packets = [
        build_repair_attempt_packet(task, autoproof, attempt, now=now, episode_id=episode_id)
        for attempt in attempts
    ]
    trace_packet = build_autoproof_trace_packet(
        task,
        autoproof,
        attempt_packets,
        final_kind,
        now=now,
        episode_id=episode_id,
    )
    if final_kind == "TheoremCandidatePacket":
        final_packet = build_candidate_packet(task, autoproof, trace_packet)
    else:
        final_packet = build_residue_packet(task, autoproof, trace_packet)
    return [*attempt_packets, trace_packet, final_packet]


def run_worker(
    task: dict[str, Any],
    *,
    store_path: Path,
    worker_id: str,
    autoproof_fn: AutoproofFn = run_autoproof,
    dry_run: bool = False,
) -> dict[str, Any]:
    ensure_task_is_bounded(task)
    goal = extract_goal(task)
    imports = extract_imports(task)
    max_iterations = int(task.get("max_iterations", 3))
    if autoproof_fn is run_autoproof:
        proposer = make_local_leanstral_proposer(
            config=LeanstralConfig(
                endpoint=str(task.get("endpoint", "http://127.0.0.1:18889/v1")),
                model=str(task.get("model", "leanstral-gguf")),
                max_tokens=int(task.get("max_tokens", 128)),
                timeout=float(task.get("timeout_seconds", task.get("timeout", 180))),
                temperature=float(task.get("temperature", 0.0)),
            )
        )
        autoproof = autoproof_fn(
            goal=goal,
            imports=imports,
            context=str(task.get("context", "")),
            max_iterations=max_iterations,
            lean_timeout=int(task.get("lean_timeout", 60)),
            proposer=proposer,
        )
    else:
        autoproof = autoproof_fn(
            goal=goal,
            imports=imports,
            max_iterations=max_iterations,
            endpoint=str(task.get("endpoint", "http://127.0.0.1:18889/v1")),
            model=str(task.get("model", "leanstral-gguf")),
            max_tokens=int(task.get("max_tokens", 128)),
            timeout=float(task.get("timeout_seconds", task.get("timeout", 180))),
            lean_timeout=float(task.get("lean_timeout", 60)),
        )
    output_packets = build_output_packets(task, autoproof)
    output = output_packets[-1]
    result = run_task(
        task,
        store_path=store_path,
        output_packets=output_packets,
        worker_id=worker_id,
        force_dry_run=dry_run,
    )
    result.setdefault("artifact_paths", [])
    result["artifact_paths"] = list(result["artifact_paths"]) + [f"packet:{packet['id']}" for packet in output_packets]
    result.setdefault("commands_run", [])
    result["commands_run"] = list(result["commands_run"]) + ["hermes_leanstral_autoproof_loop.run_autoproof"]
    result["telemetry"] = dict(result.get("telemetry", {}))
    result["telemetry"]["leanstral_attempts"] = len(autoproof.get("iterations", [])) if isinstance(autoproof.get("iterations"), list) else 0
    result["telemetry"]["leanstral_status"] = str(autoproof.get("status", "unknown"))
    validate_envelope(result, "BeeResult")
    validate_result_contract(task, result, output_packets)
    return result


def cmd_run(args: argparse.Namespace) -> int:
    task = load_json(Path(args.task))
    store = Path(args.store or task.get("store_path", ""))
    if not str(store):
        print("ERROR: store path required via --store or BeeTask.store_path", file=sys.stderr)
        return 2
    try:
        result = run_worker(task, store_path=store, worker_id=args.worker_id, dry_run=args.dry_run)
    except (RunnerError, StoreError, RuntimeError, ValueError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    if args.result:
        write_json(Path(args.result), result)
    print(json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False))
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    sp = p.add_subparsers(dest="cmd", required=True)
    p_run = sp.add_parser("run", help="Run one bounded HermesLeanstralBee task.")
    p_run.add_argument("--task", required=True, help="Path to BeeTask JSON.")
    p_run.add_argument("--store", default="", help="Path to Hive local packet JSONL store.")
    p_run.add_argument("--worker-id", default="hermes-leanstral-bee-local-001")
    p_run.add_argument("--result", default="", help="Optional BeeResult output path.")
    p_run.add_argument("--dry-run", action="store_true", help="Validate but do not append output packet.")
    return p.parse_args()


def main() -> None:
    args = parse_args()
    if args.cmd == "run":
        raise SystemExit(cmd_run(args))
    raise SystemExit(2)


if __name__ == "__main__":
    main()
