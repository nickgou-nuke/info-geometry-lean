#!/usr/bin/env python3
"""Multi-role swarm worker for the live Hive queue.

Roles:
- generator bee: proposes a tactic from graph-grounded context
- critic bee: accepts/revises/rejects the proposal before Lean execution
- formalizer bee: verifies the tactic through Lean and fossilizes success
- auditor bee: records a structured trust-boundary audit for the run
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.hermes_bounded_runner import call_openai_compatible
from tools.infra import hive_bee
from tools.infra import hive_arango_queue as queue_tool

DEFAULT_SWARM_WORKER_ID = "hive-swarm-001"
ARTIFACT_DIR = ROOT / "artifacts" / "hermes_loop" / "hive_swarm"


@dataclass(frozen=True)
class SwarmConfig:
    bee: hive_bee.BeeConfig
    generator_override: str | None = None
    critic_override: str | None = None
    auditor_override: str | None = None


@dataclass
class CriticDecision:
    verdict: str
    tactic: str
    reason: str


@dataclass
class AuditorReport:
    verdict: str
    notes: str
    promotion_allowed: str


@dataclass
class SwarmRun:
    task: dict[str, Any]
    goal: dict[str, Any]
    proof_state: dict[str, Any]
    gravity_context: dict[str, Any]
    gravity_path: Path
    generator_tactic: str
    critic_decision: CriticDecision
    verification: dict[str, Any] | None
    auditor_report: AuditorReport
    started_at: float


def role_prompt(role: str, goal: dict[str, Any], proof_state: dict[str, Any], gravity_context: dict[str, Any], tactic: str = "") -> str:
    gravity = hive_bee.summarize_gravity_context(gravity_context)
    common = (
        f"Goal target: {goal.get('target_pretty') or goal.get('canonical_shape') or goal.get('entity_key')}\n"
        f"Module hint: {goal.get('module') or 'none'}\n"
        f"Current proof state:\n{proof_state.get('proof_state') or '(no proof state)'}\n\n"
        f"Gravitational context:\n{gravity}\n"
    )
    if role == "generator":
        return (
            "You are the generator bee. Propose one Lean tactic grounded in the graph context.\n"
            "Output exactly:\nTACTIC: <Lean tactic>\nRATIONALE: <one sentence>\n\n"
            + common
        )
    if role == "critic":
        return (
            "You are the critic bee. Decide whether the proposed tactic should be approved, revised, or rejected before Lean execution.\n"
            "Output exactly:\nVERDICT: approve|revise|reject\nTACTIC: <approved or revised tactic, or empty if reject>\nREASON: <one sentence>\n\n"
            f"Proposed tactic: {tactic}\n\n"
            + common
        )
    if role == "auditor":
        return (
            "You are the auditor bee. Check trust-boundary fidelity and summarize the run without claiming proof.\n"
            "Output exactly:\nVERDICT: pass|conditional_pass|fail\nPROMOTION_ALLOWED: yes|no\nNOTES: <two concise sentences>\n\n"
            f"Generator tactic: {tactic}\n"
            + common
        )
    raise ValueError(f"unknown role: {role}")


def call_role_model(config: SwarmConfig, role: str, goal: dict[str, Any], proof_state: dict[str, Any], gravity_context: dict[str, Any], tactic: str = "") -> str:
    overrides = {
        "generator": config.generator_override,
        "critic": config.critic_override,
        "auditor": config.auditor_override,
    }
    if overrides.get(role):
        return str(overrides[role]).strip()
    prompt = role_prompt(role, goal, proof_state, gravity_context, tactic=tactic)
    response = call_openai_compatible(
        base_url=config.bee.model_base_url,
        model=config.bee.model_name,
        api_key=config.bee.api_key,
        prompt=prompt,
        timeout=config.bee.timeout,
        max_tokens=220,
    )
    choices = response.get("choices") or []
    if not choices:
        raise RuntimeError(f"{role} bee returned no choices")
    message = choices[0].get("message") or {}
    text = str(message.get("content") or message.get("reasoning_content") or "").strip()
    if not text:
        raise RuntimeError(f"{role} bee returned empty output")
    return text


def parse_keyed_line(text: str, key: str) -> str:
    import re
    match = re.search(rf"(?im)^\s*{re.escape(key)}:\s*(.*)$", text)
    return match.group(1).strip() if match else ""


def parse_critic_decision(text: str) -> CriticDecision:
    raw_verdict = parse_keyed_line(text, "VERDICT")
    raw_tactic = parse_keyed_line(text, "TACTIC")
    raw_reason = parse_keyed_line(text, "REASON")
    has_schema = bool(raw_verdict or raw_tactic or raw_reason)
    verdict = raw_verdict.lower() or "reject"
    tactic = raw_tactic
    reason = raw_reason or text.strip()
    reason = " ".join(reason.split())[:400]
    if not has_schema:
        return CriticDecision(verdict="reject", tactic="", reason="non-schema critic output")
    if verdict not in {"approve", "revise", "reject"}:
        verdict = "reject"
    if verdict == "reject":
        tactic = ""
    return CriticDecision(verdict=verdict, tactic=tactic, reason=reason)


def parse_auditor_report(text: str) -> AuditorReport:
    verdict = parse_keyed_line(text, "VERDICT") or "conditional_pass"
    notes = parse_keyed_line(text, "NOTES") or text.strip()
    promotion_allowed = parse_keyed_line(text, "PROMOTION_ALLOWED") or "no"
    return AuditorReport(verdict=verdict, notes=notes, promotion_allowed=promotion_allowed)


def write_artifact(task_key: str, payload: dict[str, Any]) -> Path:
    ARTIFACT_DIR.mkdir(parents=True, exist_ok=True)
    path = ARTIFACT_DIR / f"{task_key}.json"
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return path


def audit_and_record(run: SwarmRun) -> Path:
    payload = {
        "schema": "info_geometry.hive_swarm_run.v1",
        "task_key": run.task.get("_key"),
        "goal_key": run.goal.get("_key"),
        "generator_tactic": run.generator_tactic,
        "critic": {
            "verdict": run.critic_decision.verdict,
            "tactic": run.critic_decision.tactic,
            "reason": run.critic_decision.reason,
        },
        "auditor": {
            "verdict": run.auditor_report.verdict,
            "notes": run.auditor_report.notes,
            "promotion_allowed": run.auditor_report.promotion_allowed,
        },
        "verification": run.verification,
        "gravity_context_path": str(run.gravity_path),
        "elapsed_wall_s": round(time.time() - run.started_at, 6),
        "state_taxonomy": ["retrieved", "generated", "criticized", "formalized" if run.verification else "rejected", "audited"],
    }
    return write_artifact(str(run.task.get("_key")), payload)


def run_one(config: SwarmConfig) -> dict[str, Any]:
    task, goal = hive_bee.fetch_claimed_task_and_goal(config.bee)
    if not task or not goal:
        return {"status": "idle", "worker_id": config.bee.worker_id, "queue_name": config.bee.queue_name}
    started_at = time.time()
    queue_tool.update_goal_status(
        config.bee.hive_endpoint,
        config.bee.hive_database,
        config.bee.hive_username,
        config.bee.hive_password,
        goal_key_value=str(goal["_key"]),
        status="retrieved",
        extra_fields={"swarm_worker": config.bee.worker_id, "bee_state": "retrieved"},
    )
    gravity_context, gravity_path, gravity_error = hive_bee.run_gravity_retrieval(config.bee, goal, str(task["_key"]))
    if gravity_error or not gravity_context:
        queue_tool.requeue_task(
            config.bee.hive_endpoint,
            config.bee.hive_database,
            config.bee.hive_username,
            config.bee.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.bee.worker_id,
            error_message=f"gravity retrieval failed: {gravity_error}",
        )
        queue_tool.update_goal_status(
            config.bee.hive_endpoint,
            config.bee.hive_database,
            config.bee.hive_username,
            config.bee.hive_password,
            goal_key_value=str(goal["_key"]),
            status="requeued",
            extra_fields={"bee_state": "requeued", "last_gravity_error": gravity_error},
        )
        return {"status": "requeued", "task": task, "goal": goal, "error": gravity_error}
    proof_state = hive_bee.get_proof_state(
        str(goal.get("target_pretty") or goal.get("canonical_shape") or goal.get("entity_key") or ""),
        imports=hive_bee.parse_imports(goal),
        context=hive_bee.parse_context(goal),
        timeout=config.bee.timeout,
    )
    generator_text = call_role_model(config, "generator", goal, proof_state, gravity_context)
    generator_tactic = hive_bee.extract_tactic(generator_text)
    queue_tool.update_goal_status(
        config.bee.hive_endpoint,
        config.bee.hive_database,
        config.bee.hive_username,
        config.bee.hive_password,
        goal_key_value=str(goal["_key"]),
        status="generated",
        extra_fields={"bee_state": "generated", "generator_tactic": generator_tactic, "gravity_context_path": str(gravity_path)},
    )
    critic_text = call_role_model(config, "critic", goal, proof_state, gravity_context, tactic=generator_tactic)
    critic = parse_critic_decision(critic_text)
    if critic.verdict == "reject" or not critic.tactic:
        auditor = parse_auditor_report(call_role_model(config, "auditor", goal, proof_state, gravity_context, tactic=generator_tactic))
        run = SwarmRun(task=task, goal=goal, proof_state=proof_state, gravity_context=gravity_context, gravity_path=gravity_path, generator_tactic=generator_tactic, critic_decision=critic, verification=None, auditor_report=auditor, started_at=started_at)
        artifact = audit_and_record(run)
        deadend = hive_bee.build_deadend_doc(
            goal,
            task,
            worker_id=config.bee.worker_id,
            tactic=generator_tactic,
            failure_kind="critic_rejection",
            verification={"lean": {"stdout": "", "stderr": critic.reason}},
            gravity_path=gravity_path,
            elapsed_wall_s=time.time() - started_at,
            lean_latency_s=0.0,
        )
        queue_tool.import_rows(config.bee.hive_endpoint, config.bee.hive_database, config.bee.hive_username, config.bee.hive_password, "hive_deadends", [deadend])
        queue_tool.requeue_task(
            config.bee.hive_endpoint,
            config.bee.hive_database,
            config.bee.hive_username,
            config.bee.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.bee.worker_id,
            error_message=f"critic rejected tactic: {critic.reason}",
        )
        queue_tool.update_goal_status(
            config.bee.hive_endpoint,
            config.bee.hive_database,
            config.bee.hive_username,
            config.bee.hive_password,
            goal_key_value=str(goal["_key"]),
            status="requeued",
            extra_fields={"bee_state": "critic_rejected", "swarm_artifact": str(artifact), "critic_reason": critic.reason},
        )
        return {"status": "critic_rejected", "task": task, "goal": goal, "critic": critic.__dict__, "auditor": auditor.__dict__, "artifact": str(artifact)}
    queue_tool.update_goal_status(
        config.bee.hive_endpoint,
        config.bee.hive_database,
        config.bee.hive_username,
        config.bee.hive_password,
        goal_key_value=str(goal["_key"]),
        status="criticized",
        extra_fields={"bee_state": "criticized", "critic_tactic": critic.tactic, "critic_reason": critic.reason},
    )
    lean_start = time.time()
    verification = hive_bee.apply_tactic(
        str(goal.get("target_pretty") or goal.get("canonical_shape") or goal.get("entity_key") or ""),
        critic.tactic,
        imports=hive_bee.parse_imports(goal),
        context=hive_bee.parse_context(goal),
        timeout=config.bee.timeout,
    )
    lean_latency = time.time() - lean_start
    auditor = parse_auditor_report(call_role_model(config, "auditor", goal, proof_state, gravity_context, tactic=critic.tactic))
    run = SwarmRun(task=task, goal=goal, proof_state=proof_state, gravity_context=gravity_context, gravity_path=gravity_path, generator_tactic=generator_tactic, critic_decision=critic, verification=verification, auditor_report=auditor, started_at=started_at)
    artifact = audit_and_record(run)
    attempt = hive_bee.BeeAttempt(
        task=task,
        goal=goal,
        proof_state=proof_state,
        gravity_context=gravity_context,
        gravity_path=gravity_path,
        proposed_tactic=critic.tactic,
        verification=verification,
        elapsed_wall_s=time.time() - started_at,
        lean_latency_s=lean_latency,
    )
    if verification.get("status") == "success":
        fossil = hive_bee.fossilize_success(config.bee, attempt)
        queue_tool.update_goal_status(
            config.bee.hive_endpoint,
            config.bee.hive_database,
            config.bee.hive_username,
            config.bee.hive_password,
            goal_key_value=str(goal["_key"]),
            status="audited",
            extra_fields={"bee_state": "audited", "swarm_artifact": str(artifact), "auditor_verdict": auditor.verdict, "auditor_notes": auditor.notes},
        )
        return {"status": "fossilized", "task": fossil.get("task") or task, "goal": fossil.get("goal") or goal, "generator_tactic": generator_tactic, "critic": critic.__dict__, "auditor": auditor.__dict__, "artifact": str(artifact), "fossil": fossil}
    rejection = hive_bee.record_deadend(config.bee, attempt, "lean_verification_failure")
    if int(task.get("claim_count") or 1) < hive_bee.max_attempts(goal):
        queue_tool.requeue_task(
            config.bee.hive_endpoint,
            config.bee.hive_database,
            config.bee.hive_username,
            config.bee.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.bee.worker_id,
            error_message=f"formalizer failed after critic approval: {critic.reason}",
        )
        queue_tool.update_goal_status(
            config.bee.hive_endpoint,
            config.bee.hive_database,
            config.bee.hive_username,
            config.bee.hive_password,
            goal_key_value=str(goal["_key"]),
            status="requeued",
            extra_fields={"bee_state": "audited", "swarm_artifact": str(artifact), "auditor_verdict": auditor.verdict, "auditor_notes": auditor.notes},
        )
        return {"status": "requeued", "task": task, "goal": goal, "generator_tactic": generator_tactic, "critic": critic.__dict__, "auditor": auditor.__dict__, "artifact": str(artifact), "deadend": rejection}
    queue_tool.fail_task(
        config.bee.hive_endpoint,
        config.bee.hive_database,
        config.bee.hive_username,
        config.bee.hive_password,
        task_key_value=str(task["_key"]),
        worker_id=config.bee.worker_id,
        error_message="formalizer exhausted attempts",
    )
    queue_tool.update_goal_status(
        config.bee.hive_endpoint,
        config.bee.hive_database,
        config.bee.hive_username,
        config.bee.hive_password,
        goal_key_value=str(goal["_key"]),
        status="deadend",
        extra_fields={"bee_state": "audited", "swarm_artifact": str(artifact), "auditor_verdict": auditor.verdict, "auditor_notes": auditor.notes},
    )
    return {"status": "deadend", "task": task, "goal": goal, "generator_tactic": generator_tactic, "critic": critic.__dict__, "auditor": auditor.__dict__, "artifact": str(artifact), "deadend": rejection}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hive-endpoint", default=hive_bee.DEFAULT_HIVE_ENDPOINT)
    parser.add_argument("--hive-database", default=hive_bee.DEFAULT_HIVE_DATABASE)
    parser.add_argument("--hive-username", default=hive_bee.DEFAULT_HIVE_USERNAME)
    parser.add_argument("--hive-password", default=hive_bee.DEFAULT_HIVE_PASSWORD)
    parser.add_argument("--queue-name", default=hive_bee.DEFAULT_QUEUE)
    parser.add_argument("--worker-id", default=DEFAULT_SWARM_WORKER_ID)
    parser.add_argument("--lease-seconds", type=int, default=hive_bee.DEFAULT_LEASE_SECONDS)
    parser.add_argument("--gravity-base-url", default=hive_bee.DEFAULT_GRAVITY_BASE_URL)
    parser.add_argument("--gravity-database", default=hive_bee.DEFAULT_GRAVITY_DATABASE)
    parser.add_argument("--gravity-top-k", type=int, default=hive_bee.DEFAULT_TOP_K)
    parser.add_argument("--model-base-url", default=hive_bee.DEFAULT_MODEL_BASE_URL)
    parser.add_argument("--model-name", default=hive_bee.DEFAULT_MODEL)
    parser.add_argument("--api-key", default=hive_bee.DEFAULT_API_KEY)
    parser.add_argument("--backend-kind", default=None)
    parser.add_argument("--backend-identity", default=None)
    parser.add_argument("--subscription-backed", action="store_true")
    parser.add_argument("--backend-capability", default=hive_bee.DEFAULT_BACKEND_CAPABILITY)
    parser.add_argument("--hermes-role", default=hive_bee.DEFAULT_HERMES_ROLE)
    parser.add_argument("--allow-direct-provider-api", action="store_true")
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--generator-override", default=None)
    parser.add_argument("--critic-override", default=None)
    parser.add_argument("--auditor-override", default=None)
    parser.add_argument("--once", action="store_true")
    parser.add_argument("--poll-interval", type=int, default=15)
    return parser.parse_args()


def config_from_args(args: argparse.Namespace) -> SwarmConfig:
    bee = hive_bee.BeeConfig(
        hive_endpoint=str(args.hive_endpoint).rstrip("/"),
        hive_database=str(args.hive_database),
        hive_username=str(args.hive_username),
        hive_password=str(args.hive_password),
        queue_name=str(args.queue_name),
        worker_id=str(args.worker_id),
        lease_seconds=int(args.lease_seconds),
        gravity_base_url=str(args.gravity_base_url).rstrip("/"),
        gravity_database=str(args.gravity_database),
        gravity_top_k=int(args.gravity_top_k),
        model_base_url=str(args.model_base_url).rstrip("/"),
        model_name=str(args.model_name),
        api_key=str(args.api_key),
        backend_kind=hive_bee.infer_backend_kind(args),
        backend_identity=str(args.backend_identity or args.model_base_url).rstrip("/"),
        subscription_backed=bool(args.subscription_backed),
        backend_capability=str(args.backend_capability),
        hermes_role=str(args.hermes_role),
        allow_direct_provider_api=bool(args.allow_direct_provider_api),
        timeout=int(args.timeout),
        tactic_override=None,
    )
    return SwarmConfig(
        bee=bee,
        generator_override=str(args.generator_override).strip() if args.generator_override else None,
        critic_override=str(args.critic_override).strip() if args.critic_override else None,
        auditor_override=str(args.auditor_override).strip() if args.auditor_override else None,
    )


def main() -> int:
    args = parse_args()
    config = config_from_args(args)
    while True:
        result = run_one(config)
        print(json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True))
        if args.once:
            return 0
        time.sleep(max(1, int(args.poll_interval)))


if __name__ == "__main__":
    raise SystemExit(main())
