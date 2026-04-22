#!/usr/bin/env python3
"""Queue-backed autoproof bee for the live Hive manifold.

This worker enforces the repo's trust boundary:
- retrieve graph-grounded context from the theorem DAG on 8529 first
- ask a prover model for a tactic only after retrieval succeeds
- verify every tactic through the Lean REPL bridge
- fossilize successes back into hive_live
- record structured deadends/rejections to avoid blind churn
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.hermes_bounded_runner import call_openai_compatible
from tools.infra import hive_arango_queue as queue_tool
from tools.infra.lean_interact_wrapper import apply_tactic, get_proof_state

DEFAULT_HIVE_ENDPOINT = queue_tool.DEFAULT_ENDPOINT
DEFAULT_HIVE_DATABASE = queue_tool.DEFAULT_DATABASE
DEFAULT_HIVE_USERNAME = queue_tool.DEFAULT_USERNAME
DEFAULT_HIVE_PASSWORD = queue_tool.DEFAULT_PASSWORD
DEFAULT_QUEUE = queue_tool.DEFAULT_QUEUE
DEFAULT_WORKER_ID = "hive-bee-001"
DEFAULT_LEASE_SECONDS = queue_tool.DEFAULT_LEASE_SECONDS
DEFAULT_GRAVITY_BASE_URL = "http://127.0.0.1:8529"
DEFAULT_GRAVITY_DATABASE = "infogeometry"
DEFAULT_MODEL_BASE_URL = "http://127.0.0.1:30002/v1"
DEFAULT_MODEL = "deepseek-prover-v2-7b-q8_0.gguf"
DEFAULT_API_KEY = "***"
DEFAULT_TOP_K = 6
DEFAULT_MAX_ATTEMPTS = 3
ARTIFACT_DIR = ROOT / "artifacts" / "hermes_loop" / "hive_bee"
GRAVITY_TOOL = ROOT / "tools" / "infra" / "arango_gravity_context.py"


@dataclass(frozen=True)
class BeeConfig:
    hive_endpoint: str
    hive_database: str
    hive_username: str
    hive_password: str
    queue_name: str
    worker_id: str
    lease_seconds: int
    gravity_base_url: str
    gravity_database: str
    gravity_top_k: int
    model_base_url: str
    model_name: str
    api_key: str
    timeout: int
    tactic_override: str | None = None


@dataclass
class BeeAttempt:
    task: dict[str, Any]
    goal: dict[str, Any]
    proof_state: dict[str, Any]
    gravity_context: dict[str, Any]
    gravity_path: Path
    proposed_tactic: str
    verification: dict[str, Any]
    elapsed_wall_s: float
    lean_latency_s: float


def utc_now() -> str:
    return queue_tool.iso_now()


def sanitize_identifier(text: str) -> str:
    text = re.sub(r"[^A-Za-z0-9_]+", "_", text.strip())
    text = re.sub(r"_+", "_", text).strip("_")
    return text or "goal"


def parse_imports(goal: dict[str, Any]) -> list[str]:
    imports = goal.get("imports") or goal.get("lean_imports") or []
    if isinstance(imports, str):
        imports = [item.strip() for item in imports.split(",") if item.strip()]
    if isinstance(imports, list):
        out = [str(item).strip() for item in imports if str(item).strip()]
        return out or ["Mathlib"]
    return ["Mathlib"]


def parse_context(goal: dict[str, Any]) -> str:
    context = goal.get("lean_context") or goal.get("context") or ""
    return str(context)


def build_gravity_query(goal: dict[str, Any]) -> str:
    parts = [
        str(goal.get("target_pretty") or ""),
        str(goal.get("canonical_shape") or ""),
        str(goal.get("module") or ""),
        str(goal.get("entity_key") or ""),
        "operator partition massieu modular drazin weyl fisher hessian",
    ]
    return re.sub(r"\s+", " ", " ".join(part for part in parts if part).strip())


def run_gravity_retrieval(config: BeeConfig, goal: dict[str, Any], task_key: str) -> tuple[dict[str, Any] | None, Path, str | None]:
    ARTIFACT_DIR.mkdir(parents=True, exist_ok=True)
    out_path = ARTIFACT_DIR / f"{task_key}-gravity.json"
    query = build_gravity_query(goal)
    cmd = [
        sys.executable,
        str(GRAVITY_TOOL),
        "--query",
        query,
        "--source",
        "auto",
        "--graph-mode",
        "faithful",
        "--scc-anchor-first",
        "--top-k",
        str(config.gravity_top_k),
        "--max-hops",
        "8",
        "--arango-url",
        config.gravity_base_url,
        "--arango-db",
        config.gravity_database,
        "--json-out",
        str(out_path),
        "--repo-root",
        str(ROOT),
    ]
    try:
        proc = subprocess.run(
            cmd,
            cwd=ROOT,
            text=True,
            capture_output=True,
            timeout=config.timeout,
            check=False,
        )
    except Exception as exc:  # noqa: BLE001
        return None, out_path, repr(exc)
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout or f"gravity exit {proc.returncode}").strip()
        return None, out_path, detail
    if not out_path.exists():
        return None, out_path, "gravity retrieval produced no JSON artifact"
    payload = json.loads(out_path.read_text(encoding="utf-8"))
    return payload, out_path, None


def summarize_gravity_context(context: dict[str, Any]) -> str:
    items = context.get("items") or []
    lines = [
        f"graph_source={context.get('graph_source')} graph_mode={context.get('graph_mode')}",
        f"node_count={context.get('node_count')} edge_count={context.get('edge_count')}",
    ]
    for item in items[:4]:
        witness = item.get("faithful_witness") or {}
        lines.append(
            f"- {item.get('id') or item.get('name')} module={item.get('module')} score={item.get('score')} "
            f"scc={witness.get('scc_key') or witness.get('scc_id')} raw={witness.get('raw_doc_id')}"
        )
        excerpt = item.get("source_excerpt") or {}
        excerpt_lines = excerpt.get("lines") or []
        if excerpt_lines:
            sample = " ".join(str(row.get("text") or "").strip() for row in excerpt_lines[:2]).strip()
            if sample:
                lines.append(f"  source: {sample[:220]}")
    return "\n".join(lines)


def build_bee_prompt(goal: dict[str, Any], proof_state: dict[str, Any], gravity_context: dict[str, Any]) -> str:
    return (
        "You are a proof bee for info-geometry-lean.\n"
        "Return exactly one Lean tactic or a short tactic block.\n"
        "Do not claim proof success; propose only a tactic to test.\n"
        "Output format:\n"
        "TACTIC: <Lean tactic text>\n"
        "RATIONALE: <one sentence>\n\n"
        f"Goal target: {goal.get('target_pretty') or goal.get('canonical_shape') or goal.get('entity_key')}\n"
        f"Module hint: {goal.get('module') or 'none'}\n"
        f"Current proof state:\n{proof_state.get('proof_state') or '(no proof state)'}\n\n"
        f"Gravitational context:\n{summarize_gravity_context(gravity_context)}\n"
    )


def extract_tactic(text: str) -> str:
    match = re.search(r"(?im)^TACTIC:\s*(.+)$", text)
    if match:
        return match.group(1).strip()
    fenced = re.search(r"```(?:lean)?\n(.*?)```", text, flags=re.DOTALL)
    if fenced:
        return fenced.group(1).strip()
    first = text.strip().splitlines()
    return first[0].strip() if first else ""


def propose_tactic(config: BeeConfig, goal: dict[str, Any], proof_state: dict[str, Any], gravity_context: dict[str, Any]) -> str:
    if config.tactic_override:
        return config.tactic_override.strip()
    prompt = build_bee_prompt(goal, proof_state, gravity_context)
    response = call_openai_compatible(
        base_url=config.model_base_url,
        model=config.model_name,
        api_key=config.api_key,
        prompt=prompt,
        timeout=config.timeout,
        max_tokens=220,
    )
    text = ""
    choices = response.get("choices") or []
    if choices:
        message = choices[0].get("message") or {}
        text = str(message.get("content") or message.get("reasoning_content") or "")
    tactic = extract_tactic(text)
    if not tactic:
        raise RuntimeError("model returned no tactic")
    return tactic


def build_deadend_doc(goal: dict[str, Any], task: dict[str, Any], *, worker_id: str, tactic: str, failure_kind: str, verification: dict[str, Any], gravity_path: Path, elapsed_wall_s: float, lean_latency_s: float) -> dict[str, Any]:
    key = queue_tool.stable_key(
        "deadend",
        str(goal.get("_key")),
        tactic,
        failure_kind,
        str(task.get("claim_count") or 0),
    )
    output = ((verification.get("lean") or {}).get("stdout") or "") + ((verification.get("lean") or {}).get("stderr") or "")
    return {
        "_key": key,
        "schema": "info_geometry.hive_deadend.v1",
        "goal_key": goal.get("_key"),
        "goal_hash_shape": goal.get("goal_hash_shape"),
        "task_key": task.get("_key"),
        "worker_id": worker_id,
        "const_name": None,
        "attempted_tactic": tactic,
        "attempted_tactic_family": tactic.split()[0] if tactic.split() else tactic,
        "local_context_slice": parse_context(goal),
        "failure_kind": failure_kind,
        "retry_policy": {"max_attempts": goal.get("max_attempts") or DEFAULT_MAX_ATTEMPTS},
        "blocked_by_dependency": None,
        "verification_output": output[-4000:],
        "gravity_context_path": str(gravity_path),
        "metabolic_cost": {
            "wall_time_s": round(elapsed_wall_s, 6),
            "lean_verification_latency_s": round(lean_latency_s, 6),
            "retrieval_breadth": DEFAULT_TOP_K,
            "retries_before_closure": int((task.get("claim_count") or 1) - 1),
            "proof_depth": len([line for line in tactic.splitlines() if line.strip()]),
        },
        "state_taxonomy": ["retrieved", "proposed", "checked", "deadend"],
        "created_at": utc_now(),
    }


def build_fossil_record(goal: dict[str, Any], task: dict[str, Any], *, worker_id: str, tactic: str, gravity_path: Path, elapsed_wall_s: float, lean_latency_s: float) -> dict[str, Any]:
    const_name = f"hive.{sanitize_identifier(str(goal.get('module') or 'goal'))}.{task.get('_key')}"
    packet = {
        "artifactKind": "DiamondFossil",
        "space": "logos",
        "constName": const_name,
        "declarationKind": "theorem",
        "fullTypePretty": str(goal.get("target_pretty") or goal.get("canonical_shape") or goal.get("entity_key") or ""),
        "conclusionPretty": str(goal.get("target_pretty") or goal.get("canonical_shape") or goal.get("entity_key") or ""),
        "kernelStatus": "verified",
        "axiomsUsed": [],
        "proofTactic": tactic,
        "goalKey": goal.get("_key"),
        "taskKey": task.get("_key"),
        "workerId": worker_id,
        "gravityContextPath": str(gravity_path),
        "metabolicCost": {
            "wall_time_s": round(elapsed_wall_s, 6),
            "lean_verification_latency_s": round(lean_latency_s, 6),
            "proof_depth": len([line for line in tactic.splitlines() if line.strip()]),
        },
        "stateTaxonomy": ["retrieved", "proposed", "checked", "fossilized"],
    }
    canonical_shape = str(goal.get("canonical_shape") or goal.get("target_pretty") or goal.get("entity_key") or "")
    packet_bytes = json.dumps(packet, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    import hashlib
    return {
        "schema": "info_geometry.hive_memory.v1",
        "source": "hive-bee",
        "line_number": 0,
        "packet_index": 0,
        "artifact_kind": "DiamondFossil",
        "space": "logos",
        "entity_key": const_name,
        "canonical_shape": canonical_shape,
        "packet_sha256": hashlib.sha256(packet_bytes).hexdigest(),
        "shape_sha256": hashlib.sha256(canonical_shape.encode("utf-8")).hexdigest(),
        "packet": packet,
    }


def fossilize_success(config: BeeConfig, attempt: BeeAttempt) -> dict[str, Any]:
    record = build_fossil_record(
        attempt.goal,
        attempt.task,
        worker_id=config.worker_id,
        tactic=attempt.proposed_tactic,
        gravity_path=attempt.gravity_path,
        elapsed_wall_s=attempt.elapsed_wall_s,
        lean_latency_s=attempt.lean_latency_s,
    )
    fossil_doc = queue_tool.build_fossil_doc(record)
    event_doc = queue_tool.build_event_doc(record)
    queue_tool.import_rows(config.hive_endpoint, config.hive_database, config.hive_username, config.hive_password, "hive_fossils", [fossil_doc])
    queue_tool.import_rows(config.hive_endpoint, config.hive_database, config.hive_username, config.hive_password, "hive_events", [event_doc])
    queue_tool.import_rows(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        "hive_event_about",
        [queue_tool.build_event_edge(event_doc, "hive_fossils", fossil_doc["_key"])],
    )
    closed_edge = {
        "_key": queue_tool.stable_key("closedby", attempt.goal["_key"], fossil_doc["_key"]),
        "_from": f"hive_goals/{attempt.goal['_key']}",
        "_to": f"hive_fossils/{fossil_doc['_key']}",
        "schema": "info_geometry.hive_goal_closed_by.v1",
        "role": "closed_by",
        "created_at": utc_now(),
    }
    queue_tool.import_rows(config.hive_endpoint, config.hive_database, config.hive_username, config.hive_password, "hive_goal_closed_by", [closed_edge])
    updated_goal = queue_tool.update_goal_status(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        goal_key_value=str(attempt.goal["_key"]),
        status="closed",
        extra_fields={
            "closed_by_fossil_key": fossil_doc["_key"],
            "last_verified_tactic": attempt.proposed_tactic,
            "bee_state": "fossilized",
        },
    )
    updated_task = queue_tool.complete_task(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        task_key_value=str(attempt.task["_key"]),
        worker_id=config.worker_id,
    )
    return {"fossil": fossil_doc, "event": event_doc, "closed_edge": closed_edge, "goal": updated_goal, "task": updated_task}


def record_deadend(config: BeeConfig, attempt: BeeAttempt, failure_kind: str) -> dict[str, Any]:
    deadend_doc = build_deadend_doc(
        attempt.goal,
        attempt.task,
        worker_id=config.worker_id,
        tactic=attempt.proposed_tactic,
        failure_kind=failure_kind,
        verification=attempt.verification,
        gravity_path=attempt.gravity_path,
        elapsed_wall_s=attempt.elapsed_wall_s,
        lean_latency_s=attempt.lean_latency_s,
    )
    queue_tool.import_rows(config.hive_endpoint, config.hive_database, config.hive_username, config.hive_password, "hive_deadends", [deadend_doc])
    rejection_edge = {
        "_key": queue_tool.stable_key("rejectedby", attempt.goal["_key"], deadend_doc["_key"]),
        "_from": f"hive_goals/{attempt.goal['_key']}",
        "_to": f"hive_deadends/{deadend_doc['_key']}",
        "schema": "info_geometry.hive_goal_rejected_by.v1",
        "role": "rejected_by",
        "created_at": utc_now(),
    }
    queue_tool.import_rows(config.hive_endpoint, config.hive_database, config.hive_username, config.hive_password, "hive_goal_rejected_by", [rejection_edge])
    return {"deadend": deadend_doc, "rejection_edge": rejection_edge}


def max_attempts(goal: dict[str, Any]) -> int:
    value = goal.get("max_attempts") or goal.get("retry_policy", {}).get("max_attempts")
    try:
        return max(1, int(value))
    except Exception:  # noqa: BLE001
        return DEFAULT_MAX_ATTEMPTS


def fetch_claimed_task_and_goal(config: BeeConfig) -> tuple[dict[str, Any], dict[str, Any]] | tuple[None, None]:
    queue_tool.heartbeat_worker(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        worker_id=config.worker_id,
        capabilities=["gravity-retrieval", "lean-verification", "fossilization", "deadend-memory"],
        queues=[config.queue_name],
    )
    task = queue_tool.claim_next_task(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        worker_id=config.worker_id,
        queue_name=config.queue_name,
        lease_seconds=config.lease_seconds,
    )
    if not task:
        return None, None
    goal = queue_tool.get_goal_for_task(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        task_key_value=str(task["_key"]),
    )
    if not goal:
        queue_tool.fail_task(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.worker_id,
            error_message="claimed task has no goal document",
        )
        return None, None
    return task, goal


def run_one(config: BeeConfig) -> dict[str, Any]:
    task, goal = fetch_claimed_task_and_goal(config)
    if not task or not goal:
        return {"status": "idle", "worker_id": config.worker_id, "queue_name": config.queue_name}
    start = time.time()
    queue_tool.update_goal_status(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        goal_key_value=str(goal["_key"]),
        status="retrieved",
        extra_fields={"bee_state": "retrieved", "claimed_by": config.worker_id},
    )
    gravity_context, gravity_path, gravity_error = run_gravity_retrieval(config, goal, str(task["_key"]))
    if gravity_error or not gravity_context:
        queue_tool.requeue_task(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.worker_id,
            error_message=f"gravity retrieval failed: {gravity_error}",
        )
        queue_tool.update_goal_status(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            goal_key_value=str(goal["_key"]),
            status="requeued",
            extra_fields={"bee_state": "requeued", "last_gravity_error": gravity_error},
        )
        return {"status": "requeued", "task": task, "goal": goal, "error": gravity_error}
    proof_state = get_proof_state(
        str(goal.get("target_pretty") or goal.get("canonical_shape") or goal.get("entity_key") or ""),
        imports=parse_imports(goal),
        context=parse_context(goal),
        timeout=config.timeout,
    )
    if proof_state.get("status") != "ok":
        queue_tool.fail_task(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.worker_id,
            error_message="could not obtain Lean proof state",
        )
        queue_tool.update_goal_status(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            goal_key_value=str(goal["_key"]),
            status="failed",
            extra_fields={"bee_state": "failed", "last_proof_state_error": proof_state},
        )
        return {"status": "failed", "task": task, "goal": goal, "proof_state": proof_state}
    queue_tool.update_goal_status(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        goal_key_value=str(goal["_key"]),
        status="proposed",
        extra_fields={"bee_state": "proposed", "gravity_context_path": str(gravity_path)},
    )
    tactic = propose_tactic(config, goal, proof_state, gravity_context)
    lean_start = time.time()
    verification = apply_tactic(
        str(goal.get("target_pretty") or goal.get("canonical_shape") or goal.get("entity_key") or ""),
        tactic,
        imports=parse_imports(goal),
        context=parse_context(goal),
        timeout=config.timeout,
    )
    lean_latency = time.time() - lean_start
    attempt = BeeAttempt(
        task=task,
        goal=goal,
        proof_state=proof_state,
        gravity_context=gravity_context,
        gravity_path=gravity_path,
        proposed_tactic=tactic,
        verification=verification,
        elapsed_wall_s=time.time() - start,
        lean_latency_s=lean_latency,
    )
    queue_tool.update_goal_status(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        goal_key_value=str(goal["_key"]),
        status="checked",
        extra_fields={"bee_state": "checked", "last_proposed_tactic": tactic},
    )
    if verification.get("status") == "success":
        fossil = fossilize_success(config, attempt)
        return {"status": "fossilized", "task": task, "goal": goal, "tactic": tactic, "fossil": fossil}
    rejection = record_deadend(config, attempt, "lean_verification_failure")
    attempts = int(task.get("claim_count") or 1)
    if attempts < max_attempts(goal):
        queue_tool.requeue_task(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.worker_id,
            error_message="tactic failed verification; requeued",
        )
        queue_tool.update_goal_status(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            goal_key_value=str(goal["_key"]),
            status="requeued",
            extra_fields={"bee_state": "requeued", "last_deadend_key": rejection["deadend"]["_key"]},
        )
        return {"status": "requeued", "task": task, "goal": goal, "tactic": tactic, "deadend": rejection}
    queue_tool.fail_task(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        task_key_value=str(task["_key"]),
        worker_id=config.worker_id,
        error_message="maximum attempts reached after Lean verification failures",
    )
    queue_tool.update_goal_status(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        goal_key_value=str(goal["_key"]),
        status="deadend",
        extra_fields={"bee_state": "deadend", "last_deadend_key": rejection["deadend"]["_key"]},
    )
    return {"status": "deadend", "task": task, "goal": goal, "tactic": tactic, "deadend": rejection}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hive-endpoint", default=DEFAULT_HIVE_ENDPOINT)
    parser.add_argument("--hive-database", default=DEFAULT_HIVE_DATABASE)
    parser.add_argument("--hive-username", default=DEFAULT_HIVE_USERNAME)
    parser.add_argument("--hive-password", default=DEFAULT_HIVE_PASSWORD)
    parser.add_argument("--queue-name", default=DEFAULT_QUEUE)
    parser.add_argument("--worker-id", default=DEFAULT_WORKER_ID)
    parser.add_argument("--lease-seconds", type=int, default=DEFAULT_LEASE_SECONDS)
    parser.add_argument("--gravity-base-url", default=DEFAULT_GRAVITY_BASE_URL)
    parser.add_argument("--gravity-database", default=DEFAULT_GRAVITY_DATABASE)
    parser.add_argument("--gravity-top-k", type=int, default=DEFAULT_TOP_K)
    parser.add_argument("--model-base-url", default=DEFAULT_MODEL_BASE_URL)
    parser.add_argument("--model-name", default=DEFAULT_MODEL)
    parser.add_argument("--api-key", default=DEFAULT_API_KEY)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--tactic-override", default=None)
    parser.add_argument("--once", action="store_true", help="run one claim/attempt cycle and exit")
    parser.add_argument("--poll-interval", type=int, default=15)
    return parser.parse_args()


def config_from_args(args: argparse.Namespace) -> BeeConfig:
    return BeeConfig(
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
        timeout=int(args.timeout),
        tactic_override=str(args.tactic_override).strip() if args.tactic_override else None,
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
