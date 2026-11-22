#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import subprocess
import sys
import time
from pathlib import Path
from typing import Any
from urllib.error import URLError

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.arango_env import (  # noqa: E402
    alexandria_arango_database,
    alexandria_arango_endpoint,
    alexandria_arango_password,
    alexandria_arango_username,
    guard_alexandria_target,
    load_alexandria_arango_env,
    load_repo_arango_env,
)
from tools.infra import hive_arango_queue as queue_tool  # noqa: E402

load_repo_arango_env(ROOT)
load_alexandria_arango_env(ROOT)

DEFAULT_HIVE_ENDPOINT = queue_tool.DEFAULT_ENDPOINT
DEFAULT_HIVE_DATABASE = queue_tool.DEFAULT_DATABASE
DEFAULT_HIVE_USERNAME = queue_tool.DEFAULT_USERNAME
DEFAULT_HIVE_PASSWORD = queue_tool.DEFAULT_PASSWORD
DEFAULT_QUEUE = "research-digest"
DEFAULT_WORKER_ID = "research-digest-worker-001"
DEFAULT_LEASE_SECONDS = queue_tool.DEFAULT_LEASE_SECONDS
ALEX_ENDPOINT = alexandria_arango_endpoint()
ALEX_DATABASE = alexandria_arango_database(os.environ.get("ALEXANDRIA_DATABASE", "alexandria"))
ALEX_USERNAME = alexandria_arango_username()
ALEX_PASSWORD = alexandria_arango_password("alexandria_root")
ARXIV_RE = re.compile(r"\b(?:[a-z\-]+/\d{7}|\d{4}\.\d{4,5})(?:v\d+)?\b", re.I)
MOTHERBEE_CONTEXT = ROOT / "artifacts" / "alexandria" / "hive_research_digest" / "motherbee_context_2026-04-22.md"
BASE_DIR = ROOT / "artifacts" / "alexandria" / "research_digest_runs"
FETCH = ROOT / "tools" / "alexandria" / "fetch_arxiv_corpus.py"
INGEST = ROOT / "tools" / "alexandria" / "semantic_ingest.py"
ARANGO = ROOT / "tools" / "alexandria" / "arango_ingest.py"
RETRIEVE = ROOT / "tools" / "alexandria" / "retrieve_context.py"


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--hive-endpoint", default=DEFAULT_HIVE_ENDPOINT)
    p.add_argument("--hive-database", default=DEFAULT_HIVE_DATABASE)
    p.add_argument("--hive-username", default=DEFAULT_HIVE_USERNAME)
    p.add_argument("--hive-password", default=DEFAULT_HIVE_PASSWORD)
    p.add_argument("--alexandria-endpoint", default=ALEX_ENDPOINT)
    p.add_argument("--alexandria-database", default=ALEX_DATABASE)
    p.add_argument("--alexandria-username", default=ALEX_USERNAME)
    p.add_argument("--alexandria-password", default=ALEX_PASSWORD)
    p.add_argument("--queue-name", default=DEFAULT_QUEUE)
    p.add_argument("--worker-id", default=DEFAULT_WORKER_ID)
    p.add_argument("--lease-seconds", type=int, default=DEFAULT_LEASE_SECONDS)
    p.add_argument("--timeout", type=int, default=300)
    p.add_argument("--once", action="store_true")
    p.add_argument("--poll-interval", type=int, default=30)
    args = p.parse_args()
    if args.lease_seconds < 1:
        p.error("--lease-seconds must be >= 1")
    if args.timeout < 1:
        p.error("--timeout must be >= 1")
    if args.poll_interval < 1:
        p.error("--poll-interval must be >= 1")
    return args


def sanitize(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]+", "_", text).strip("_") or "task"


def shell(command: str, timeout: int) -> tuple[int, str]:
    proc = subprocess.run(command, shell=True, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    return proc.returncode, proc.stdout


def extract_ids(goal: dict[str, Any]) -> list[str]:
    text = " ".join(str(goal.get(k) or "") for k in ["target_pretty", "canonical_shape", "goal_hash_shape", "module"])
    out = []
    seen = set()
    for m in ARXIV_RE.findall(text):
        if m not in seen:
            seen.add(m)
            out.append(m)
    return out


def build_run_dir(goal: dict[str, Any], task: dict[str, Any]) -> Path:
    run_dir = BASE_DIR / f"{sanitize(str(goal.get('module') or 'goal'))}-{sanitize(str(task.get('_key') or 'task'))}"
    run_dir.mkdir(parents=True, exist_ok=True)
    return run_dir


def import_event(hive_endpoint: str, hive_database: str, hive_username: str, hive_password: str, *, goal: dict[str, Any], task: dict[str, Any], status: str, payload: dict[str, Any]) -> None:
    now = queue_tool.iso_now()
    event = {
        "_key": queue_tool.stable_key("event", str(goal.get("_key")), str(task.get("_key")), status, now),
        "schema": "info_geometry.hive_research_event.v1",
        "artifact_kind": "ResearchDigest",
        "space": "research-digest",
        "entity_key": goal.get("entity_key"),
        "canonical_shape": goal.get("canonical_shape"),
        "packet_sha256": queue_tool.stable_key("sha", json.dumps(payload, sort_keys=True, ensure_ascii=False)),
        "shape_sha256": goal.get("goal_hash_shape"),
        "source": "research-digest-worker",
        "line_number": None,
        "packet_index": 0,
        "packet": payload,
        "created_at": now,
    }
    edge = {
        "_key": queue_tool.stable_key("eventabout", event["_key"], "hive_goals", str(goal.get("_key"))),
        "_from": f"hive_events/{event['_key']}",
        "_to": f"hive_goals/{goal['_key']}",
        "schema": "info_geometry.hive_event_about.v1",
        "role": "describes",
        "created_at": now,
    }
    queue_tool.import_rows(hive_endpoint, hive_database, hive_username, hive_password, "hive_events", [event])
    queue_tool.import_rows(hive_endpoint, hive_database, hive_username, hive_password, "hive_event_about", [edge])


def _resolve_alexandria_target(args: argparse.Namespace) -> tuple[str, str, str, str]:
    raw_endpoint = getattr(args, "alexandria_endpoint", None)
    raw_database = getattr(args, "alexandria_database", None)
    raw_username = getattr(args, "alexandria_username", None)
    raw_password = getattr(args, "alexandria_password", None)
    endpoint = str(ALEX_ENDPOINT if raw_endpoint is None else raw_endpoint).strip()
    database = str(ALEX_DATABASE if raw_database is None else raw_database).strip()
    username = str(ALEX_USERNAME if raw_username is None else raw_username)
    password = str(ALEX_PASSWORD if raw_password is None else raw_password)
    if not endpoint:
        raise ValueError("Alexandria endpoint must not be empty")
    if not database:
        raise ValueError("Alexandria database must not be empty")
    guard_alexandria_target(endpoint, database)
    return endpoint, database, username, password


def process_task(args: argparse.Namespace, task: dict[str, Any], goal: dict[str, Any]) -> dict[str, Any]:
    run_dir = build_run_dir(goal, task)
    context_file = None
    outputs: dict[str, Any] = {"goal_key": goal.get("_key"), "task_key": task.get("_key"), "module": goal.get("module"), "run_dir": str(run_dir)}
    query_text = str(goal.get("target_pretty") or goal.get("canonical_shape") or "")
    if goal.get("module") == "MotherBeeContext" and MOTHERBEE_CONTEXT.exists():
        alex_endpoint, alex_database, alex_username, alex_password = _resolve_alexandria_target(args)
        outputs["arxiv_ids"] = []
        cmd = (
            f"{shlex.quote(sys.executable)} {shlex.quote(str(INGEST))} --input {shlex.quote(str(MOTHERBEE_CONTEXT))} --output {shlex.quote(str(run_dir / 'digest'))} && "
            f"{shlex.quote(sys.executable)} {shlex.quote(str(ARANGO))} --input-dir {shlex.quote(str(run_dir / 'digest'))} --endpoint {shlex.quote(alex_endpoint)} --database {shlex.quote(alex_database)} --username {shlex.quote(alex_username)} --password {shlex.quote(alex_password)} && "
            f"{shlex.quote(sys.executable)} {shlex.quote(str(RETRIEVE))} --query {shlex.quote(query_text)} --input-dir {shlex.quote(str(run_dir / 'digest'))} > {shlex.quote(str(run_dir / 'context_packet.json'))}"
        )
        code, out = shell(cmd, args.timeout)
        (run_dir / 'worker.log').write_text(out, encoding='utf-8')
        outputs["pipeline_output"] = out[-4000:]
        if code != 0:
            raise RuntimeError(out.strip() or f"pipeline exited {code}")
        context_file = run_dir / 'context_packet.json'
    else:
        ids = extract_ids(goal)
        outputs["arxiv_ids"] = ids
        if ids:
            alex_endpoint, alex_database, alex_username, alex_password = _resolve_alexandria_target(args)
            ids_file = run_dir / "arxiv_ids.txt"
            ids_file.write_text("\n".join(ids) + "\n", encoding="utf-8")
            cmd = (
                f"{shlex.quote(sys.executable)} {shlex.quote(str(FETCH))} --ids-file {shlex.quote(str(ids_file))} --output-dir {shlex.quote(str(run_dir / 'cache'))} && "
                f"{shlex.quote(sys.executable)} {shlex.quote(str(INGEST))} --input {shlex.quote(str(run_dir / 'cache'))} --output {shlex.quote(str(run_dir / 'digest'))} && "
                f"{shlex.quote(sys.executable)} {shlex.quote(str(ARANGO))} --input-dir {shlex.quote(str(run_dir / 'digest'))} --endpoint {shlex.quote(alex_endpoint)} --database {shlex.quote(alex_database)} --username {shlex.quote(alex_username)} --password {shlex.quote(alex_password)} && "
                f"{shlex.quote(sys.executable)} {shlex.quote(str(RETRIEVE))} --query {shlex.quote(query_text)} --input-dir {shlex.quote(str(run_dir / 'digest'))} > {shlex.quote(str(run_dir / 'context_packet.json'))}"
            )
            code, out = shell(cmd, args.timeout)
            (run_dir / 'worker.log').write_text(out, encoding='utf-8')
            outputs["pipeline_output"] = out[-4000:]
            if code != 0:
                raise RuntimeError(out.strip() or f"pipeline exited {code}")
            context_file = run_dir / 'context_packet.json'
        else:
            note = run_dir / 'note.txt'
            note.write_text(goal.get('target_pretty') or goal.get('canonical_shape') or 'No arXiv id or known context source', encoding='utf-8')
            outputs["note"] = str(note)
    if context_file and context_file.exists():
        outputs["context_packet"] = str(context_file)
    return outputs


def run_once(args: argparse.Namespace) -> dict[str, Any]:
    queue_tool.init_schema(args.hive_endpoint, args.hive_database, args.hive_username, args.hive_password)
    queue_tool.heartbeat_worker(args.hive_endpoint, args.hive_database, args.hive_username, args.hive_password, worker_id=args.worker_id, capabilities=["research-digest", "alexandria", "arxiv-fetch"], queues=[args.queue_name])
    task = queue_tool.claim_next_task(args.hive_endpoint, args.hive_database, args.hive_username, args.hive_password, worker_id=args.worker_id, queue_name=args.queue_name, lease_seconds=args.lease_seconds)
    if not task:
        return {"status": "idle", "queue_name": args.queue_name, "worker_id": args.worker_id}
    goal = queue_tool.get_goal_for_task(args.hive_endpoint, args.hive_database, args.hive_username, args.hive_password, task_key_value=str(task["_key"]))
    if not goal:
        queue_tool.fail_task(args.hive_endpoint, args.hive_database, args.hive_username, args.hive_password, task_key_value=str(task['_key']), worker_id=args.worker_id, error_message='goal missing')
        return {"status": "failed", "reason": "goal missing", "task": task}
    queue_tool.update_goal_status(args.hive_endpoint, args.hive_database, args.hive_username, args.hive_password, goal_key_value=str(goal['_key']), status='retrieved', extra_fields={'worker_id': args.worker_id, 'bee_state': 'research_retrieved'})
    try:
        outputs = process_task(args, task, goal)
        queue_tool.complete_task(args.hive_endpoint, args.hive_database, args.hive_username, args.hive_password, task_key_value=str(task['_key']), worker_id=args.worker_id)
        queue_tool.update_goal_status(args.hive_endpoint, args.hive_database, args.hive_username, args.hive_password, goal_key_value=str(goal['_key']), status='completed', extra_fields={'bee_state': 'research_completed', 'research_outputs': outputs})
        import_event(args.hive_endpoint, args.hive_database, args.hive_username, args.hive_password, goal=goal, task=task, status='completed', payload=outputs)
        return {"status": "completed", "task": task, "goal": goal, "outputs": outputs}
    except Exception as exc:
        queue_tool.fail_task(args.hive_endpoint, args.hive_database, args.hive_username, args.hive_password, task_key_value=str(task['_key']), worker_id=args.worker_id, error_message=str(exc))
        queue_tool.update_goal_status(args.hive_endpoint, args.hive_database, args.hive_username, args.hive_password, goal_key_value=str(goal['_key']), status='failed', extra_fields={'bee_state': 'research_failed', 'last_error': str(exc)})
        import_event(args.hive_endpoint, args.hive_database, args.hive_username, args.hive_password, goal=goal, task=task, status='failed', payload={'error': str(exc)})
        return {"status": "failed", "task": task, "goal": goal, "error": str(exc)}


def main() -> int:
    args = parse_args()
    try:
        _resolve_alexandria_target(args)
    except ValueError as exc:
        print(json.dumps({"error": str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 2
    while True:
        try:
            result = run_once(args)
        except (URLError, OSError, RuntimeError, ValueError) as exc:
            print(json.dumps({"error": str(exc)}, ensure_ascii=False), file=sys.stderr)
            return 1
        print(json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True))
        if args.once:
            return 0
        time.sleep(max(1, int(args.poll_interval)))


if __name__ == '__main__':
    raise SystemExit(main())
