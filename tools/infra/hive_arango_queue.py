#!/usr/bin/env python3
"""MotherBee queue-oriented ArangoDB manifold bootstrap for Hive agents.

This tool operationalizes the queue/firewall portions of hive.md without inventing
new Lean semantics. It provides:

- schema initialization for a live Hive database
- worker heartbeats for bee registration
- queue-backed task enqueue/claim/complete/fail operations
- seeding from repo-native HIVE_JSON JSONL artifacts produced by ingest_hive_json.py

The truth boundary remains Lean-owned: this script only stores Lean-emitted packets,
queue state, and lightweight routing metadata.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Iterable
from urllib.error import HTTPError
from urllib.parse import quote
from urllib.request import Request, urlopen

DEFAULT_ENDPOINT = "http://127.0.0.1:8530"
DEFAULT_DATABASE = "hive_live"
DEFAULT_USERNAME = "root"
DEFAULT_PASSWORD = "alexandria_root"
DEFAULT_QUEUE = "proof-search"
DEFAULT_LEASE_SECONDS = 900

GOAL_ARTIFACT_KINDS = {"InfoTreeArtifact"}
FOSSIL_ARTIFACT_KINDS = {"DiamondFossil", "TheoremFossil"}


@dataclass(frozen=True)
class CollectionSpec:
    name: str
    edge: bool = False


@dataclass(frozen=True)
class IndexSpec:
    collection: str
    fields: tuple[str, ...]
    unique: bool = False
    sparse: bool = True
    name: str | None = None


COLLECTIONS: tuple[CollectionSpec, ...] = (
    CollectionSpec("hive_goals"),
    CollectionSpec("hive_fossils"),
    CollectionSpec("hive_deadends"),
    CollectionSpec("hive_replay_packets"),
    CollectionSpec("hive_tasks"),
    CollectionSpec("hive_workers"),
    CollectionSpec("hive_events"),
    CollectionSpec("hive_goal_closed_by", edge=True),
    CollectionSpec("hive_goal_rejected_by", edge=True),
    CollectionSpec("hive_task_for_goal", edge=True),
    CollectionSpec("hive_event_about", edge=True),
)

INDEXES: tuple[IndexSpec, ...] = (
    IndexSpec("hive_goals", ("goal_hash_shape",), name="goal_hash_shape_idx"),
    IndexSpec("hive_goals", ("queue_name", "status"), name="goal_queue_status_idx"),
    IndexSpec("hive_fossils", ("conclusion_hash_shape",), name="fossil_conclusion_shape_idx"),
    IndexSpec("hive_fossils", ("const_name",), name="fossil_const_name_idx"),
    IndexSpec("hive_deadends", ("goal_hash_shape", "const_name"), name="deadend_goal_const_idx"),
    IndexSpec("hive_replay_packets", ("fossil_key",), name="replay_fossil_key_idx"),
    IndexSpec("hive_replay_packets", ("goal_key", "task_key"), name="replay_goal_task_idx"),
    IndexSpec("hive_tasks", ("queue_name", "status", "priority"), name="task_queue_status_priority_idx"),
    IndexSpec("hive_tasks", ("lease_expires_at",), name="task_lease_expiry_idx"),
    IndexSpec("hive_tasks", ("goal_key",), name="task_goal_key_idx"),
    IndexSpec("hive_workers", ("worker_id",), unique=True, sparse=False, name="worker_id_idx"),
    IndexSpec("hive_events", ("packet_sha256",), unique=True, sparse=False, name="event_packet_sha_idx"),
    IndexSpec("hive_events", ("artifact_kind", "space"), name="event_kind_space_idx"),
)


def iso_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")



def iso_after(seconds: int) -> str:
    return (datetime.now(timezone.utc) + timedelta(seconds=int(seconds))).replace(microsecond=0).isoformat().replace(
        "+00:00", "Z"
    )



def auth_header(username: str, password: str) -> str:
    token = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
    return f"Basic {token}"



def request_json(
    method: str,
    url: str,
    *,
    username: str,
    password: str,
    payload: Any | None = None,
) -> Any:
    body = None if payload is None else json.dumps(payload, ensure_ascii=False).encode("utf-8")
    req = Request(url, data=body, method=method)
    req.add_header("Authorization", auth_header(username, password))
    req.add_header("Accept", "application/json")
    if body is not None:
        req.add_header("Content-Type", "application/json")
    try:
        with urlopen(req) as resp:
            raw = resp.read().decode("utf-8")
            return json.loads(raw) if raw else {}
    except HTTPError as exc:
        raw = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {exc.code} {url}: {raw}") from exc



def sys_url(endpoint: str, path: str) -> str:
    return f"{endpoint.rstrip('/')}/{path.lstrip('/')}"



def db_url(endpoint: str, database: str, path: str) -> str:
    return f"{endpoint.rstrip('/')}/_db/{quote(database)}/{path.lstrip('/')}"



def ensure_database(endpoint: str, database: str, username: str, password: str) -> None:
    dbs = request_json("GET", sys_url(endpoint, "/_api/database"), username=username, password=password)
    if database in dbs.get("result", []):
        return
    request_json(
        "POST",
        sys_url(endpoint, "/_api/database"),
        username=username,
        password=password,
        payload={"name": database},
    )



def list_collections(endpoint: str, database: str, username: str, password: str) -> set[str]:
    payload = request_json(
        "GET",
        db_url(endpoint, database, "/_api/collection"),
        username=username,
        password=password,
    )
    return {
        str(row.get("name"))
        for row in payload.get("result", [])
        if isinstance(row, dict) and row.get("name")
    }



def ensure_collection(endpoint: str, database: str, username: str, password: str, spec: CollectionSpec) -> None:
    current = list_collections(endpoint, database, username, password)
    if spec.name in current:
        return
    request_json(
        "POST",
        db_url(endpoint, database, "/_api/collection"),
        username=username,
        password=password,
        payload={"name": spec.name, "type": 3 if spec.edge else 2, "waitForSync": False},
    )



def ensure_index(endpoint: str, database: str, username: str, password: str, spec: IndexSpec) -> None:
    payload = {
        "type": "persistent",
        "fields": list(spec.fields),
        "unique": spec.unique,
        "sparse": spec.sparse,
    }
    if spec.name:
        payload["name"] = spec.name
    try:
        request_json(
            "POST",
            db_url(endpoint, database, f"/_api/index?collection={quote(spec.collection)}"),
            username=username,
            password=password,
            payload=payload,
        )
    except RuntimeError as exc:
        message = str(exc)
        if '"errorNum":1210' in message or 'duplicate' in message.lower() or 'already exists' in message.lower():
            return
        raise



def collection_count(endpoint: str, database: str, username: str, password: str, collection: str) -> int:
    out = request_json(
        "GET",
        db_url(endpoint, database, f"/_api/collection/{quote(collection)}/count"),
        username=username,
        password=password,
    )
    count = out.get("count")
    return count if isinstance(count, int) else -1



def aql(endpoint: str, database: str, username: str, password: str, query: str, bind_vars: dict[str, Any] | None = None) -> list[dict[str, Any]]:
    payload = {"query": query, "bindVars": bind_vars or {}}
    out = request_json(
        "POST",
        db_url(endpoint, database, "/_api/cursor"),
        username=username,
        password=password,
        payload=payload,
    )
    result = out.get("result")
    return list(result) if isinstance(result, list) else []



def import_rows(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    collection: str,
    rows: list[dict[str, Any]],
) -> None:
    if not rows:
        return
    request_json(
        "POST",
        db_url(endpoint, database, f"/_api/document/{quote(collection)}?overwriteMode=replace&silent=false"),
        username=username,
        password=password,
        payload=rows,
    )



def stable_key(prefix: str, *parts: str) -> str:
    digest = hashlib.sha256("::".join(parts).encode("utf-8")).hexdigest()[:24]
    return f"{prefix}_{digest}"



def event_key(record: dict[str, Any]) -> str:
    packet_sha = str(record.get("packet_sha256") or "")
    return stable_key("event", packet_sha or json.dumps(record.get("packet", {}), sort_keys=True, ensure_ascii=False))



def goal_key(record: dict[str, Any]) -> str:
    return stable_key(
        "goal",
        str(record.get("entity_key") or "unknown"),
        str(record.get("canonical_shape") or ""),
        str(record.get("packet_sha256") or ""),
    )



def fossil_key(record: dict[str, Any]) -> str:
    packet = record.get("packet") or {}
    return stable_key(
        "fossil",
        str(packet.get("constName") or record.get("entity_key") or "unknown"),
        str(record.get("canonical_shape") or ""),
        str(record.get("packet_sha256") or ""),
    )



def task_key(goal_doc: dict[str, Any], queue_name: str) -> str:
    return stable_key("task", str(goal_doc["_key"]), queue_name)



def worker_key(worker_id: str) -> str:
    return stable_key("worker", worker_id)



def build_event_doc(record: dict[str, Any]) -> dict[str, Any]:
    packet = record.get("packet") or {}
    return {
        "_key": event_key(record),
        "schema": "info_geometry.hive_event.v1",
        "packet_sha256": record.get("packet_sha256"),
        "artifact_kind": record.get("artifact_kind"),
        "space": record.get("space"),
        "entity_key": record.get("entity_key"),
        "canonical_shape": record.get("canonical_shape"),
        "shape_sha256": record.get("shape_sha256"),
        "source": record.get("source"),
        "line_number": record.get("line_number"),
        "packet_index": record.get("packet_index"),
        "packet": packet,
        "created_at": iso_now(),
    }



def build_goal_doc(record: dict[str, Any], *, queue_name: str) -> dict[str, Any]:
    packet = record.get("packet") or {}
    return {
        "_key": goal_key(record),
        "schema": "info_geometry.hive_goal.v1",
        "queue_name": queue_name,
        "status": "open",
        "artifact_kind": record.get("artifact_kind"),
        "goal_hash_shape": record.get("shape_sha256"),
        "canonical_shape": record.get("canonical_shape"),
        "entity_key": record.get("entity_key"),
        "source": record.get("source"),
        "line_number": record.get("line_number"),
        "packet_sha256": record.get("packet_sha256"),
        "module": packet.get("module"),
        "goal_index": packet.get("goalIndex"),
        "target_pretty": packet.get("targetPretty"),
        "normalization_policy": packet.get("normalizationPolicy"),
        "fvar_policy": packet.get("fvarPolicy"),
        "created_at": iso_now(),
        "updated_at": iso_now(),
    }



def build_fossil_doc(record: dict[str, Any]) -> dict[str, Any]:
    packet = record.get("packet") or {}
    return {
        "_key": fossil_key(record),
        "schema": "info_geometry.hive_fossil.v1",
        "artifact_kind": record.get("artifact_kind"),
        "const_name": packet.get("constName"),
        "declaration_kind": packet.get("declarationKind"),
        "conclusion_hash_shape": record.get("shape_sha256"),
        "canonical_shape": record.get("canonical_shape"),
        "packet_sha256": record.get("packet_sha256"),
        "kernel_status": packet.get("kernelStatus"),
        "conclusion_pretty": packet.get("conclusionPretty"),
        "full_type_pretty": packet.get("fullTypePretty"),
        "axioms_used": packet.get("axiomsUsed", []),
        "created_at": iso_now(),
    }



def build_task_doc(goal_doc: dict[str, Any], *, queue_name: str, priority: float = 0.5) -> dict[str, Any]:
    now = iso_now()
    return {
        "_key": task_key(goal_doc, queue_name),
        "schema": "info_geometry.hive_task.v1",
        "queue_name": queue_name,
        "goal_key": goal_doc["_key"],
        "status": "pending",
        "priority": float(priority),
        "claim_count": 0,
        "worker_id": None,
        "lease_expires_at": None,
        "created_at": now,
        "updated_at": now,
    }



def build_task_edge(task_doc: dict[str, Any], goal_doc: dict[str, Any]) -> dict[str, Any]:
    return {
        "_key": stable_key("taskgoal", task_doc["_key"], goal_doc["_key"]),
        "_from": f"hive_tasks/{task_doc['_key']}",
        "_to": f"hive_goals/{goal_doc['_key']}",
        "schema": "info_geometry.hive_task_for_goal.v1",
        "role": "queued_goal",
        "created_at": iso_now(),
    }



def build_event_edge(event_doc: dict[str, Any], collection: str, key: str) -> dict[str, Any]:
    return {
        "_key": stable_key("eventabout", event_doc["_key"], collection, key),
        "_from": f"hive_events/{event_doc['_key']}",
        "_to": f"{collection}/{key}",
        "schema": "info_geometry.hive_event_about.v1",
        "role": "describes",
        "created_at": iso_now(),
    }



def iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_no}: expected JSON object")
            yield row



def seed_payloads(input_path: Path, *, queue_name: str, priority: float) -> dict[str, list[dict[str, Any]]]:
    docs: dict[str, list[dict[str, Any]]] = {
        "hive_goals": [],
        "hive_fossils": [],
        "hive_tasks": [],
        "hive_events": [],
        "hive_task_for_goal": [],
        "hive_event_about": [],
    }
    for record in iter_jsonl(input_path):
        event_doc = build_event_doc(record)
        docs["hive_events"].append(event_doc)
        artifact_kind = str(record.get("artifact_kind") or "")
        if artifact_kind in GOAL_ARTIFACT_KINDS:
            goal_doc = build_goal_doc(record, queue_name=queue_name)
            task_doc = build_task_doc(goal_doc, queue_name=queue_name, priority=priority)
            docs["hive_goals"].append(goal_doc)
            docs["hive_tasks"].append(task_doc)
            docs["hive_task_for_goal"].append(build_task_edge(task_doc, goal_doc))
            docs["hive_event_about"].append(build_event_edge(event_doc, "hive_goals", goal_doc["_key"]))
        elif artifact_kind in FOSSIL_ARTIFACT_KINDS:
            fossil_doc = build_fossil_doc(record)
            docs["hive_fossils"].append(fossil_doc)
            docs["hive_event_about"].append(build_event_edge(event_doc, "hive_fossils", fossil_doc["_key"]))
    return docs



def init_schema(endpoint: str, database: str, username: str, password: str) -> dict[str, Any]:
    ensure_database(endpoint, database, username, password)
    for spec in COLLECTIONS:
        ensure_collection(endpoint, database, username, password, spec)
    for spec in INDEXES:
        ensure_index(endpoint, database, username, password, spec)
    return schema_status(endpoint, database, username, password)



def schema_status(endpoint: str, database: str, username: str, password: str) -> dict[str, Any]:
    existing = list_collections(endpoint, database, username, password)
    counts = {
        spec.name: collection_count(endpoint, database, username, password, spec.name)
        for spec in COLLECTIONS
        if spec.name in existing
    }
    return {
        "schema": "info_geometry.hive_arango_queue.status.v1",
        "endpoint": endpoint,
        "database": database,
        "collections": sorted(existing & {spec.name for spec in COLLECTIONS}),
        "counts": counts,
    }



def heartbeat_worker(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    worker_id: str,
    capabilities: list[str],
    queues: list[str],
) -> dict[str, Any]:
    now = iso_now()
    doc = {
        "_key": worker_key(worker_id),
        "schema": "info_geometry.hive_worker.v1",
        "worker_id": worker_id,
        "status": "online",
        "capabilities": capabilities,
        "queues": queues,
        "last_seen_at": now,
        "updated_at": now,
    }
    import_rows(endpoint, database, username, password, "hive_workers", [doc])
    return doc



def enqueue_goal(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    queue_name: str,
    goal_hash_shape: str,
    canonical_shape: str,
    target_pretty: str,
    module: str,
    goal_index: int,
    priority: float,
) -> dict[str, Any]:
    now = iso_now()
    goal_doc = {
        "_key": stable_key("goal", goal_hash_shape, module, str(goal_index), canonical_shape),
        "schema": "info_geometry.hive_goal.v1",
        "queue_name": queue_name,
        "status": "open",
        "artifact_kind": "InfoTreeArtifact",
        "goal_hash_shape": goal_hash_shape,
        "canonical_shape": canonical_shape,
        "entity_key": f"{module}:{goal_index}",
        "source": "manual-enqueue",
        "line_number": None,
        "packet_sha256": None,
        "module": module,
        "goal_index": int(goal_index),
        "target_pretty": target_pretty,
        "normalization_policy": None,
        "fvar_policy": None,
        "created_at": now,
        "updated_at": now,
    }
    task_doc = build_task_doc(goal_doc, queue_name=queue_name, priority=priority)
    import_rows(endpoint, database, username, password, "hive_goals", [goal_doc])
    import_rows(endpoint, database, username, password, "hive_tasks", [task_doc])
    import_rows(endpoint, database, username, password, "hive_task_for_goal", [build_task_edge(task_doc, goal_doc)])
    return {"goal": goal_doc, "task": task_doc}



def claim_next_task(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    worker_id: str,
    queue_name: str,
    lease_seconds: int,
) -> dict[str, Any] | None:
    query = """
LET now = DATE_ISO8601(DATE_NOW())
FOR task IN @@tasks
  FILTER task.queue_name == @queue_name
  FILTER task.status == "pending" || (task.status == "leased" && task.lease_expires_at != null && task.lease_expires_at <= now)
  SORT task.priority DESC, task.created_at ASC
  LIMIT 1
  UPDATE task WITH {
    status: "leased",
    worker_id: @worker_id,
    lease_expires_at: DATE_ISO8601(DATE_ADD(DATE_NOW(), @lease_seconds, "second")),
    claim_count: TO_NUMBER(task.claim_count) + 1,
    claimed_at: now,
    updated_at: now
  } IN @@tasks
  OPTIONS { mergeObjects: false }
  RETURN NEW
""".strip()
    rows = aql(
        endpoint,
        database,
        username,
        password,
        query,
        {
            "@tasks": "hive_tasks",
            "queue_name": queue_name,
            "worker_id": worker_id,
            "lease_seconds": int(lease_seconds),
        },
    )
    return rows[0] if rows else None



def get_task_record(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    task_key_value: str,
) -> dict[str, Any] | None:
    rows = aql(
        endpoint,
        database,
        username,
        password,
        "FOR task IN @@tasks FILTER task._key == @task_key LIMIT 1 RETURN task",
        {"@tasks": "hive_tasks", "task_key": task_key_value},
    )
    return rows[0] if rows else None



def get_goal_for_task(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    task_key_value: str,
) -> dict[str, Any] | None:
    query = """
FOR task IN @@tasks
  FILTER task._key == @task_key
  LIMIT 1
  FOR goal IN @@goals
    FILTER goal._key == task.goal_key
    LIMIT 1
    RETURN goal
""".strip()
    rows = aql(
        endpoint,
        database,
        username,
        password,
        query,
        {"@tasks": "hive_tasks", "@goals": "hive_goals", "task_key": task_key_value},
    )
    return rows[0] if rows else None



def complete_task(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    task_key_value: str,
    worker_id: str,
) -> dict[str, Any] | None:
    query = """
LET now = DATE_ISO8601(DATE_NOW())
FOR task IN @@tasks
  FILTER task._key == @task_key
  FILTER task.worker_id == @worker_id
  LIMIT 1
  UPDATE task WITH {
    status: "completed",
    completed_at: now,
    lease_expires_at: null,
    updated_at: now
  } IN @@tasks
  OPTIONS { mergeObjects: true }
  RETURN NEW
""".strip()
    rows = aql(
        endpoint,
        database,
        username,
        password,
        query,
        {"@tasks": "hive_tasks", "task_key": task_key_value, "worker_id": worker_id},
    )
    return rows[0] if rows else None



def update_goal_status(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    goal_key_value: str,
    status: str,
    extra_fields: dict[str, Any] | None = None,
) -> dict[str, Any] | None:
    query = """
LET now = DATE_ISO8601(DATE_NOW())
FOR goal IN @@goals
  FILTER goal._key == @goal_key
  LIMIT 1
  UPDATE goal WITH MERGE({ status: @status, updated_at: now }, @extra) IN @@goals
  OPTIONS { mergeObjects: true }
  RETURN NEW
""".strip()
    rows = aql(
        endpoint,
        database,
        username,
        password,
        query,
        {
            "@goals": "hive_goals",
            "goal_key": goal_key_value,
            "status": status,
            "extra": extra_fields or {},
        },
    )
    return rows[0] if rows else None



def fail_task(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    task_key_value: str,
    worker_id: str,
    error_message: str,
) -> dict[str, Any] | None:
    query = """
LET now = DATE_ISO8601(DATE_NOW())
FOR task IN @@tasks
  FILTER task._key == @task_key
  FILTER task.worker_id == @worker_id
  LIMIT 1
  UPDATE task WITH {
    status: "failed",
    last_error: @error_message,
    failed_at: now,
    lease_expires_at: null,
    updated_at: now
  } IN @@tasks
  OPTIONS { mergeObjects: true }
  RETURN NEW
""".strip()
    rows = aql(
        endpoint,
        database,
        username,
        password,
        query,
        {
            "@tasks": "hive_tasks",
            "task_key": task_key_value,
            "worker_id": worker_id,
            "error_message": error_message,
        },
    )
    return rows[0] if rows else None



def requeue_task(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    task_key_value: str,
    worker_id: str,
    error_message: str,
) -> dict[str, Any] | None:
    query = """
LET now = DATE_ISO8601(DATE_NOW())
FOR task IN @@tasks
  FILTER task._key == @task_key
  FILTER task.worker_id == @worker_id
  LIMIT 1
  UPDATE task WITH {
    status: "pending",
    worker_id: null,
    lease_expires_at: null,
    last_error: @error_message,
    last_requeued_at: now,
    updated_at: now
  } IN @@tasks
  OPTIONS { mergeObjects: true }
  RETURN NEW
""".strip()
    rows = aql(
        endpoint,
        database,
        username,
        password,
        query,
        {
            "@tasks": "hive_tasks",
            "task_key": task_key_value,
            "worker_id": worker_id,
            "error_message": error_message,
        },
    )
    return rows[0] if rows else None



def queue_stats(endpoint: str, database: str, username: str, password: str, *, queue_name: str) -> dict[str, Any]:
    query = """
FOR task IN @@tasks
  FILTER task.queue_name == @queue_name
  COLLECT status = task.status WITH COUNT INTO count
  RETURN {status, count}
""".strip()
    rows = aql(
        endpoint,
        database,
        username,
        password,
        query,
        {"@tasks": "hive_tasks", "queue_name": queue_name},
    )
    return {
        "schema": "info_geometry.hive_queue_stats.v1",
        "queue_name": queue_name,
        "rows": rows,
    }



def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default=DEFAULT_ENDPOINT)
    parser.add_argument("--database", default=DEFAULT_DATABASE)
    parser.add_argument("--username", default=DEFAULT_USERNAME)
    parser.add_argument("--password", default=DEFAULT_PASSWORD)
    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser("init", help="Create the Hive live database schema and indexes")
    sub.add_parser("status", help="Print live schema status and counts")

    heartbeat = sub.add_parser("heartbeat-worker", help="Register/update a worker bee heartbeat")
    heartbeat.add_argument("--worker-id", required=True)
    heartbeat.add_argument("--capability", action="append", default=[])
    heartbeat.add_argument("--queue", action="append", default=[])

    enqueue = sub.add_parser("enqueue-goal", help="Insert a manual goal and pending task")
    enqueue.add_argument("--queue-name", default=DEFAULT_QUEUE)
    enqueue.add_argument("--goal-hash-shape", required=True)
    enqueue.add_argument("--canonical-shape", required=True)
    enqueue.add_argument("--target-pretty", required=True)
    enqueue.add_argument("--module", required=True)
    enqueue.add_argument("--goal-index", type=int, required=True)
    enqueue.add_argument("--priority", type=float, default=0.5)

    seed = sub.add_parser("seed-jsonl", help="Seed goals/fossils/tasks from ingest_hive_json JSONL")
    seed.add_argument("--input", type=Path, required=True)
    seed.add_argument("--queue-name", default=DEFAULT_QUEUE)
    seed.add_argument("--priority", type=float, default=0.5)

    claim = sub.add_parser("claim-next", help="Atomically lease the next pending task")
    claim.add_argument("--worker-id", required=True)
    claim.add_argument("--queue-name", default=DEFAULT_QUEUE)
    claim.add_argument("--lease-seconds", type=int, default=DEFAULT_LEASE_SECONDS)

    complete = sub.add_parser("complete-task", help="Mark a leased task completed")
    complete.add_argument("--task-key", required=True)
    complete.add_argument("--worker-id", required=True)

    fail = sub.add_parser("fail-task", help="Mark a leased task failed")
    fail.add_argument("--task-key", required=True)
    fail.add_argument("--worker-id", required=True)
    fail.add_argument("--error", required=True)

    stats = sub.add_parser("queue-stats", help="Summarize queue status counts")
    stats.add_argument("--queue-name", default=DEFAULT_QUEUE)
    return parser.parse_args()



def main() -> int:
    args = parse_args()
    endpoint = str(args.endpoint).rstrip("/")
    database = str(args.database)
    username = str(args.username)
    password = str(args.password)

    if args.command == "init":
        result = init_schema(endpoint, database, username, password)
    elif args.command == "status":
        result = schema_status(endpoint, database, username, password)
    elif args.command == "heartbeat-worker":
        result = heartbeat_worker(
            endpoint,
            database,
            username,
            password,
            worker_id=str(args.worker_id),
            capabilities=list(args.capability),
            queues=list(args.queue),
        )
    elif args.command == "enqueue-goal":
        result = enqueue_goal(
            endpoint,
            database,
            username,
            password,
            queue_name=str(args.queue_name),
            goal_hash_shape=str(args.goal_hash_shape),
            canonical_shape=str(args.canonical_shape),
            target_pretty=str(args.target_pretty),
            module=str(args.module),
            goal_index=int(args.goal_index),
            priority=float(args.priority),
        )
    elif args.command == "seed-jsonl":
        payloads = seed_payloads(Path(args.input), queue_name=str(args.queue_name), priority=float(args.priority))
        for collection, rows in payloads.items():
            import_rows(endpoint, database, username, password, collection, rows)
        result = {
            "schema": "info_geometry.hive_seed_jsonl.v1",
            "input": str(Path(args.input).resolve()),
            "database": database,
            "queue_name": str(args.queue_name),
            "counts": {collection: len(rows) for collection, rows in payloads.items()},
        }
    elif args.command == "claim-next":
        result = claim_next_task(
            endpoint,
            database,
            username,
            password,
            worker_id=str(args.worker_id),
            queue_name=str(args.queue_name),
            lease_seconds=int(args.lease_seconds),
        )
    elif args.command == "complete-task":
        result = complete_task(
            endpoint,
            database,
            username,
            password,
            task_key_value=str(args.task_key),
            worker_id=str(args.worker_id),
        )
    elif args.command == "fail-task":
        result = fail_task(
            endpoint,
            database,
            username,
            password,
            task_key_value=str(args.task_key),
            worker_id=str(args.worker_id),
            error_message=str(args.error),
        )
    elif args.command == "queue-stats":
        result = queue_stats(endpoint, database, username, password, queue_name=str(args.queue_name))
    else:
        raise AssertionError(f"unhandled command: {args.command}")

    print(json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
