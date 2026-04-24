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
    CollectionSpec("hive_retrieval_packets"),
    CollectionSpec("hive_proof_state_packets"),
    CollectionSpec("hive_proposals"),
    CollectionSpec("hive_critiques"),
    CollectionSpec("hive_execution_intents"),
    CollectionSpec("hive_verifications"),
    CollectionSpec("hive_build_packets"),
    CollectionSpec("hive_audit_packets"),
    CollectionSpec("hive_candidate_packets"),
    CollectionSpec("hive_promotions"),
    CollectionSpec("hive_resources"),
    CollectionSpec("hive_resource_leases"),
    CollectionSpec("hive_tasks"),
    CollectionSpec("hive_workers"),
    CollectionSpec("hive_events"),
    CollectionSpec("hive_goal_closed_by", edge=True),
    CollectionSpec("hive_goal_rejected_by", edge=True),
    CollectionSpec("hive_task_for_goal", edge=True),
    CollectionSpec("hive_event_about", edge=True),
    CollectionSpec("hive_task_emits_packet", edge=True),
    CollectionSpec("hive_task_consumes_packet", edge=True),
    CollectionSpec("hive_packet_depends_on", edge=True),
)

INDEXES: tuple[IndexSpec, ...] = (
    IndexSpec("hive_goals", ("goal_hash_shape",), name="goal_hash_shape_idx"),
    IndexSpec("hive_goals", ("queue_name", "status"), name="goal_queue_status_idx"),
    IndexSpec("hive_fossils", ("conclusion_hash_shape",), name="fossil_conclusion_shape_idx"),
    IndexSpec("hive_fossils", ("const_name",), name="fossil_const_name_idx"),
    IndexSpec("hive_deadends", ("goal_hash_shape", "const_name"), name="deadend_goal_const_idx"),
    IndexSpec("hive_replay_packets", ("fossil_key",), name="replay_fossil_key_idx"),
    IndexSpec("hive_replay_packets", ("goal_key", "task_key"), name="replay_goal_task_idx"),
    IndexSpec("hive_retrieval_packets", ("goal_key",), name="retrieval_goal_key_idx"),
    IndexSpec("hive_retrieval_packets", ("authority", "representation_class"), name="retrieval_authority_repr_idx"),
    IndexSpec("hive_proof_state_packets", ("goal_key",), name="proof_state_goal_key_idx"),
    IndexSpec("hive_proposals", ("goal_key",), name="proposal_goal_key_idx"),
    IndexSpec("hive_critiques", ("proposal_key",), name="critique_proposal_key_idx"),
    IndexSpec("hive_execution_intents", ("proposal_key", "critique_key"), name="exec_intent_lineage_idx"),
    IndexSpec("hive_verifications", ("execution_intent_key",), name="verification_exec_intent_idx"),
    IndexSpec("hive_build_packets", ("verification_key", "state"), name="build_verification_state_idx"),
    IndexSpec("hive_audit_packets", ("build_key",), name="audit_build_key_idx"),
    IndexSpec("hive_candidate_packets", ("formal_target",), name="candidate_formal_target_idx"),
    IndexSpec("hive_promotions", ("audit_key",), name="promotion_audit_key_idx"),
    IndexSpec("hive_resources", ("resource_class", "status"), name="resource_class_status_idx"),
    IndexSpec("hive_resource_leases", ("resource_class", "state"), name="resource_lease_state_idx"),
    IndexSpec("hive_tasks", ("queue_name", "status", "priority"), name="task_queue_status_priority_idx"),
    IndexSpec("hive_tasks", ("task_kind",), name="task_kind_idx"),
    IndexSpec("hive_tasks", ("lease_expires_at",), name="task_lease_expiry_idx"),
    IndexSpec("hive_tasks", ("goal_key",), name="task_goal_key_idx"),
    IndexSpec("hive_workers", ("worker_id",), unique=True, sparse=False, name="worker_id_idx"),
    IndexSpec("hive_events", ("packet_sha256",), unique=True, sparse=False, name="event_packet_sha_idx"),
    IndexSpec("hive_events", ("artifact_kind", "space"), name="event_kind_space_idx"),
)

ALLOWED_AUTHORITIES = {
    "navigation",
    "semantic",
    "proposal",
    "execution_intent",
    "lean_checked",
    "build_checked",
    "audit_checked",
    "promoted",
}

ALLOWED_REPRESENTATION_CLASSES = {
    "owner",
    "translator",
    "coherence",
    "capstone",
    "shadow",
}

ALLOWED_REPRESENTATION_DEPTHS = {
    "scalar",
    "finite_matrix",
    "projective",
    "hilbert",
    "operatorial",
    "krein",
    "von_neumann",
    "type_iii",
    "categorical",
}

ALLOWED_SOURCE_REGIMES = {
    "symbolic",
    "research",
    "theorem_lane",
    "synthetic_smoke",
    "infrastructure",
    "unknown",
}

ALLOWED_VERIFICATION_ORIGINS = {
    "lean_produced",
    "synthetic_smoke",
    "replay_lane",
    "unknown",
}

ALLOWED_BUILD_ORIGINS = {
    "locked_lake_build",
    "synthetic_smoke",
    "unknown",
}

ALLOWED_AUDIT_ORIGINS = {
    "auditbee",
    "manual",
    "synthetic_smoke",
    "unknown",
}

ALLOWED_PROMOTION_ORIGINS = {
    "promotionbee",
    "manual",
    "unknown",
}

ALLOWED_BACKEND_KINDS = {
    "provider_api",
    "codex_cli",
    "copilot_cli",
    "gemini_cli",
    "local_openai_compatible",
    "manual_override",
    "unknown",
}

ALLOWED_BACKEND_CAPABILITIES = {
    "strict_code_review",
    "code_transform",
    "symbolic_interpolation",
    "research_digest",
    "proof_tactic_proposal",
    "unknown",
}

ALLOWED_HERMES_ROLES = {
    "hermes_hive",
    "hermes_codex",
    "hermes_gemini",
    "hermes_copilot",
    "hermes_local_prover",
    "hermes_local_auditor",
    "hive_proof_bee",
    "manual_operator",
    "unknown",
}

ALLOWED_PROVIDER_CONTACT_POLICIES = {
    "codex_cli_only_for_provider_contact",
    "direct_provider_api_explicit_override",
    "local_endpoint_only",
    "unknown",
}

PACKET_COLLECTION_BY_SCHEMA = {
    "hive.packet.retrieval.v1": "hive_retrieval_packets",
    "hive.packet.proof_state.v1": "hive_proof_state_packets",
    "hive.packet.proposal.v1": "hive_proposals",
    "hive.packet.critique.v1": "hive_critiques",
    "hive.packet.execution_intent.v1": "hive_execution_intents",
    "hive.packet.verification.v1": "hive_verifications",
    "hive.packet.build.v1": "hive_build_packets",
    "hive.packet.audit.v1": "hive_audit_packets",
    "hive.packet.theorem_candidate.v1": "hive_candidate_packets",
    "hive.packet.promotion_decision.v1": "hive_promotions",
    "info_geometry.hive_replay_packet.v1": "hive_replay_packets",
}


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
        "task_kind": "proof.search",
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


def packet_key(packet: dict[str, Any]) -> str:
    schema = str(packet.get("schema") or "unknown")
    goal_key_value = str(packet.get("goal_key") or packet.get("formal_target") or packet.get("audit_key") or "")
    digest = hashlib.sha256(json.dumps(packet, sort_keys=True, ensure_ascii=False).encode("utf-8")).hexdigest()[:24]
    return stable_key("packet", schema, goal_key_value, digest)


def packet_collection_for_schema(schema: str) -> str:
    collection = PACKET_COLLECTION_BY_SCHEMA.get(schema)
    if not collection:
        raise ValueError(f"unsupported packet schema: {schema}")
    return collection


def authority_rank(authority: str) -> int:
    ranks = {
        "navigation": 0,
        "semantic": 1,
        "proposal": 2,
        "execution_intent": 3,
        "lean_checked": 4,
        "build_checked": 5,
        "audit_checked": 6,
        "promoted": 7,
    }
    return ranks[authority]


def normalize_packet_origin_metadata(packet: dict[str, Any]) -> None:
    schema = str(packet.get("schema") or "")
    if schema in {
        "hive.packet.retrieval.v1",
        "hive.packet.proof_state.v1",
        "hive.packet.proposal.v1",
        "hive.packet.critique.v1",
        "hive.packet.execution_intent.v1",
        "hive.packet.verification.v1",
        "hive.packet.build.v1",
        "hive.packet.audit.v1",
        "hive.packet.promotion_decision.v1",
        "info_geometry.hive_replay_packet.v1",
    }:
        packet.setdefault("source_regime", "theorem_lane")
    elif schema == "hive.packet.theorem_candidate.v1":
        packet.setdefault("source_regime", "symbolic" if packet.get("symbolic_origin") else "unknown")

    if schema == "hive.packet.verification.v1":
        packet.setdefault("verification_origin", "lean_produced")
    elif schema == "hive.packet.build.v1":
        packet.setdefault("build_origin", "locked_lake_build")
    elif schema == "hive.packet.audit.v1":
        packet.setdefault("audit_origin", "auditbee")
        if packet.get("verification_origin") == "synthetic_smoke":
            packet["source_regime"] = "synthetic_smoke"
    elif schema == "hive.packet.promotion_decision.v1":
        packet.setdefault("promotion_origin", "promotionbee")
        if packet.get("verification_origin") == "synthetic_smoke":
            packet["source_regime"] = "synthetic_smoke"
    elif schema == "info_geometry.hive_replay_packet.v1":
        packet.setdefault("verification_origin", "replay_lane")


def validate_origin_metadata(packet: dict[str, Any]) -> None:
    schema = str(packet.get("schema") or "")
    source_regime = str(packet.get("source_regime") or "")
    if source_regime and source_regime not in ALLOWED_SOURCE_REGIMES:
        raise ValueError(f"packet {schema} has invalid source_regime: {source_regime!r}")

    verification_origin = packet.get("verification_origin")
    if verification_origin is not None and str(verification_origin) not in ALLOWED_VERIFICATION_ORIGINS:
        raise ValueError(f"packet {schema} has invalid verification_origin: {verification_origin!r}")

    build_origin = packet.get("build_origin")
    if build_origin is not None and str(build_origin) not in ALLOWED_BUILD_ORIGINS:
        raise ValueError(f"packet {schema} has invalid build_origin: {build_origin!r}")

    audit_origin = packet.get("audit_origin")
    if audit_origin is not None and str(audit_origin) not in ALLOWED_AUDIT_ORIGINS:
        raise ValueError(f"packet {schema} has invalid audit_origin: {audit_origin!r}")

    promotion_origin = packet.get("promotion_origin")
    if promotion_origin is not None and str(promotion_origin) not in ALLOWED_PROMOTION_ORIGINS:
        raise ValueError(f"packet {schema} has invalid promotion_origin: {promotion_origin!r}")


def validate_backend_metadata(packet: dict[str, Any]) -> None:
    schema = str(packet.get("schema") or "")
    backend_kind = packet.get("backend_kind")
    if backend_kind is not None and str(backend_kind) not in ALLOWED_BACKEND_KINDS:
        raise ValueError(f"packet {schema} has invalid backend_kind: {backend_kind!r}")

    backend_capability = packet.get("backend_capability")
    if backend_capability is not None and str(backend_capability) not in ALLOWED_BACKEND_CAPABILITIES:
        raise ValueError(f"packet {schema} has invalid backend_capability: {backend_capability!r}")

    hermes_role = packet.get("hermes_role")
    if hermes_role is not None and str(hermes_role) not in ALLOWED_HERMES_ROLES:
        raise ValueError(f"packet {schema} has invalid hermes_role: {hermes_role!r}")

    if backend_kind is not None and schema in {
        "hive.packet.verification.v1",
        "hive.packet.build.v1",
        "hive.packet.audit.v1",
        "hive.packet.promotion_decision.v1",
    }:
        raise ValueError(f"authority packet {schema} cannot carry cognition backend_kind")

    provider_contact_policy = packet.get("provider_contact_policy")
    if (
        provider_contact_policy is not None
        and str(provider_contact_policy) not in ALLOWED_PROVIDER_CONTACT_POLICIES
    ):
        raise ValueError(f"packet {schema} has invalid provider_contact_policy: {provider_contact_policy!r}")


def validate_packet_invariants(packet: dict[str, Any]) -> dict[str, Any]:
    if not isinstance(packet, dict):
        raise ValueError("packet must be a JSON object")
    schema = str(packet.get("schema") or "")
    if not schema:
        raise ValueError("packet missing schema")
    packet_collection_for_schema(schema)

    authority = str(packet.get("authority") or "")
    if authority not in ALLOWED_AUTHORITIES:
        raise ValueError(f"packet {schema} has invalid authority: {authority!r}")

    rep_class = packet.get("representation_class")
    if rep_class is not None and str(rep_class) not in ALLOWED_REPRESENTATION_CLASSES:
        raise ValueError(f"packet {schema} has invalid representation_class: {rep_class!r}")

    rep_depth = packet.get("representation_depth")
    if rep_depth is not None and str(rep_depth) not in ALLOWED_REPRESENTATION_DEPTHS:
        raise ValueError(f"packet {schema} has invalid representation_depth: {rep_depth!r}")

    if schema == "hive.packet.retrieval.v1":
        if authority != "navigation":
            raise ValueError("RetrievalPacket must have authority 'navigation'")
        if not packet.get("goal_key"):
            raise ValueError("RetrievalPacket requires goal_key")
    elif schema == "hive.packet.proof_state.v1":
        if authority != "navigation":
            raise ValueError("ProofStatePacket must have authority 'navigation'")
        for field in ("goal_key", "goal_text", "proof_state"):
            if not packet.get(field):
                raise ValueError(f"ProofStatePacket requires {field}")
    elif schema == "hive.packet.proposal.v1":
        if authority != "proposal":
            raise ValueError("ProposalPacket must have authority 'proposal'")
        for field in ("goal_key", "proof_state_key", "retrieval_key", "proposal_kind", "content"):
            if not packet.get(field):
                raise ValueError(f"ProposalPacket requires {field}")
    elif schema == "hive.packet.critique.v1":
        if authority != "proposal":
            raise ValueError("CritiquePacket must have authority 'proposal'")
        if not packet.get("proposal_key"):
            raise ValueError("CritiquePacket requires proposal_key")
        verdict = str(packet.get("verdict") or "")
        if verdict not in {"approve", "revise", "reject"}:
            raise ValueError(f"CritiquePacket has invalid verdict: {verdict!r}")
    elif schema == "hive.packet.execution_intent.v1":
        if authority != "execution_intent":
            raise ValueError("ExecutionIntentPacket must have authority 'execution_intent'")
        for field in ("proposal_key", "critique_key", "intent_kind", "frozen_payload"):
            if packet.get(field) in (None, ""):
                raise ValueError(f"ExecutionIntentPacket requires {field}")
    elif schema == "hive.packet.verification.v1":
        if authority != "lean_checked":
            raise ValueError("VerificationPacket must have authority 'lean_checked'")
        if not packet.get("execution_intent_key"):
            raise ValueError("VerificationPacket requires execution_intent_key")
        status = str(packet.get("status") or "")
        if status not in {"success", "failure", "environment_blocked"}:
            raise ValueError(f"VerificationPacket has invalid status: {status!r}")
    elif schema == "hive.packet.build.v1":
        if authority != "build_checked":
            raise ValueError("BuildPacket must have authority 'build_checked'")
        if not packet.get("verification_key"):
            raise ValueError("BuildPacket requires verification_key")
        state = str(packet.get("state") or "")
        if state not in {"lock_wait", "running", "passed", "failed", "environment_blocked"}:
            raise ValueError(f"BuildPacket has invalid state: {state!r}")
        if not packet.get("target"):
            raise ValueError("BuildPacket requires target")
    elif schema == "hive.packet.audit.v1":
        if authority != "audit_checked":
            raise ValueError("AuditPacket must have authority 'audit_checked'")
        if not packet.get("build_key"):
            raise ValueError("AuditPacket requires build_key")
        verdict = str(packet.get("verdict") or "")
        if verdict not in {"pass", "conditional_pass", "fail"}:
            raise ValueError(f"AuditPacket has invalid verdict: {verdict!r}")
    elif schema == "hive.packet.theorem_candidate.v1":
        if authority != "semantic":
            raise ValueError("TheoremCandidatePacket must have authority 'semantic'")
        if not packet.get("formal_target"):
            raise ValueError("TheoremCandidatePacket requires formal_target")
        if packet.get("asserts_theorem_closure"):
            raise ValueError("TheoremCandidatePacket cannot assert theorem closure")
    elif schema == "hive.packet.promotion_decision.v1":
        if authority != "promoted":
            raise ValueError("PromotionDecisionPacket must have authority 'promoted'")
        if not packet.get("audit_key"):
            raise ValueError("PromotionDecisionPacket requires audit_key")
        decision = str(packet.get("decision") or "")
        if decision not in {"promote", "hold", "reject"}:
            raise ValueError(f"PromotionDecisionPacket has invalid decision: {decision!r}")
    elif schema == "info_geometry.hive_replay_packet.v1":
        if authority_rank(authority) < authority_rank("lean_checked"):
            raise ValueError("Replay packets must have authority at least 'lean_checked'")

    if packet.get("asserts_theorem_closure") and authority_rank(authority) < authority_rank("lean_checked"):
        raise ValueError("Only lean_checked-or-higher packets may assert theorem closure")

    if str(packet.get("representation_class") or "") == "shadow" and packet.get("discharges_owner_debt"):
        raise ValueError("Shadow packets cannot discharge owner debts without an explicit bridge path")

    packet_copy = dict(packet)
    normalize_packet_origin_metadata(packet_copy)
    validate_origin_metadata(packet_copy)
    validate_backend_metadata(packet_copy)
    packet_copy.setdefault("packet_key", packet_key(packet_copy))
    packet_copy.setdefault("created_at", iso_now())
    return packet_copy


def import_packet(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    packet: dict[str, Any],
) -> dict[str, Any]:
    validated = validate_packet_invariants(packet)
    collection = packet_collection_for_schema(str(validated["schema"]))
    row = dict(validated)
    row["_key"] = str(validated["packet_key"])
    import_rows(endpoint, database, username, password, collection, [row])
    return {"collection": collection, "packet": row}


def fetch_packet_by_key(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    schema: str,
    packet_key_value: str,
) -> dict[str, Any] | None:
    collection = packet_collection_for_schema(schema)
    rows = aql(
        endpoint,
        database,
        username,
        password,
        "FOR packet IN @@collection FILTER packet._key == @packet_key LIMIT 1 RETURN packet",
        {"@collection": collection, "packet_key": packet_key_value},
    )
    return rows[0] if rows else None


def validate_packet_database_invariants(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    packet: dict[str, Any],
) -> None:
    schema = str(packet.get("schema") or "")
    if schema == "hive.packet.build.v1":
        verification_key = str(packet.get("verification_key") or "")
        verification = fetch_packet_by_key(
            endpoint,
            database,
            username,
            password,
            schema="hive.packet.verification.v1",
            packet_key_value=verification_key,
        )
        if not verification:
            raise ValueError(f"BuildPacket references missing VerificationPacket: {verification_key}")
        if verification.get("authority") != "lean_checked":
            raise ValueError("BuildPacket requires referenced VerificationPacket authority 'lean_checked'")
    elif schema == "hive.packet.audit.v1":
        build_key = str(packet.get("build_key") or "")
        build = fetch_packet_by_key(
            endpoint,
            database,
            username,
            password,
            schema="hive.packet.build.v1",
            packet_key_value=build_key,
        )
        if not build:
            raise ValueError(f"AuditPacket references missing BuildPacket: {build_key}")
        if build.get("authority") != "build_checked":
            raise ValueError("AuditPacket requires referenced BuildPacket authority 'build_checked'")
    elif schema == "hive.packet.promotion_decision.v1":
        audit_key = str(packet.get("audit_key") or "")
        audit = fetch_packet_by_key(
            endpoint,
            database,
            username,
            password,
            schema="hive.packet.audit.v1",
            packet_key_value=audit_key,
        )
        if not audit:
            raise ValueError(f"PromotionDecisionPacket references missing AuditPacket: {audit_key}")
        if audit.get("authority") != "audit_checked":
            raise ValueError("PromotionDecisionPacket requires referenced AuditPacket authority 'audit_checked'")
        if packet.get("decision") == "promote":
            if audit.get("verdict") != "pass":
                raise ValueError("PromotionDecisionPacket cannot promote unless AuditPacket verdict is 'pass'")
            if not audit.get("promotion_allowed"):
                raise ValueError("PromotionDecisionPacket cannot promote unless AuditPacket promotion_allowed is true")


def packet_doc_key(packet: dict[str, Any]) -> str:
    key = packet.get("packet_key") or packet.get("_key")
    if not key:
        raise ValueError("packet row is missing packet_key/_key")
    return str(key)


def packet_doc_ref(packet: dict[str, Any]) -> str:
    collection = packet_collection_for_schema(str(packet.get("schema") or ""))
    return f"{collection}/{packet_doc_key(packet)}"


def build_task_emits_packet_edge(task_key_value: str, packet: dict[str, Any]) -> dict[str, Any]:
    packet_key_value = packet_doc_key(packet)
    return {
        "_key": stable_key("taskemitspacket", task_key_value, packet_key_value),
        "_from": f"hive_tasks/{task_key_value}",
        "_to": packet_doc_ref(packet),
        "schema": "info_geometry.hive_task_emits_packet.v1",
        "role": "emits",
        "packet_schema": packet.get("schema"),
        "created_at": iso_now(),
    }


def build_packet_depends_on_edge(
    packet: dict[str, Any],
    dependency: dict[str, Any],
    *,
    role: str = "depends_on",
) -> dict[str, Any]:
    packet_key_value = packet_doc_key(packet)
    dependency_key_value = packet_doc_key(dependency)
    return {
        "_key": stable_key("packetdependson", packet_key_value, dependency_key_value, role),
        "_from": packet_doc_ref(packet),
        "_to": packet_doc_ref(dependency),
        "schema": "info_geometry.hive_packet_depends_on.v1",
        "role": role,
        "packet_schema": packet.get("schema"),
        "dependency_schema": dependency.get("schema"),
        "created_at": iso_now(),
    }


def record_packet_lineage(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    task_key_value: str | None = None,
    emitted_packet: dict[str, Any] | None = None,
    dependencies: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    task_edges: list[dict[str, Any]] = []
    dependency_edges: list[dict[str, Any]] = []
    if emitted_packet is not None and task_key_value:
        task_edges.append(build_task_emits_packet_edge(task_key_value, emitted_packet))
    if emitted_packet is not None:
        for dependency in dependencies or []:
            dependency_edges.append(build_packet_depends_on_edge(emitted_packet, dependency))
    import_rows(endpoint, database, username, password, "hive_task_emits_packet", task_edges)
    import_rows(endpoint, database, username, password, "hive_packet_depends_on", dependency_edges)
    return {
        "task_emits_packet_edges": task_edges,
        "packet_depends_on_edges": dependency_edges,
    }


def import_packet_with_lineage(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    packet: dict[str, Any],
    task_key_value: str | None = None,
    dependencies: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    validated = validate_packet_invariants(packet)
    validate_packet_database_invariants(
        endpoint,
        database,
        username,
        password,
        packet=validated,
    )
    result = import_packet(endpoint, database, username, password, packet=validated)
    lineage = record_packet_lineage(
        endpoint,
        database,
        username,
        password,
        task_key_value=task_key_value,
        emitted_packet=result["packet"],
        dependencies=dependencies,
    )
    return {**result, "lineage": lineage}



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
    task_kind: str = "proof.search",
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
    task_doc["task_kind"] = str(task_kind)
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
    task_kind: str | None = None,
) -> dict[str, Any] | None:
    query = """
LET now = DATE_ISO8601(DATE_NOW())
FOR task IN @@tasks
  FILTER task.queue_name == @queue_name
  FILTER @task_kind == null || task.task_kind == @task_kind
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
            "task_kind": task_kind,
        },
    )
    return rows[0] if rows else None


def enqueue_build_verify_task(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    queue_name: str,
    verification_key: str,
    target: str,
    priority: float = 0.5,
    wfail: bool = False,
) -> dict[str, Any]:
    now = iso_now()
    task_doc = {
        "_key": stable_key("task", "build.verify", verification_key, target),
        "schema": "info_geometry.hive_task.v1",
        "task_kind": "build.verify",
        "queue_name": queue_name,
        "goal_key": None,
        "verification_key": verification_key,
        "target": target,
        "wfail": bool(wfail),
        "status": "pending",
        "priority": float(priority),
        "claim_count": 0,
        "worker_id": None,
        "lease_expires_at": None,
        "created_at": now,
        "updated_at": now,
    }
    import_rows(endpoint, database, username, password, "hive_tasks", [task_doc])
    return {"task": task_doc}


def enqueue_audit_task(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    queue_name: str,
    build_key: str,
    priority: float = 0.5,
) -> dict[str, Any]:
    now = iso_now()
    task_doc = {
        "_key": stable_key("task", "audit.semantic", build_key),
        "schema": "info_geometry.hive_task.v1",
        "task_kind": "audit.semantic",
        "queue_name": queue_name,
        "goal_key": None,
        "build_key": build_key,
        "status": "pending",
        "priority": float(priority),
        "claim_count": 0,
        "worker_id": None,
        "lease_expires_at": None,
        "created_at": now,
        "updated_at": now,
    }
    import_rows(endpoint, database, username, password, "hive_tasks", [task_doc])
    return {"task": task_doc}


def enqueue_promotion_task(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    queue_name: str,
    audit_key: str,
    priority: float = 0.5,
    allow_override: bool = False,
) -> dict[str, Any]:
    now = iso_now()
    task_doc = {
        "_key": stable_key("task", "promotion.decide", audit_key),
        "schema": "info_geometry.hive_task.v1",
        "task_kind": "promotion.decide",
        "queue_name": queue_name,
        "goal_key": None,
        "audit_key": audit_key,
        "allow_override": bool(allow_override),
        "status": "pending",
        "priority": float(priority),
        "claim_count": 0,
        "worker_id": None,
        "lease_expires_at": None,
        "created_at": now,
        "updated_at": now,
    }
    import_rows(endpoint, database, username, password, "hive_tasks", [task_doc])
    return {"task": task_doc}



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



def update_task_status(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    task_key_value: str,
    worker_id: str | None,
    status: str,
    extra_fields: dict[str, Any] | None = None,
) -> dict[str, Any] | None:
    query = """
LET now = DATE_ISO8601(DATE_NOW())
FOR task IN @@tasks
  FILTER task._key == @task_key
  FILTER @worker_id == null || task.worker_id == @worker_id
  LIMIT 1
  UPDATE task WITH MERGE({ status: @status, updated_at: now }, @extra) IN @@tasks
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
            "status": status,
            "extra": extra_fields or {},
        },
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


def find_packet_by_key_any_schema(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    packet_key_value: str,
) -> dict[str, Any] | None:
    for schema, collection in PACKET_COLLECTION_BY_SCHEMA.items():
        rows = aql(
            endpoint,
            database,
            username,
            password,
            "FOR packet IN @@collection FILTER packet._key == @packet_key LIMIT 1 RETURN packet",
            {"@collection": collection, "packet_key": packet_key_value},
        )
        if rows:
            return {"schema": schema, "collection": collection, "packet": rows[0]}
    return None


def show_packet(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    packet_key_value: str,
    schema: str | None = None,
) -> dict[str, Any]:
    if schema:
        packet = fetch_packet_by_key(
            endpoint,
            database,
            username,
            password,
            schema=schema,
            packet_key_value=packet_key_value,
        )
        return {
            "schema": "info_geometry.hive_packet_show.v1",
            "packet_key": packet_key_value,
            "packet_schema": schema,
            "collection": packet_collection_for_schema(schema),
            "packet": packet,
        }
    found = find_packet_by_key_any_schema(
        endpoint,
        database,
        username,
        password,
        packet_key_value=packet_key_value,
    )
    return {
        "schema": "info_geometry.hive_packet_show.v1",
        "packet_key": packet_key_value,
        "found": found is not None,
        **(found or {}),
    }


def lineage_upstream(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    packet_key_value: str,
    schema: str | None = None,
    depth: int = 4,
) -> dict[str, Any]:
    packet = show_packet(endpoint, database, username, password, packet_key_value=packet_key_value, schema=schema)
    collection = packet.get("collection")
    if not collection:
        return {"schema": "info_geometry.hive_lineage_upstream.v1", "packet_key": packet_key_value, "found": False}
    start = f"{collection}/{packet_key_value}"
    query = """
FOR v, e, p IN 1..@depth OUTBOUND @start hive_packet_depends_on
  RETURN {
    depth: LENGTH(p.edges),
    vertex: v,
    edge: e,
    path_vertices: p.vertices[*]._id,
    path_edges: p.edges[*]._id
  }
""".strip()
    rows = aql(
        endpoint,
        database,
        username,
        password,
        query,
        {"start": start, "depth": int(depth)},
    )
    return {
        "schema": "info_geometry.hive_lineage_upstream.v1",
        "packet_key": packet_key_value,
        "start": start,
        "depth": int(depth),
        "rows": rows,
    }


def lineage_downstream_task(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    task_key_value: str,
    depth: int = 4,
) -> dict[str, Any]:
    start = f"hive_tasks/{task_key_value}"
    emissions = aql(
        endpoint,
        database,
        username,
        password,
        """
FOR packet, edge IN OUTBOUND @start hive_task_emits_packet
  RETURN {packet, edge}
""".strip(),
        {"start": start},
    )
    paths = aql(
        endpoint,
        database,
        username,
        password,
        """
FOR v, e, p IN 1..@depth OUTBOUND @start hive_task_emits_packet, hive_packet_depends_on
  RETURN {
    depth: LENGTH(p.edges),
    vertex: v,
    edge: e,
    path_vertices: p.vertices[*]._id,
    path_edges: p.edges[*]._id
  }
""".strip(),
        {"start": start, "depth": int(depth)},
    )
    return {
        "schema": "info_geometry.hive_lineage_downstream_task.v1",
        "task_key": task_key_value,
        "start": start,
        "depth": int(depth),
        "emissions": emissions,
        "paths": paths,
    }


def trace_packet_metadata(packet: dict[str, Any], *, depth: int = 0) -> dict[str, Any]:
    return {
        "depth": int(depth),
        "packet_key": packet.get("packet_key") or packet.get("_key"),
        "schema": packet.get("schema"),
        "authority": packet.get("authority"),
        "representation_class": packet.get("representation_class"),
        "representation_depth": packet.get("representation_depth"),
        "source_regime": packet.get("source_regime"),
        "verification_origin": packet.get("verification_origin"),
        "build_origin": packet.get("build_origin"),
        "audit_origin": packet.get("audit_origin"),
        "promotion_origin": packet.get("promotion_origin"),
        "backend_kind": packet.get("backend_kind"),
        "backend_identity": packet.get("backend_identity"),
        "backend_capability": packet.get("backend_capability"),
        "hermes_role": packet.get("hermes_role"),
        "provider_contact_policy": packet.get("provider_contact_policy"),
        "status": packet.get("status"),
        "state": packet.get("state"),
        "verdict": packet.get("verdict"),
        "decision": packet.get("decision"),
    }


def backend_trace(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    *,
    packet_key_value: str,
    schema: str | None = None,
    depth: int = 6,
) -> dict[str, Any]:
    start = show_packet(endpoint, database, username, password, packet_key_value=packet_key_value, schema=schema)
    trace: list[dict[str, Any]] = []
    if start.get("found"):
        trace.append(trace_packet_metadata(start.get("packet") or {}, depth=0))
    upstream = lineage_upstream(
        endpoint,
        database,
        username,
        password,
        packet_key_value=packet_key_value,
        schema=schema,
        depth=depth,
    )
    for row in upstream.get("rows") or []:
        trace.append(trace_packet_metadata(row.get("vertex") or {}, depth=int(row.get("depth") or 0)))
    return {
        "schema": "info_geometry.hive_backend_trace.v1",
        "packet_key": packet_key_value,
        "found": bool(start.get("found")),
        "depth": int(depth),
        "trace": trace,
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
    enqueue.add_argument("--task-kind", default="proof.search")

    seed = sub.add_parser("seed-jsonl", help="Seed goals/fossils/tasks from ingest_hive_json JSONL")
    seed.add_argument("--input", type=Path, required=True)
    seed.add_argument("--queue-name", default=DEFAULT_QUEUE)
    seed.add_argument("--priority", type=float, default=0.5)

    claim = sub.add_parser("claim-next", help="Atomically lease the next pending task")
    claim.add_argument("--worker-id", required=True)
    claim.add_argument("--queue-name", default=DEFAULT_QUEUE)
    claim.add_argument("--lease-seconds", type=int, default=DEFAULT_LEASE_SECONDS)
    claim.add_argument("--task-kind", default=None)

    build_task = sub.add_parser("enqueue-build-verify", help="Insert a build.verify task for BuildBee")
    build_task.add_argument("--queue-name", default="build-verify")
    build_task.add_argument("--verification-key", required=True)
    build_task.add_argument("--target", required=True)
    build_task.add_argument("--priority", type=float, default=0.5)
    build_task.add_argument("--wfail", action="store_true")
    audit_task = sub.add_parser("enqueue-audit", help="Insert an audit.semantic task for AuditBee")
    audit_task.add_argument("--queue-name", default="audit-semantic")
    audit_task.add_argument("--build-key", required=True)
    audit_task.add_argument("--priority", type=float, default=0.5)
    promotion_task = sub.add_parser("enqueue-promotion", help="Insert a promotion.decide task for PromotionBee")
    promotion_task.add_argument("--queue-name", default="promotion-decide")
    promotion_task.add_argument("--audit-key", required=True)
    promotion_task.add_argument("--priority", type=float, default=0.5)
    promotion_task.add_argument("--allow-override", action="store_true")

    complete = sub.add_parser("complete-task", help="Mark a leased task completed")
    complete.add_argument("--task-key", required=True)
    complete.add_argument("--worker-id", required=True)

    fail = sub.add_parser("fail-task", help="Mark a leased task failed")
    fail.add_argument("--task-key", required=True)
    fail.add_argument("--worker-id", required=True)
    fail.add_argument("--error", required=True)

    stats = sub.add_parser("queue-stats", help="Summarize queue status counts")
    stats.add_argument("--queue-name", default=DEFAULT_QUEUE)

    packet = sub.add_parser("import-packet", help="Validate and import a typed Hive packet")
    packet.add_argument("--input", type=Path, required=True)
    validate = sub.add_parser("validate-packet", help="Validate a typed Hive packet without importing it")
    validate.add_argument("--input", type=Path, required=True)
    show = sub.add_parser("show-packet", help="Show a packet by packet key")
    show.add_argument("--packet-key", required=True)
    show.add_argument("--schema", default=None)
    upstream = sub.add_parser("lineage-upstream", help="Show upstream packet dependencies")
    upstream.add_argument("--packet-key", required=True)
    upstream.add_argument("--schema", default=None)
    upstream.add_argument("--depth", type=int, default=4)
    backend_trace_parser = sub.add_parser("backend-trace", help="Summarize authority/backend metadata upstream of a packet")
    backend_trace_parser.add_argument("--packet-key", required=True)
    backend_trace_parser.add_argument("--schema", default=None)
    backend_trace_parser.add_argument("--depth", type=int, default=6)
    downstream_task = sub.add_parser("lineage-downstream-task", help="Show packets emitted by a task and downstream paths")
    downstream_task.add_argument("--task-key", required=True)
    downstream_task.add_argument("--depth", type=int, default=4)
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
            task_kind=str(args.task_kind),
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
            task_kind=str(args.task_kind) if args.task_kind else None,
        )
    elif args.command == "enqueue-build-verify":
        result = enqueue_build_verify_task(
            endpoint,
            database,
            username,
            password,
            queue_name=str(args.queue_name),
            verification_key=str(args.verification_key),
            target=str(args.target),
            priority=float(args.priority),
            wfail=bool(args.wfail),
        )
    elif args.command == "enqueue-audit":
        result = enqueue_audit_task(
            endpoint,
            database,
            username,
            password,
            queue_name=str(args.queue_name),
            build_key=str(args.build_key),
            priority=float(args.priority),
        )
    elif args.command == "enqueue-promotion":
        result = enqueue_promotion_task(
            endpoint,
            database,
            username,
            password,
            queue_name=str(args.queue_name),
            audit_key=str(args.audit_key),
            priority=float(args.priority),
            allow_override=bool(args.allow_override),
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
    elif args.command == "validate-packet":
        packet_payload = json.loads(Path(args.input).read_text(encoding="utf-8"))
        result = validate_packet_invariants(packet_payload)
    elif args.command == "import-packet":
        packet_payload = json.loads(Path(args.input).read_text(encoding="utf-8"))
        result = import_packet(endpoint, database, username, password, packet=packet_payload)
    elif args.command == "show-packet":
        result = show_packet(
            endpoint,
            database,
            username,
            password,
            packet_key_value=str(args.packet_key),
            schema=str(args.schema) if args.schema else None,
        )
    elif args.command == "lineage-upstream":
        result = lineage_upstream(
            endpoint,
            database,
            username,
            password,
            packet_key_value=str(args.packet_key),
            schema=str(args.schema) if args.schema else None,
            depth=int(args.depth),
        )
    elif args.command == "backend-trace":
        result = backend_trace(
            endpoint,
            database,
            username,
            password,
            packet_key_value=str(args.packet_key),
            schema=str(args.schema) if args.schema else None,
            depth=int(args.depth),
        )
    elif args.command == "lineage-downstream-task":
        result = lineage_downstream_task(
            endpoint,
            database,
            username,
            password,
            task_key_value=str(args.task_key),
            depth=int(args.depth),
        )
    else:
        raise AssertionError(f"unhandled command: {args.command}")

    print(json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
