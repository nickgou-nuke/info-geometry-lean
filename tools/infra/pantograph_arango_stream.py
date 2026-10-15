#!/usr/bin/env python3
"""Record a Pantograph JSONL REPL session in append-only Arango collections.

The proxy preserves Pantograph's stdin/stdout protocol. It stores the exact
request before forwarding it, then stores the corresponding response and any
session-scoped state transitions. Lean state IDs are aliases for replay only;
they are not portable proof-state identities.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.infra.arango_env import (  # noqa: E402
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.infra.arango_raw_infotree_ingest import (  # noqa: E402
    ArangoTarget,
    db_url,
    request_json,
)
from tools.infra.pantograph_environment import build_environment_manifest  # noqa: E402


COLLECTIONS = {
    "sessions": ("pantograph_sessions", False),
    "source_snapshots": ("pantograph_source_snapshots", False),
    "session_events": ("pantograph_session_events", False),
    "requests": ("pantograph_requests", False),
    "responses": ("pantograph_responses", False),
    "states": ("pantograph_states", False),
    "goal_summaries": ("pantograph_goal_summaries", False),
    "revision_events": ("pantograph_revision_events", False),
    "scc_covers": ("pantograph_scc_covers", False),
    "frontend_fragments": ("pantograph_frontend_fragments", False),
    "revision_edges": ("pantograph_revision_edges", True),
    "event_occurrences": ("pantograph_event_occurrences", True),
    "state_goal_edges": ("pantograph_state_goal_edges", True),
    "transitions": ("pantograph_state_transitions", True),
    "frontend_occurrences": ("pantograph_frontend_fragment_occurrences", True),
    "raw_generation_links": ("pantograph_raw_infotree_generation_links", True),
}


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def digest(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def arango_key(prefix: str, value: str) -> str:
    return f"{prefix}_{digest(value)}"


def query_all_rows(target: ArangoTarget, query: str, bind_vars: dict[str, Any]) -> list[Any]:
    """Read every Arango cursor batch; a first-page result is not complete evidence."""
    url = db_url(target, "/_api/cursor")
    response = request_json(
        "POST", url, username=target.username, password=target.password,
        payload={"query": query, "bindVars": bind_vars},
    )
    rows: list[Any] = []
    while True:
        batch = response.get("result") if isinstance(response, dict) else None
        if not isinstance(batch, list):
            raise RuntimeError("Arango cursor response has no result batch")
        rows.extend(batch)
        if not response.get("hasMore"):
            return rows
        cursor_id = response.get("id")
        if not isinstance(cursor_id, (str, int)):
            raise RuntimeError("Arango cursor reports more rows without a cursor id")
        response = request_json(
            "POST", db_url(target, f"/_api/cursor/{cursor_id}"),
            username=target.username, password=target.password, payload={},
        )


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def parse_request(line: str) -> tuple[str, dict[str, Any]]:
    """Parse both documented Pantograph command encodings."""
    try:
        value = json.loads(line)
    except json.JSONDecodeError:
        command, separator, payload_text = line.partition(" ")
        if separator:
            payload = json.loads(payload_text)
            if isinstance(payload, dict):
                return command, payload
        raise
    if isinstance(value, dict) and isinstance(value.get("cmd"), str):
        payload = value.get("payload", {})
        return value["cmd"], payload if isinstance(payload, dict) else {"value": payload}
    if isinstance(value, dict) and len(value) == 1:
        command, payload = next(iter(value.items()))
        if isinstance(command, str) and isinstance(payload, dict):
            return command, payload
    raise ValueError("expected Pantograph JSON {cmd, payload} request")


def response_state_ids(command: str, payload: dict[str, Any], result: Any) -> tuple[list[str], list[str]]:
    """Return parent and child Pantograph IDs from known stateful commands."""
    if not isinstance(result, dict) or "error" in result:
        return [], []
    parents: list[str] = []
    children: list[str] = []

    def add_parent(value: Any) -> None:
        if isinstance(value, int) and not isinstance(value, bool):
            parents.append(str(value))

    def add_child(value: Any) -> None:
        if isinstance(value, int) and not isinstance(value, bool):
            children.append(str(value))

    if command == "goal.start":
        add_child(result.get("stateId"))
    elif command == "goal.tactic":
        add_parent(payload.get("stateId"))
        add_child(result.get("nextStateId", result.get("nextStateId?")))
    elif command == "goal.continue":
        add_parent(payload.get("target"))
        add_parent(payload.get("branch", payload.get("branch?")))
        add_child(result.get("nextStateId", result.get("nextStateId?")))
    elif command == "goal.subsume":
        add_parent(payload.get("stateId"))
        add_parent(payload.get("srcStateId", payload.get("srcStateId?")))
        add_child(result.get("stateId", result.get("stateId?")))
    elif command == "goal.load":
        add_child(result.get("id"))
    elif command == "frontend.distil":
        targets = result.get("targets", [])
        if isinstance(targets, list):
            for target in targets:
                if isinstance(target, dict):
                    add_child(target.get("stateId"))
    return list(dict.fromkeys(parents)), list(dict.fromkeys(children))


def normalize_frontend_invocation(value: Any) -> dict[str, Any]:
    """Select stable, position-free fields from Pantograph's InfoTree projection."""
    if not isinstance(value, dict):
        raise ValueError("Pantograph frontend invocation must be an object")
    required = ("goalBefore", "goalAfter", "tactic")
    if any(not isinstance(value.get(field), str) for field in required):
        raise ValueError("Pantograph frontend invocation is missing goal/tactic text")
    used = value.get("usedConstants", [])
    if not isinstance(used, list):
        raise ValueError("Pantograph frontend invocation usedConstants must be an array")
    constants = sorted({canonical_json(name) for name in used})
    return {
        "schema": "info_geometry.pantograph_infotree_tactic_fragment.v1",
        "goalBefore": value["goalBefore"],
        "tactic": value["tactic"],
        "goalAfter": value["goalAfter"],
        "usedConstants": constants,
        "identityScope": "Pantograph TacticInfo projection; navigation evidence, not proof identity",
    }


def frontend_fragment_key(invocation: Any) -> tuple[str, dict[str, Any], str]:
    """Return a SHA-256 content key, normalized payload, and canonical bytes as text."""
    normalized = normalize_frontend_invocation(invocation)
    encoded = canonical_json(normalized)
    fingerprint = digest(encoded)
    return arango_key("pfi", fingerprint), normalized, fingerprint


def resolve_generation_archetype(
    target: ArangoTarget,
    generation_id: str,
    decl_name: str,
    build_fingerprint: str,
) -> tuple[str, str, str, str, str, list[dict[str, str]]]:
    """Resolve a declaration's complete generation-local SCC cover.

    The returned declaration fingerprint is a digest of the exact stored
    wire-topology declaration fields. It is a retrieval label, not a Lean
    semantic fingerprint or proof of equivalence.
    """
    manifest = request_json(
        "GET", db_url(target, f"/_api/document/ig_graph_generations/{generation_id}"),
        username=target.username, password=target.password,
    )
    if not isinstance(manifest, dict) or manifest.get("status") != "complete":
        raise RuntimeError(f"wire-topology generation {generation_id!r} is absent or incomplete")
    if manifest.get("buildFingerprint") != build_fingerprint:
        raise RuntimeError("wire-topology generation build fingerprint does not match this session")
    collections = manifest.get("collections")
    if not isinstance(collections, dict):
        raise RuntimeError("wire-topology generation manifest has no collection map")
    scc_collection = collections.get("ig_scc")
    decl_collection = collections.get("ig_decl_topologies")
    if not isinstance(scc_collection, str) or not isinstance(decl_collection, str):
        raise RuntimeError("wire-topology generation manifest lacks SCC/declaration collections")

    query = """
FOR occurrence IN ig_archetype_occurrences
  FILTER occurrence.generationId == @generationId
  FILTER PARSE_IDENTIFIER(occurrence._from).collection == @sccCollection
  LET scc = DOCUMENT(occurrence._from)
  FILTER scc != null AND @declName IN scc.decls
  LET topology = FIRST(
    FOR declaration IN @@declCollection
      FILTER declaration.decl == @declName
      LIMIT 2
      RETURN declaration
  )
  FILTER topology != null
  RETURN DISTINCT {
    sccKey: scc._key,
    sccPatternHash: scc.sccPatternHash,
    signatureKey: PARSE_IDENTIFIER(occurrence._to).key,
    patternHash: topology.patternHash,
    roleHash: topology.roleHash
  }
"""
    rows = query_all_rows(target, query, {
        "generationId": generation_id,
        "declName": decl_name,
        "sccCollection": scc_collection,
        "@declCollection": decl_collection,
    })
    if not rows or any(not isinstance(row, dict) for row in rows):
        raise RuntimeError(
            f"expected at least one SCC/archetype row for {decl_name!r} in generation {generation_id!r}"
        )
    required = ("sccKey", "sccPatternHash", "signatureKey", "patternHash", "roleHash")
    if any(any(not isinstance(row.get(field), str) or not row[field] for field in required) for row in rows):
        raise RuntimeError("generation lookup returned incomplete SCC/declaration hash data")
    decl_rows = {(row["patternHash"], row["roleHash"]) for row in rows}
    if len(decl_rows) != 1:
        raise RuntimeError("generation lookup returned inconsistent declaration fingerprint fields")
    pattern_hash, role_hash = next(iter(decl_rows))
    # A declaration commonly occurs in many expression SCCs. Preserve the full
    # sorted cover and hash that set; choosing FIRST would lose topology and make
    # the event identity depend on arbitrary database iteration order.
    occurrences = sorted(
        ({"sccKey": row["sccKey"], "sccPatternHash": row["sccPatternHash"],
          "signatureKey": row["signatureKey"]} for row in rows),
        key=lambda row: (row["sccKey"], row["signatureKey"]),
    )
    occurrences = list({(row["sccKey"], row["signatureKey"]): row for row in occurrences}.values())
    cover_fingerprint = digest(canonical_json({
        "schema": "info_geometry.generation_decl_scc_cover.v1",
        "generationId": generation_id,
        "declName": decl_name,
        "occurrences": occurrences,
    }))
    declaration_identity = {
        "schema": "info_geometry.generation_decl_fingerprint.v1",
        "generationId": generation_id,
        "declName": decl_name,
        "patternHash": pattern_hash,
        "roleHash": role_hash,
    }
    return (
        digest(canonical_json(declaration_identity)),
        generation_id,
        cover_fingerprint,
        "",
        "",
        occurrences,
    )


def verify_raw_infotree_generation_match(
    target: ArangoTarget,
    generation_id: str,
    environment_manifest: dict[str, Any],
) -> dict[str, Any]:
    """Require exact source and computed Lean-context provenance before linking."""
    generation = request_json(
        "GET", db_url(target, f"/_api/document/raw_infotree_generations/{generation_id}"),
        username=target.username, password=target.password,
    )
    if not isinstance(generation, dict) or generation.get("status") != "complete":
        raise RuntimeError("raw InfoTree generation is absent or incomplete")
    source_hash = environment_manifest.get("sourceSha256")
    source_path = environment_manifest.get("sourcePath")
    context_hash = environment_manifest.get("leanContextFingerprint")
    if not all(isinstance(value, str) and value for value in (source_hash, source_path, context_hash)):
        raise RuntimeError("Pantograph session lacks complete source/context fingerprints")
    provenance = generation.get("sourceProvenance")
    if not isinstance(provenance, list) or not provenance:
        raise RuntimeError("raw InfoTree generation has no captured source provenance")
    exact = [row for row in provenance if isinstance(row, dict)
             and row.get("sourcePath") == source_path
             and row.get("sourceSha256") == source_hash
             and row.get("leanContextFingerprint") == context_hash]
    if not exact:
        raise RuntimeError("raw InfoTree generation has no exact source and Lean-context match")
    return {
        "generationId": generation_id,
        "sourcePath": source_path,
        "sourceSha256": source_hash,
        "leanContextFingerprint": context_hash,
    }


class PantographStore:
    def __init__(self, target: ArangoTarget, session_id: str, build_fingerprint: str,
                 parent_event_id: str | None = None,
                 decl_fingerprint: str | None = None,
                 scc_generation: str | None = None,
                 scc_fingerprint: str | None = None,
                 scc_occurrence_key: str | None = None,
                 archetype_signature_key: str | None = None,
                 scc_occurrences: list[dict[str, str]] | None = None,
                 environment_manifest: dict[str, Any] | None = None,
                 raw_infotree_generation_id: str | None = None):
        self.target = target
        self.session_id = session_id
        self.session_key = arango_key("ps", session_id)
        self.build_fingerprint = build_fingerprint
        self.parent_event_id = parent_event_id
        # These are location/index labels, not standalone proof identities.
        # Including them in event identity binds them to this lineage node.
        self.decl_fingerprint = decl_fingerprint
        self.scc_generation = scc_generation
        self.scc_fingerprint = scc_fingerprint
        self.scc_occurrence_key = scc_occurrence_key
        self.archetype_signature_key = archetype_signature_key
        self.scc_occurrences = scc_occurrences or []
        self.environment_manifest = environment_manifest
        self.raw_infotree_generation_id = raw_infotree_generation_id
        self.environment_fingerprint = (
            environment_manifest.get("fingerprint") if environment_manifest else None
        )
        self.scc_cover_key = (
            arango_key("pscc", canonical_json({
                "generation": self.scc_generation,
                "fingerprint": self.scc_fingerprint,
                "occurrences": self.scc_occurrences,
            }))
            if self.scc_occurrences else None
        )
        self.last_event_key: str | None = None
        self._snapshot_digest: str | None = None
        self._pending_event_by_sequence: dict[int, str] = {}

    def url(self, path: str) -> str:
        return db_url(self.target, path)

    def ensure_collections(self) -> None:
        existing = request_json(
            "GET", self.url("/_api/collection"),
            username=self.target.username, password=self.target.password,
        )
        names = {row.get("name") for row in existing.get("result", [])} if isinstance(existing, dict) else set()
        for name, edge in COLLECTIONS.values():
            if name in names:
                continue
            try:
                request_json(
                    "POST", self.url("/_api/collection"),
                    username=self.target.username, password=self.target.password,
                    payload={"name": name, "type": 3 if edge else 2, "waitForSync": True},
                )
            except RuntimeError:
                # Concurrent session startup may have created the collection.
                check = request_json(
                    "GET", self.url(f"/_api/collection/{name}"),
                    username=self.target.username, password=self.target.password,
                )
                if not isinstance(check, dict) or check.get("name") != name:
                    raise

    def insert_immutable(self, collection: str, document: dict[str, Any]) -> None:
        key = document["_key"]
        try:
            request_json(
                "POST", self.url(f"/_api/document/{collection}?waitForSync=true"),
                username=self.target.username, password=self.target.password,
                payload=document,
            )
        except RuntimeError as exc:
            # Permit deterministic retries only when the existing row is exact.
            if "1210" not in str(exc):
                raise
            existing = request_json(
                "GET", self.url(f"/_api/document/{collection}/{key}"),
                username=self.target.username, password=self.target.password,
            )
            volatile = {"_key", "time", "startedAt", "endedAt"}
            expected = {k: v for k, v in document.items() if k not in volatile}
            actual = {k: v for k, v in existing.items() if k not in {"_id", "_key", "_rev"}}
            for field in volatile - {"_key"}:
                actual.pop(field, None)
            if canonical_json(expected) != canonical_json(actual):
                raise RuntimeError(f"immutable Arango key collision in {collection}/{key}") from exc

    def start(self, command: list[str], pantograph_version: str, source_snapshot: Path | None) -> None:
        raw_generation_match = None
        if self.raw_infotree_generation_id is not None:
            if self.environment_manifest is None:
                raise RuntimeError("raw InfoTree generation linking requires --source-snapshot")
            # Perform all provenance checks before creating collections or storing
            # any part of a session that cannot be linked to its requested export.
            raw_generation_match = verify_raw_infotree_generation_match(
                self.target, self.raw_infotree_generation_id, self.environment_manifest
            )
        self.ensure_collections()
        snapshot_key = None
        snapshot_digest = None
        snapshot_path = None
        if source_snapshot is not None:
            source_snapshot = source_snapshot.resolve()
            source_text = source_snapshot.read_bytes().decode("utf-8")
            snapshot_digest = digest(source_text)
            snapshot_key = arango_key("pss", snapshot_digest)
            snapshot_path = str(source_snapshot)
            self.insert_immutable("pantograph_source_snapshots", {
                "_key": snapshot_key,
                "schema": "info_geometry.pantograph_source_snapshot.v1",
                "contentSha256": snapshot_digest,
                "sourceText": source_text,
            })
        self._snapshot_digest = snapshot_digest
        if self.scc_cover_key is not None:
            self.insert_immutable("pantograph_scc_covers", {
                "_key": self.scc_cover_key,
                "schema": "info_geometry.pantograph_scc_cover.v1",
                "generationId": self.scc_generation,
                "coverFingerprint": self.scc_fingerprint,
                "occurrences": self.scc_occurrences,
            })
        root_event_key = self.root_revision_event(snapshot_key, snapshot_digest, command)
        if self.raw_infotree_generation_id is not None:
            assert raw_generation_match is not None
            link_key = arango_key("prgl", canonical_json({
                "rootEventKey": root_event_key, **raw_generation_match,
            }))
            self.insert_immutable("pantograph_raw_infotree_generation_links", {
                "_key": link_key,
                "_from": f"pantograph_revision_events/{root_event_key}",
                "_to": f"raw_infotree_generations/{self.raw_infotree_generation_id}",
                "schema": "info_geometry.pantograph_raw_infotree_generation_link.v1",
                "role": "exact_source_and_lean_context",
                **raw_generation_match,
            })
        self.insert_immutable("pantograph_sessions", {
            "_key": self.session_key,
            "schema": "info_geometry.pantograph_session.v1",
            "sessionId": self.session_id,
            "buildFingerprint": self.build_fingerprint,
            "environmentFingerprint": self.environment_fingerprint,
            "environmentManifest": self.environment_manifest,
            "pantographVersion": pantograph_version,
            "command": command,
            "sourceSnapshotKey": snapshot_key,
            "sourceSnapshotSha256": snapshot_digest,
            "sourcePathHint": snapshot_path,
            "replayBasis": "snapshot-checked-request-log" if snapshot_key else "request-log-only; source baseline not captured",
            "rootEventKey": root_event_key,
            "rawInfoTreeGenerationId": self.raw_infotree_generation_id,
            "rawInfoTreeGenerationMatch": raw_generation_match,
            "startedAt": utc_now(),
        })
        self.last_event_key = root_event_key
        self.session_event("opened", {"pid": os.getpid()})

    def root_revision_event(self, snapshot_key: str | None, snapshot_digest: str | None,
                            command: list[str]) -> str:
        identity = {
            "schema": "info_geometry.revision_event.v1",
            "parentEventKey": self.parent_event_id,
            "sourceSnapshotSha256": snapshot_digest,
            "buildFingerprint": self.build_fingerprint,
            "environmentFingerprint": self.environment_fingerprint,
            "declFingerprint": self.decl_fingerprint,
            "sccGeneration": self.scc_generation,
            "sccFingerprint": self.scc_fingerprint,
            "sccOccurrenceKey": self.scc_occurrence_key,
            "archetypeSignatureKey": self.archetype_signature_key,
            "sccCoverKey": self.scc_cover_key,
            "rootCommand": command,
        }
        event_key = arango_key("rev", canonical_json(identity))
        self.insert_immutable("pantograph_revision_events", {
            "_key": event_key, **identity,
            "sourceSnapshotKey": snapshot_key,
            "eventKind": "session_root",
            "identityScope": "append-only replay lineage event",
        })
        if self.parent_event_id:
            edge_key = arango_key("pre", f"{self.parent_event_id}:{event_key}")
            self.insert_immutable("pantograph_revision_edges", {
                "_key": edge_key,
                "_from": f"pantograph_revision_events/{self.parent_event_id}",
                "_to": f"pantograph_revision_events/{event_key}",
                "role": "revision_child",
            })
        return event_key

    def session_event(self, kind: str, data: dict[str, Any]) -> None:
        body = {"schema": "info_geometry.pantograph_session_event.v1", "sessionKey": self.session_key,
                "sessionId": self.session_id, "kind": kind, "data": data, "time": utc_now()}
        body["_key"] = arango_key("pse", f"{self.session_id}:{kind}:{body['time']}:{canonical_json(data)}")
        self.insert_immutable("pantograph_session_events", body)

    def record_request(self, seq: int, raw: str, command: str, payload: dict[str, Any]) -> str:
        if self.last_event_key is None:
            raise RuntimeError("session root event must be stored before requests")
        key = arango_key("prq", f"{self.session_id}:{seq}")
        raw_hash = digest(raw)
        body = {
            "_key": key, "schema": "info_geometry.pantograph_request.v1",
            "sessionKey": self.session_key, "sessionId": self.session_id,
            "sequence": seq, "command": command, "payload": payload,
            "rawLine": raw, "requestSha256": raw_hash, "time": utc_now(),
        }
        event_identity = {
            "schema": "info_geometry.revision_event.v1",
            "parentEventKey": self.last_event_key,
            "sourceSnapshotSha256": self._snapshot_digest,
            "buildFingerprint": self.build_fingerprint,
            "environmentFingerprint": self.environment_fingerprint,
            "declFingerprint": self.decl_fingerprint,
            "sccGeneration": self.scc_generation,
            "sccFingerprint": self.scc_fingerprint,
            "sccOccurrenceKey": self.scc_occurrence_key,
            "archetypeSignatureKey": self.archetype_signature_key,
            "sccCoverKey": self.scc_cover_key,
            "eventKind": "pantograph_request_intent",
            "requestSha256": raw_hash,
            "command": command,
            "payload": payload,
        }
        event_key = arango_key("rev", canonical_json(event_identity))
        self.insert_immutable("pantograph_revision_events", {
            "_key": event_key, **event_identity,
            "identityScope": "append-only replay lineage event",
        })
        self.insert_immutable("pantograph_revision_edges", {
            "_key": arango_key("pre", f"{self.last_event_key}:{event_key}"),
            "_from": f"pantograph_revision_events/{self.last_event_key}",
            "_to": f"pantograph_revision_events/{event_key}",
            "role": "revision_child",
        })
        body["revisionEventKey"] = event_key
        self.insert_immutable("pantograph_requests", body)
        self.insert_immutable("pantograph_event_occurrences", {
            "_key": arango_key("peo", f"{self.session_id}:{seq}"),
            "_from": f"pantograph_requests/{key}",
            "_to": f"pantograph_revision_events/{event_key}",
            "sessionId": self.session_id,
            "sequence": seq,
        })
        self._pending_event_by_sequence[seq] = event_key
        return key

    def record_response(self, seq: int, request_key: str, raw: str, result: Any,
                        command: str, payload: dict[str, Any]) -> None:
        parent_event_key = self._pending_event_by_sequence.pop(seq, None)
        if parent_event_key is None:
            raise RuntimeError(f"response has no stored request event for sequence {seq}")
        response_key = arango_key("prs", f"{self.session_id}:{seq}")
        response_hash = digest(raw)
        status = response_status(result)
        response_event = {
            "schema": "info_geometry.revision_event.v1",
            "parentEventKey": parent_event_key,
            "sourceSnapshotSha256": self._snapshot_digest,
            "buildFingerprint": self.build_fingerprint,
            "environmentFingerprint": self.environment_fingerprint,
            "declFingerprint": self.decl_fingerprint,
            "sccGeneration": self.scc_generation,
            "sccFingerprint": self.scc_fingerprint,
            "sccOccurrenceKey": self.scc_occurrence_key,
            "archetypeSignatureKey": self.archetype_signature_key,
            "sccCoverKey": self.scc_cover_key,
            "eventKind": "pantograph_response",
            "responseSha256": response_hash,
            "status": status,
        }
        response_event_key = arango_key("rev", canonical_json(response_event))
        self.insert_immutable("pantograph_revision_events", {
            "_key": response_event_key, **response_event,
            "identityScope": "append-only replay lineage event",
        })
        self.insert_immutable("pantograph_revision_edges", {
            "_key": arango_key("pre", f"{parent_event_key}:{response_event_key}"),
            "_from": f"pantograph_revision_events/{parent_event_key}",
            "_to": f"pantograph_revision_events/{response_event_key}",
            "role": "revision_child",
        })
        body = {
            "_key": response_key, "schema": "info_geometry.pantograph_response.v1",
            "sessionKey": self.session_key, "requestKey": request_key,
            "sessionId": self.session_id, "sequence": seq,
            "response": result, "rawLine": raw, "responseSha256": response_hash,
            "revisionEventKey": response_event_key,
            "status": status, "time": utc_now(),
        }
        self.insert_immutable("pantograph_responses", body)
        self.insert_immutable("pantograph_event_occurrences", {
            "_key": arango_key("peo", f"{self.session_id}:{seq}:response"),
            "_from": f"pantograph_responses/{response_key}",
            "_to": f"pantograph_revision_events/{response_event_key}",
            "sessionId": self.session_id,
            "sequence": seq,
            "role": "observed_response",
        })
        self.last_event_key = response_event_key
        parents, children = response_state_ids(command, payload, result)
        for child in children:
            state_key = arango_key("pst", f"{self.session_id}:{child}")
            goals = result.get("goals", result.get("goals?")) if isinstance(result, dict) else None
            state = {
                "_key": state_key, "schema": "info_geometry.pantograph_state.v1",
                "sessionKey": self.session_key, "sessionId": self.session_id,
                "stateId": child, "createdByRequest": request_key,
                "responseKey": response_key, "goals": goals,
                "stateIdScope": "session-local; replay alias only",
                "environmentFingerprint": self.environment_fingerprint or self.build_fingerprint,
            }
            self.insert_immutable("pantograph_states", state)
            if isinstance(goals, list):
                for goal_index, goal in enumerate(goals):
                    summary = {
                        "schema": "info_geometry.pantograph_goal_summary.v1",
                        "goal": goal,
                        "identityScope": "canonical Pantograph JSON only; includes display metadata; navigation, not Expr identity",
                    }
                    summary_hash = digest(canonical_json(summary))
                    summary_key = arango_key("pgs", summary_hash)
                    self.insert_immutable("pantograph_goal_summaries", {
                        "_key": summary_key, **summary, "summarySha256": summary_hash,
                    })
                    edge_key = arango_key("psg", f"{self.session_id}:{child}:{goal_index}:{summary_hash}")
                    self.insert_immutable("pantograph_state_goal_edges", {
                        "_key": edge_key,
                        "_from": f"pantograph_states/{state_key}",
                        "_to": f"pantograph_goal_summaries/{summary_key}",
                        "schema": "info_geometry.pantograph_state_goal.v1",
                        "sessionId": self.session_id, "stateId": child,
                        "goalIndex": goal_index, "summarySha256": summary_hash,
                    })
            for parent in parents:
                from_key = arango_key("pst", f"{self.session_id}:{parent}")
                transition_key = arango_key("ptr", f"{self.session_id}:{seq}:{parent}:{child}")
                self.insert_immutable("pantograph_state_transitions", {
                    "_key": transition_key,
                    "_from": f"pantograph_states/{from_key}",
                    "_to": f"pantograph_states/{state_key}",
                    "schema": "info_geometry.pantograph_transition.v1",
                    "sessionId": self.session_id, "requestKey": request_key,
                    "responseKey": response_key, "sequence": seq,
                    "command": command,
                })


    def record_frontend_invocations(
        self,
        seq: int,
        result: Any,
        invocations_path: Path,
    ) -> int:
        """Persist Pantograph's extracted InfoTree tactic records as shared fragments.

        Pantograph writes this projection only when `frontend.process` receives
        an `invocations?` path. The response supplies compilation-unit source
        boundaries; occurrence edges retain those locations while fragment
        documents omit process IDs and source positions for cross-run reuse.
        """
        if self.last_event_key is None:
            raise RuntimeError("frontend projection has no response event to attach to")
        if not isinstance(result, dict) or not isinstance(result.get("units"), list):
            raise ValueError("frontend.process response has no compilation units")
        exported = json.loads(invocations_path.read_text(encoding="utf-8"))
        if not isinstance(exported, dict) or not isinstance(exported.get("units"), list):
            raise ValueError("Pantograph invocation output has no units array")
        response_units = result["units"]
        data_units = exported["units"]
        if len(response_units) != len(data_units):
            raise ValueError("Pantograph invocation and response unit counts differ")

        count = 0
        for unit_index, (response_unit, data_unit) in enumerate(zip(response_units, data_units)):
            if not isinstance(response_unit, dict) or not isinstance(data_unit, dict):
                raise ValueError("Pantograph compilation unit must be an object")
            invocations = data_unit.get("invocations?", data_unit.get("invocations"))
            if not isinstance(invocations, list):
                raise ValueError(f"Pantograph invocation unit {unit_index} has no invocation array")
            reported_count = response_unit.get("nInvocations", response_unit.get("nInvocations?"))
            if reported_count is not None and reported_count != len(invocations):
                raise ValueError(f"Pantograph invocation count mismatch in unit {unit_index}")
            boundary = response_unit.get("boundary")
            if (not isinstance(boundary, list) or len(boundary) != 2
                    or any(not isinstance(position, int) for position in boundary)):
                raise ValueError(f"Pantograph unit {unit_index} has no valid source boundary")

            for invocation_index, invocation in enumerate(invocations):
                fragment_key, normalized, fingerprint = frontend_fragment_key(invocation)
                self.insert_immutable("pantograph_frontend_fragments", {
                    "_key": fragment_key,
                    **normalized,
                    "fragmentSha256": fingerprint,
                })
                occurrence_identity = canonical_json({
                    "sessionId": self.session_id,
                    "sequence": seq,
                    "unitIndex": unit_index,
                    "invocationIndex": invocation_index,
                    "fragmentKey": fragment_key,
                })
                self.insert_immutable("pantograph_frontend_fragment_occurrences", {
                    "_key": arango_key("pfio", occurrence_identity),
                    "_from": f"pantograph_revision_events/{self.last_event_key}",
                    "_to": f"pantograph_frontend_fragments/{fragment_key}",
                    "schema": "info_geometry.pantograph_frontend_fragment_occurrence.v1",
                    "sessionId": self.session_id,
                    "sequence": seq,
                    "unitIndex": unit_index,
                    "invocationIndex": invocation_index,
                    "sourceBoundary": boundary,
                    "environmentFingerprint": self.environment_fingerprint,
                    "buildFingerprint": self.build_fingerprint,
                })
                count += 1
        return count


def response_status(result: Any) -> str:
    if not isinstance(result, dict):
        return "protocol_error"
    if "error" in result or result.get("parseError") or result.get("parseError?"):
        return "failed"
    if "goals" in result or "goals?" in result:
        return "succeeded" if result.get("goals", result.get("goals?")) is not None else "failed"
    return "returned"


def read_response(stdout: Any) -> str:
    """Read one JSON value, accepting compact and pretty-printed responses."""
    chunks: list[str] = []
    while True:
        line = stdout.readline()
        if line == "":
            raise EOFError("Pantograph exited before returning a response")
        chunks.append(line)
        candidate = "".join(chunks).strip()
        try:
            json.loads(candidate)
            return candidate
        except json.JSONDecodeError:
            continue


def parse_args() -> argparse.Namespace:
    load_repo_arango_env(Path(__file__).resolve().parents[2])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--session-id", required=True)
    parser.add_argument("--parent-event-id",
                        help="Append this session root below an existing pantograph_revision_events document key.")
    parser.add_argument("--build-fingerprint",
                        help="Legacy/import-generation fingerprint. New session environment identity is computed locally.")
    parser.add_argument("--decl-fingerprint",
                        help="Optional declaration fingerprint from the current export generation.")
    parser.add_argument("--scc-generation",
                        help="Generation-local SCC namespace; must be paired with --scc-fingerprint.")
    parser.add_argument("--scc-fingerprint",
                        help="Optional SCC signature within --scc-generation; navigation label only.")
    parser.add_argument("--archetype-generation-id",
                        help="Resolve SCC/declaration hashes from this complete wire-topology generation.")
    parser.add_argument("--decl-name",
                        help="Declaration whose complete SCC cover is resolved within the selected generation.")
    parser.add_argument("--pantograph-version", default="unknown")
    parser.add_argument("--source-snapshot", type=Path,
                        help="Exact owner-source text captured once as an immutable content-addressed replay input.")
    parser.add_argument("--raw-infotree-generation-id",
                        help="Link this session root to a complete raw InfoTree generation only after exact source/context matching.")
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default=arango_database())
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password())
    parser.add_argument("command", nargs=argparse.REMAINDER,
                        help="Pantograph executable and import/options after --")
    args = parser.parse_args()
    if args.command and args.command[0] == "--":
        args.command = args.command[1:]
    if not args.command:
        parser.error("provide Pantograph command after --, e.g. -- lake env repl Mathlib")
    if bool(args.scc_generation) != bool(args.scc_fingerprint):
        parser.error("--scc-generation and --scc-fingerprint must be supplied together")
    if bool(args.archetype_generation_id) != bool(args.decl_name):
        parser.error("--archetype-generation-id and --decl-name must be supplied together")
    if args.archetype_generation_id and (args.scc_generation or args.scc_fingerprint or args.decl_fingerprint):
        parser.error("generation lookup cannot be mixed with manually supplied declaration/SCC fingerprints")
    if args.archetype_generation_id and not args.build_fingerprint:
        parser.error("--archetype-generation-id requires the generation's --build-fingerprint")
    if args.raw_infotree_generation_id and args.source_snapshot is None:
        parser.error("--raw-infotree-generation-id requires --source-snapshot")
    return args


def main() -> int:
    args = parse_args()
    target = ArangoTarget(args.endpoint.rstrip("/"), args.database, args.username, args.password)
    environment_manifest = None
    if args.source_snapshot is not None:
        environment_manifest = build_environment_manifest(
            Path.cwd(), args.source_snapshot, args.command
        )
        source_sha = digest(args.source_snapshot.resolve().read_bytes().decode("utf-8"))
        if source_sha != environment_manifest["sourceSha256"]:
            raise RuntimeError("source snapshot changed while its environment manifest was computed")
    build_fingerprint = args.build_fingerprint or (
        environment_manifest["fingerprint"] if environment_manifest else None
    )
    if not build_fingerprint:
        raise RuntimeError("provide --source-snapshot for computed identity or --build-fingerprint for log-only mode")
    scc_occurrence_key = None
    archetype_signature_key = None
    scc_occurrences: list[dict[str, str]] = []
    if args.archetype_generation_id:
        (
            args.decl_fingerprint,
            args.scc_generation,
            args.scc_fingerprint,
            scc_occurrence_key,
            archetype_signature_key,
            scc_occurrences,
        ) = resolve_generation_archetype(
            target,
            args.archetype_generation_id,
            args.decl_name,
            build_fingerprint,
        )
    store = PantographStore(
        target,
        args.session_id,
        build_fingerprint,
        args.parent_event_id,
        args.decl_fingerprint,
        args.scc_generation,
        args.scc_fingerprint,
        scc_occurrence_key,
        archetype_signature_key,
        scc_occurrences,
        environment_manifest,
        args.raw_infotree_generation_id,
    )
    store.start(args.command, args.pantograph_version, args.source_snapshot)

    child = subprocess.Popen(args.command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                             stderr=None, text=True, bufsize=1)
    assert child.stdin is not None and child.stdout is not None
    seq = 0
    try:
        while True:
            greeting = child.stdout.readline()
            if greeting == "":
                return child.wait()
            sys.stdout.write(greeting)
            sys.stdout.flush()
            if greeting.strip() == "ready.":
                break

        for line in sys.stdin:
            raw = line.rstrip("\r\n")
            if not raw.strip():
                child.stdin.write("\n")
                child.stdin.flush()
                break
            command_name, payload = parse_request(raw)
            seq += 1
            request_key = store.record_request(seq, raw, command_name, payload)
            child.stdin.write(raw + "\n")
            child.stdin.flush()
            response_raw = read_response(child.stdout)
            response = json.loads(response_raw)
            store.record_response(seq, request_key, response_raw, response, command_name, payload)
            sys.stdout.write(response_raw + "\n")
            sys.stdout.flush()
            invocations_path = payload.get("invocations?", payload.get("invocations"))
            if command_name == "frontend.process" and isinstance(invocations_path, str):
                try:
                    invocation_count = store.record_frontend_invocations(
                        seq, response, Path(invocations_path)
                    )
                    print(
                        f"Pantograph InfoTree projection persisted: {invocation_count} invocations",
                        file=sys.stderr,
                        flush=True,
                    )
                except (OSError, ValueError, RuntimeError, json.JSONDecodeError) as exc:
                    store.session_event("frontend_invocations_capture_failed", {
                        "sequence": seq,
                        "error": str(exc)[:1000],
                    })
                    print(f"Pantograph InfoTree projection not persisted: {exc}", file=sys.stderr, flush=True)

        child.stdin.close()
        return child.wait()
    except BaseException as exc:
        store.session_event("interrupted", {"sequence": seq, "error": str(exc)[:1000]})
        if child.poll() is None:
            child.stdin.close()
            child.wait()
        raise
    finally:
        if child.poll() is not None:
            store.session_event("closed", {"sequence": seq, "returnCode": child.returncode})


if __name__ == "__main__":
    raise SystemExit(main())
