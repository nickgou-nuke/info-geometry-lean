#!/usr/bin/env python3
"""Bind a Pantograph session replay observation to a Hive candidate packet.

The emitted packet has navigation authority only. It records a replay result;
it does not certify a theorem, a Lake owner build, or an audit.
"""
from __future__ import annotations

import argparse
import hashlib
import json
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
from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet  # noqa: E402
from tools.infra.pantograph_arango_stream import (  # noqa: E402
    arango_key,
    canonical_json,
    digest,
    parse_request,
    query_all_rows,
)
from tools.infra.pantograph_environment import manifest_fingerprint  # noqa: E402


PACKET_SCHEMA = "info_geometry.hive.pantograph_session_evidence.v1"
REPLAY_STATUS = {
    "matched": "replay_matched",
    "mismatch": "replay_diverged",
    "process_failed": "replay_process_failed",
    "refused_or_failed": "replay_refused",
}


def _fetch_doc(target: ArangoTarget, collection: str, key: str) -> dict[str, Any]:
    value = request_json(
        "GET", db_url(target, f"/_api/document/{collection}/{key}"),
        username=target.username, password=target.password,
    )
    if not isinstance(value, dict):
        raise ValueError(f"missing Arango document {collection}/{key}")
    return value


def fetch_session_bundle(target: ArangoTarget, session_id: str) -> dict[str, Any]:
    """Fetch all rows needed to bind one session; cursor pages are exhausted."""
    session = _fetch_doc(target, "pantograph_sessions", arango_key("ps", session_id))
    if session.get("sessionId") != session_id:
        raise ValueError("session key resolves to a different session id")
    snapshot_key = session.get("sourceSnapshotKey")
    root_key = session.get("rootEventKey")
    if not isinstance(snapshot_key, str) or not isinstance(root_key, str):
        raise ValueError("session lacks an exact source snapshot or revision root")
    snapshot = _fetch_doc(target, "pantograph_source_snapshots", snapshot_key)
    root = _fetch_doc(target, "pantograph_revision_events", root_key)
    requests = query_all_rows(target, """
FOR row IN pantograph_requests
  FILTER row.sessionId == @sessionId
  SORT row.sequence
  RETURN row
""", {"sessionId": session_id})
    responses = query_all_rows(target, """
FOR row IN pantograph_responses
  FILTER row.sessionId == @sessionId
  SORT row.sequence
  RETURN row
""", {"sessionId": session_id})
    events = query_all_rows(target, """
FOR row IN pantograph_session_events
  FILTER row.sessionId == @sessionId
  SORT row.time
  RETURN row
""", {"sessionId": session_id})
    return {
        "session": session,
        "source_snapshot": snapshot,
        "root_event": root,
        "requests": requests,
        "responses": responses,
        "session_events": events,
    }


def _require_digest(value: Any, label: str) -> str:
    if not isinstance(value, str) or len(value) != 64 or any(c not in "0123456789abcdef" for c in value):
        raise ValueError(f"{label} is not a lowercase SHA-256 digest")
    return value


def validate_session_bundle(bundle: dict[str, Any]) -> dict[str, Any]:
    """Check stored session provenance, clean closure, and request/response bindings."""
    session = bundle.get("session")
    snapshot = bundle.get("source_snapshot")
    root = bundle.get("root_event")
    requests = bundle.get("requests")
    responses = bundle.get("responses")
    events = bundle.get("session_events")
    if not all(isinstance(x, dict) for x in (session, snapshot, root)):
        raise ValueError("session bundle is missing session, source snapshot, or root event")
    if not all(isinstance(x, list) for x in (requests, responses, events)):
        raise ValueError("session bundle request/response/event rows must be arrays")

    session_id = session.get("sessionId")
    session_key = arango_key("ps", session_id) if isinstance(session_id, str) and session_id else ""
    if not session_key or session.get("_key") != session_key or session.get("sessionKey", session_key) != session_key:
        raise ValueError("session id and canonical session key do not agree")
    source_hash = _require_digest(session.get("sourceSnapshotSha256"), "session source snapshot hash")
    if snapshot.get("_key") != session.get("sourceSnapshotKey"):
        raise ValueError("source snapshot key does not match the session")
    source_text = snapshot.get("sourceText")
    if not isinstance(source_text, str) or digest(source_text) != source_hash:
        raise ValueError("source snapshot content does not match the session hash")
    if snapshot.get("contentSha256") != source_hash:
        raise ValueError("source snapshot document digest does not match the session")

    environment_hash = _require_digest(session.get("environmentFingerprint"), "environment fingerprint")
    environment = session.get("environmentManifest")
    if not isinstance(environment, dict):
        raise ValueError("session lacks its environment manifest")
    if environment.get("fingerprint") != environment_hash or manifest_fingerprint(environment) != environment_hash:
        raise ValueError("stored environment manifest does not match its fingerprint")
    build_fingerprint = session.get("buildFingerprint")
    if not isinstance(build_fingerprint, str) or not build_fingerprint:
        raise ValueError("session lacks its build fingerprint")
    if (
        root.get("_key") != session.get("rootEventKey")
        or root.get("eventKind") != "session_root"
        or root.get("sourceSnapshotKey") != session.get("sourceSnapshotKey")
    ):
        raise ValueError("session revision root is absent or has the wrong event kind")
    declaration_fingerprint = root.get("declFingerprint")
    if declaration_fingerprint is not None and (not isinstance(declaration_fingerprint, str) or not declaration_fingerprint):
        raise ValueError("session revision root has an invalid declaration fingerprint")
    if session.get("declFingerprint") not in (None, declaration_fingerprint):
        raise ValueError("session declaration fingerprint differs from its revision root")
    for field, expected in (
        ("sourceSnapshotSha256", source_hash),
        ("environmentFingerprint", environment_hash),
        ("buildFingerprint", build_fingerprint),
        ("declFingerprint", declaration_fingerprint),
    ):
        if root.get(field) != expected:
            raise ValueError(f"revision root does not match session {field}")

    if len(requests) == 0 or len(requests) != len(responses):
        raise ValueError("a usable Pantograph trace requires a nonempty paired request/response log")
    if any(not isinstance(row, dict) for row in requests + responses + events):
        raise ValueError("session bundle contains a malformed row")
    session_events = [row for row in events if row.get("sessionId") == session_id]
    if any(row.get("sessionKey") != session_key for row in session_events):
        raise ValueError("session event is bound to a different session key")
    if sum(row.get("kind") == "opened" for row in session_events) != 1:
        raise ValueError("session must have exactly one opened event")
    if any(row.get("kind") == "interrupted" for row in session_events):
        raise ValueError("interrupted Pantograph sessions cannot produce evidence packets")
    closed = [row for row in session_events if row.get("kind") == "closed"]
    if len(closed) != 1 or not isinstance(closed[0].get("data"), dict) or closed[0]["data"].get("returnCode") != 0:
        raise ValueError("session must have exactly one clean process-closure event")

    targets: list[str] = []
    request_keys: list[str] = []
    response_keys: list[str] = []
    for index, (request, response) in enumerate(zip(requests, responses), start=1):
        if request.get("sequence") != index or response.get("sequence") != index:
            raise ValueError("request and response sequences must be contiguous and paired")
        if any(row.get("sessionId") != session_id or row.get("sessionKey") != session_key for row in (request, response)):
            raise ValueError("request or response row belongs to a different session")
        request_key = arango_key("prq", f"{session_id}:{index}")
        response_key = arango_key("prs", f"{session_id}:{index}")
        if request.get("_key") != request_key or response.get("_key") != response_key:
            raise ValueError("request/response document keys do not match their sequence")
        raw_request = request.get("rawLine")
        if not isinstance(raw_request, str) or digest(raw_request) != request.get("requestSha256"):
            raise ValueError(f"request {index} content hash mismatch")
        command, payload = parse_request(raw_request)
        if command != request.get("command") or payload != request.get("payload"):
            raise ValueError(f"request {index} raw line disagrees with stored command/payload")
        raw_response = response.get("rawLine")
        if not isinstance(raw_response, str) or digest(raw_response) != response.get("responseSha256"):
            raise ValueError(f"response {index} content hash mismatch")
        try:
            response_value = json.loads(raw_response)
        except json.JSONDecodeError as exc:
            raise ValueError(f"response {index} raw line is not JSON") from exc
        if response_value != response.get("response"):
            raise ValueError(f"response {index} raw line disagrees with stored response")
        if response.get("requestKey") != request_key:
            raise ValueError(f"response {index} does not reference its paired request")
        if command == "goal.start":
            for name in ("decl", "copyFrom", "expr", "expression"):
                target = payload.get(name)
                if isinstance(target, str) and target.strip():
                    targets.append(target.strip())
                    break
        request_keys.append(request_key)
        response_keys.append(response_key)
    if not targets:
        raise ValueError("session has no goal.start target to bind to the candidate")
    if len(set(targets)) != 1:
        raise ValueError("session contains multiple distinct goal.start targets")
    source_path = session.get("sourcePathHint")
    if not isinstance(source_path, str) or not source_path.strip():
        raise ValueError("session lacks a source path hint")
    return {
        "session_id": session_id,
        "session_key": session_key,
        "root_event_key": str(session["rootEventKey"]),
        "source_hash": source_hash,
        "source_path": source_path,
        "environment_hash": environment_hash,
        "build_fingerprint": build_fingerprint,
        "declaration_fingerprint": declaration_fingerprint,
        "target_expression": targets[0],
        "request_keys": request_keys,
        "response_keys": response_keys,
        "request_count": len(requests),
        "request_hashes": [row["requestSha256"] for row in requests],
        "response_hashes": [row["responseSha256"] for row in responses],
    }


def build_pantograph_evidence_packet(
    candidate: dict[str, Any], bundle: dict[str, Any], replay_result: dict[str, Any],
) -> dict[str, Any]:
    """Build a low-authority packet after validating the archived interaction."""
    if candidate.get("kind") != "TheoremCandidatePacket":
        raise ValueError("Pantograph evidence must be linked to a TheoremCandidatePacket")
    candidate_id = candidate.get("id")
    if not isinstance(candidate_id, str) or not candidate_id:
        raise ValueError("candidate packet has no id")
    evidence = validate_session_bundle(bundle)
    candidate_binding = candidate.get("pantograph_binding")
    if not isinstance(candidate_binding, dict):
        raise ValueError("candidate packet lacks an explicit Pantograph source/target binding")
    if candidate_binding.get("source_path") != evidence["source_path"]:
        raise ValueError("candidate Pantograph source path differs from the session snapshot")
    if candidate_binding.get("source_snapshot_sha256") != evidence["source_hash"]:
        raise ValueError("candidate Pantograph source hash differs from the session snapshot")
    if candidate_binding.get("target_expression") != evidence["target_expression"]:
        raise ValueError("Pantograph goal target differs from the candidate target expression")
    formal_target = candidate.get("formal_target")
    if not isinstance(formal_target, dict):
        raise ValueError("candidate packet lacks its formal target")
    for field, expected in (
        ("target_expression", evidence["target_expression"]),
        ("source_path", evidence["source_path"]),
        ("source_snapshot_sha256", evidence["source_hash"]),
    ):
        if formal_target.get(field) != expected:
            raise ValueError(f"candidate formal target {field} differs from the Pantograph session")
    replay_binding = replay_result.get("session_binding")
    if not isinstance(replay_binding, dict):
        raise ValueError("replay result is not bound to a Pantograph session")
    expected_binding = {
        "sessionId": evidence["session_id"],
        "sourceSnapshotSha256": evidence["source_hash"],
        "environmentFingerprint": evidence["environment_hash"],
        "buildFingerprint": evidence["build_fingerprint"],
        "requestCount": evidence["request_count"],
        "rootEventKey": evidence["root_event_key"],
        "requestSha256s": evidence["request_hashes"],
        "responseSha256s": evidence["response_hashes"],
    }
    if any(replay_binding.get(key) != value for key, value in expected_binding.items()):
        raise ValueError("replay result session/source/environment binding does not match archived evidence")
    outcome = replay_result.get("status")
    status = REPLAY_STATUS.get(str(outcome))
    if status is None:
        raise ValueError("unknown Pantograph replay outcome")
    if outcome == "matched" and replay_result.get("requestCount") != evidence["request_count"]:
        raise ValueError("matched replay request count differs from the archived session")
    if outcome == "mismatch":
        sequence = replay_result.get("sequence")
        if type(sequence) is not int or not 1 <= sequence <= evidence["request_count"]:
            raise ValueError("mismatch replay result has no valid failing sequence")
        replay_count = sequence
    elif outcome == "matched":
        replay_count = evidence["request_count"]
    elif outcome == "process_failed":
        replay_count = evidence["request_count"]
    else:
        replay_count = int(replay_result.get("requestCount", 0)) if type(replay_result.get("requestCount", 0)) is int else 0

    now = datetime.now(timezone.utc).isoformat()
    replay_hash = hashlib.sha256(canonical_json(replay_result).encode("utf-8")).hexdigest()
    identity = f"{candidate_id}:{evidence['session_key']}:{replay_hash}"
    packet_id = "pantograph_evidence_" + hashlib.sha256(identity.encode("utf-8")).hexdigest()[:24]
    packet: dict[str, Any] = {
        "id": packet_id,
        "kind": "PantographSessionEvidencePacket",
        "schema": PACKET_SCHEMA,
        "status": status,
        "lineage_id": str(candidate.get("lineage_id") or candidate_id),
        "revision": 1,
        "origin_run_id": str(candidate.get("origin_run_id") or packet_id),
        "created_at": now,
        "updated_at": now,
        "created_by_agent": "pantograph-evidence-adapter",
        "agent_role": "codex_reviewer",
        "backend": "pantograph",
        "session_key": evidence["session_key"],
        "parent_refs": [{"ref": candidate_id, "kind": "TheoremCandidatePacket", "role": "candidate_under_review"}],
        "evidence_refs": [
            {"ref": f"pantograph_sessions/{evidence['session_key']}", "kind": "PantographSession", "role": "session"},
            {"ref": f"pantograph_revision_events/{evidence['root_event_key']}", "kind": "PantographRevisionEvent", "role": "session_root"},
        ],
        "source_hashes": ["sha256:" + evidence["source_hash"]],
        "packet_version": "1",
        "origin_candidate_ref": {"ref": candidate_id, "kind": "TheoremCandidatePacket", "role": "candidate_under_review"},
        "candidate_link_basis": "caller_asserted_candidate_binding",
        "pantograph_session_key": evidence["session_key"],
        "pantograph_session_id": evidence["session_id"],
        "root_event_key": evidence["root_event_key"],
        "source_path": evidence["source_path"],
        "source_snapshot_sha256": evidence["source_hash"],
        "environment_fingerprint": evidence["environment_hash"],
        "build_fingerprint": evidence["build_fingerprint"],
        "target_expression": evidence["target_expression"],
        "request_count": evidence["request_count"],
        "response_count": evidence["request_count"],
        "request_keys": evidence["request_keys"],
        "response_keys": evidence["response_keys"],
        "request_sha256s": evidence["request_hashes"],
        "response_sha256s": evidence["response_hashes"],
        "replay_outcome": outcome,
        "replay_result": replay_result,
        "replay_result_sha256": replay_hash,
        "replay_completed_request_count": replay_count,
        "evidence_scope": "pantograph_interaction_replay_only",
        "kernel_proof": False,
        "owner_build": False,
        "independent_audit": False,
        "authority": "navigation",
        "promotion_allowed": False,
        "representation_class": "translator",
        "representation_depth": "categorical",
    }
    if evidence["declaration_fingerprint"]:
        packet["declaration_fingerprint"] = evidence["declaration_fingerprint"]
    unsigned = dict(packet)
    packet["packet_hash"] = "sha256:" + hashlib.sha256(canonical_json(unsigned).encode("utf-8")).hexdigest()
    errors = validate_packet(packet, SCHEMA_BY_KIND[packet["kind"]], build_store())
    if errors:
        raise ValueError("built Pantograph evidence packet failed schema validation: " + "; ".join(errors))
    return packet


def _load_json(path: Path) -> Any:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object in {path}")
    return value


def main() -> int:
    load_repo_arango_env(Path(__file__).resolve().parents[2])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--session-id", required=True)
    parser.add_argument("--candidate-packet", type=Path, required=True)
    parser.add_argument("--replay-result", type=Path, required=True,
                        help="JSON output captured from pantograph_arango_replay.py")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default=arango_database())
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password())
    args = parser.parse_args()
    target = ArangoTarget(args.endpoint.rstrip("/"), args.database, args.username, args.password)
    packet = build_pantograph_evidence_packet(
        _load_json(args.candidate_packet),
        fetch_session_bundle(target, args.session_id),
        _load_json(args.replay_result),
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(packet, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"Pantograph evidence packet written: {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
