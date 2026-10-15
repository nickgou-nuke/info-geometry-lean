from __future__ import annotations

import hashlib
import json

import pytest

from tools.infra.hive_arango_queue import COLLECTIONS, validate_packet_invariants
from tools.infra.hive_motherbee import discover_tasks
from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet
from tools.infra.pantograph_arango_stream import arango_key, canonical_json, digest
from tools.infra.pantograph_environment import manifest_fingerprint
from tools.infra.pantograph_evidence_packet import build_pantograph_evidence_packet


def session_bundle() -> dict:
    session_id = "session-test"
    session_key = arango_key("ps", session_id)
    source_text = "import Mathlib\n"
    source_hash = digest(source_text)
    environment = {"lean": "Lean 4", "lake": "Lake"}
    environment["fingerprint"] = manifest_fingerprint(environment)
    environment_hash = environment["fingerprint"]
    root_key = "rev_test_root"
    request_raw = json.dumps(
        {"cmd": "goal.start", "payload": {"expr": "∀ x : Nat, x = x"}},
        separators=(",", ":"),
    )
    response_value = {"stateId": 1, "goals": [{"target": "∀ x : Nat, x = x"}]}
    response_raw = json.dumps(response_value, separators=(",", ":"))
    request_key = arango_key("prq", f"{session_id}:1")
    response_key = arango_key("prs", f"{session_id}:1")
    return {
        "session": {
            "_key": session_key,
            "sessionId": session_id,
            "rootEventKey": root_key,
            "sourceSnapshotKey": "snapshot-1",
            "sourceSnapshotSha256": source_hash,
            "sourcePathHint": "lean/Example.lean",
            "environmentManifest": environment,
            "environmentFingerprint": environment_hash,
            "buildFingerprint": "build-fingerprint",
            "declFingerprint": "decl-fingerprint",
        },
        "source_snapshot": {
            "_key": "snapshot-1",
            "sourceText": source_text,
            "contentSha256": source_hash,
        },
        "root_event": {
            "_key": root_key,
            "eventKind": "session_root",
            "sourceSnapshotKey": "snapshot-1",
            "sourceSnapshotSha256": source_hash,
            "environmentFingerprint": environment_hash,
            "buildFingerprint": "build-fingerprint",
            "declFingerprint": "decl-fingerprint",
        },
        "requests": [{
            "_key": request_key,
            "sessionId": session_id,
            "sessionKey": session_key,
            "sequence": 1,
            "command": "goal.start",
            "payload": {"expr": "∀ x : Nat, x = x"},
            "rawLine": request_raw,
            "requestSha256": digest(request_raw),
        }],
        "responses": [{
            "_key": response_key,
            "sessionId": session_id,
            "sessionKey": session_key,
            "sequence": 1,
            "requestKey": request_key,
            "response": response_value,
            "rawLine": response_raw,
            "responseSha256": digest(response_raw),
        }],
        "session_events": [
            {"sessionId": session_id, "sessionKey": session_key, "kind": "opened", "data": {}},
            {"sessionId": session_id, "sessionKey": session_key, "kind": "closed", "data": {"returnCode": 0}},
        ],
    }


def candidate_packet() -> dict:
    bundle = session_bundle()
    return {
        "kind": "TheoremCandidatePacket",
        "id": "candidate-1",
        "lineage_id": "lineage-1",
        "origin_run_id": "run-1",
        "formal_target": {
            "summary": "identity target",
            "target_expression": bundle["requests"][0]["payload"]["expr"],
            "source_path": bundle["session"]["sourcePathHint"],
            "source_snapshot_sha256": bundle["session"]["sourceSnapshotSha256"],
        },
        "pantograph_binding": {
            "source_path": bundle["session"]["sourcePathHint"],
            "source_snapshot_sha256": bundle["session"]["sourceSnapshotSha256"],
            "target_expression": bundle["requests"][0]["payload"]["expr"],
        },
    }


def matched_replay(bundle_data: dict | None = None) -> dict:
    b = bundle_data or session_bundle()
    return {
        "status": "matched",
        "requestCount": 1,
        "session_binding": {
            "sessionId": b["session"]["sessionId"],
            "rootEventKey": b["session"]["rootEventKey"],
            "sourceSnapshotSha256": b["source_snapshot"]["contentSha256"],
            "environmentFingerprint": b["session"]["environmentFingerprint"],
            "buildFingerprint": b["session"]["buildFingerprint"],
            "requestCount": len(b["requests"]),
            "requestSha256s": [row["requestSha256"] for row in b["requests"]],
            "responseSha256s": [row["responseSha256"] for row in b["responses"]],
        },
    }


def test_packet_binds_replay_and_keeps_navigation_only_authority() -> None:
    b = session_bundle()
    packet = build_pantograph_evidence_packet(candidate_packet(), b, matched_replay(b))
    assert packet["authority"] == "navigation"
    assert packet["promotion_allowed"] is False
    assert packet["kernel_proof"] is False
    assert packet["owner_build"] is False
    assert packet["status"] == "replay_matched"
    assert packet["origin_candidate_ref"]["ref"] == "candidate-1"
    assert validate_packet(packet, SCHEMA_BY_KIND[packet["kind"]], build_store()) == []


def test_packet_records_a_replay_divergence_without_promoting_it() -> None:
    b = session_bundle()
    packet = build_pantograph_evidence_packet(
        candidate_packet(),
        b,
        {
            "status": "mismatch",
            "sequence": 1,
            "reason": "goal changed",
            "session_binding": {
                "sessionId": b["session"]["sessionId"],
                "rootEventKey": b["session"]["rootEventKey"],
                "sourceSnapshotSha256": b["source_snapshot"]["contentSha256"],
                "environmentFingerprint": b["session"]["environmentFingerprint"],
                "buildFingerprint": b["session"]["buildFingerprint"],
                "requestCount": len(b["requests"]),
                "requestSha256s": [row["requestSha256"] for row in b["requests"]],
                "responseSha256s": [row["responseSha256"] for row in b["responses"]],
            },
        },
    )
    assert packet["status"] == "replay_diverged"
    assert packet["replay_completed_request_count"] == 1
    assert packet["promotion_allowed"] is False


def test_request_payload_tampering_is_rejected_even_if_saved_payload_is_rewritten() -> None:
    bundle = session_bundle()
    bundle["requests"][0]["payload"] = {"expr": "True"}
    with pytest.raises(ValueError, match="raw line disagrees"):
        build_pantograph_evidence_packet(candidate_packet(), bundle, matched_replay())


def test_response_tampering_is_rejected_even_if_saved_response_is_rewritten() -> None:
    bundle = session_bundle()
    bundle["responses"][0]["response"] = {"stateId": 1, "goals": []}
    with pytest.raises(ValueError, match="raw line disagrees"):
        build_pantograph_evidence_packet(candidate_packet(), bundle, matched_replay())


def test_empty_incomplete_or_interrupted_sessions_are_rejected() -> None:
    bundle = session_bundle()
    bundle["requests"] = []
    bundle["responses"] = []
    with pytest.raises(ValueError, match="nonempty"):
        build_pantograph_evidence_packet(candidate_packet(), bundle, matched_replay())

    bundle = session_bundle()
    bundle["session_events"].append({"sessionId": "session-test", "sessionKey": bundle["session"]["_key"], "kind": "interrupted", "data": {}})
    with pytest.raises(ValueError, match="interrupted"):
        build_pantograph_evidence_packet(candidate_packet(), bundle, matched_replay())


def test_motherbee_routes_evidence_to_semantic_question_and_critique() -> None:
    evidence = build_pantograph_evidence_packet(candidate_packet(), session_bundle(), matched_replay())
    tasks = discover_tasks([evidence], store_path=__import__("pathlib").Path("/tmp/hive-evidence-test.jsonl"), dry_run_task=True)
    assert {task["assigned_role"] for task in tasks} == {"SocratesBee", "PauliBee"}
    assert all(task["authority_ceiling"] == "semantic" for task in tasks)
    assert all("LeanVerificationPacket" in task["forbidden_output_kinds"] for task in tasks)


def test_arango_queue_rejects_authority_escalation() -> None:
    packet = build_pantograph_evidence_packet(candidate_packet(), session_bundle(), matched_replay())
    queue_packet = {
        **packet,
        "schema": "info_geometry.hive.pantograph_session_evidence.v1",
    }
    checked = validate_packet_invariants(queue_packet)
    assert checked["authority"] == "navigation"
    assert checked["promotion_allowed"] is False
    assert any(spec.name == "hive_pantograph_session_evidence" for spec in COLLECTIONS)
    round_trip = validate_packet_invariants(checked)
    assert round_trip["packet_hash"] == checked["packet_hash"]

    list_depth_packet = {**queue_packet, "representation_depth": ["operatorial", "categorical"]}
    unsigned = dict(list_depth_packet)
    unsigned.pop("packet_hash")
    list_depth_packet["packet_hash"] = "sha256:" + hashlib.sha256(canonical_json(unsigned).encode()).hexdigest()
    checked = validate_packet_invariants(list_depth_packet)
    assert checked["authority"] == "navigation"
    assert checked["promotion_allowed"] is False
    with pytest.raises(ValueError, match="navigation authority"):
        validate_packet_invariants({**list_depth_packet, "authority": "lean_checked"})
    with pytest.raises(ValueError, match="cannot authorize promotion"):
        validate_packet_invariants({**list_depth_packet, "promotion_allowed": True})
    with pytest.raises(ValueError, match="disagrees with replay outcome"):
        validate_packet_invariants({**list_depth_packet, "status": "replay_diverged"})
    contradictory_result = dict(packet["replay_result"])
    contradictory_result["status"] = "mismatch"
    with pytest.raises(ValueError, match="nested Pantograph replay status"):
        validate_packet_invariants({**packet, "replay_result": contradictory_result})


def test_candidate_target_and_replay_session_must_match() -> None:
    bundle = session_bundle()
    candidate = candidate_packet()
    candidate["pantograph_binding"]["target_expression"] = "True"
    with pytest.raises(ValueError, match="target expression"):
        build_pantograph_evidence_packet(candidate, bundle, matched_replay(bundle))

    candidate = candidate_packet()
    candidate["formal_target"]["target_expression"] = "True"
    with pytest.raises(ValueError, match="formal target target_expression"):
        build_pantograph_evidence_packet(candidate, bundle, matched_replay(bundle))

    with pytest.raises(ValueError, match="not bound"):
        build_pantograph_evidence_packet(candidate_packet(), bundle, {"status": "matched", "requestCount": 1})

    replay = matched_replay(bundle)
    replay["session_binding"]["environmentFingerprint"] = "0" * 64
    with pytest.raises(ValueError, match="binding does not match"):
        build_pantograph_evidence_packet(candidate_packet(), bundle, replay)


def test_bound_stale_environment_refusal_is_recorded_without_promotion() -> None:
    bundle = session_bundle()
    replay = matched_replay(bundle)
    replay["status"] = "refused_or_failed"
    replay["reason"] = "Lean environment fingerprint differs"
    replay.pop("requestCount")
    packet = build_pantograph_evidence_packet(candidate_packet(), bundle, replay)
    assert packet["status"] == "replay_refused"
    assert packet["replay_completed_request_count"] == 0
    assert packet["promotion_allowed"] is False
    validate_packet_invariants(packet)
