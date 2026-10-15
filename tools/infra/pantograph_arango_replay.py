#!/usr/bin/env python3
"""Replay one immutable Pantograph request log in a fresh REPL process.

This checks protocol reproducibility against a locally recomputed environment
manifest. It does not prove Lean equivalence; kernel-checked responses remain
the authority for proof terms.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Callable

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
from tools.infra.pantograph_arango_stream import (  # noqa: E402
    arango_key,
    canonical_json,
    digest,
    query_all_rows,
    read_response,
    response_state_ids,
)
from tools.infra.pantograph_environment import (  # noqa: E402
    build_environment_manifest,
    verify_environment_match,
)


TRANSIENT_RESPONSE_FIELDS = {
    "stateId", "stateId?", "nextStateId", "nextStateId?", "root",
}
STATE_REFERENCE_FIELDS = {
    "stateId", "stateId?", "target", "branch", "branch?", "srcStateId?",
    "id",
}


def normalize_response(value: Any, *, omit_load_id: bool = False) -> Any:
    """Remove process-local aliases while retaining goals and diagnostics."""
    if isinstance(value, dict):
        return {
            key: normalize_response(item, omit_load_id=omit_load_id)
            for key, item in sorted(value.items())
            if key not in TRANSIENT_RESPONSE_FIELDS and not (omit_load_id and key == "id")
        }
    if isinstance(value, list):
        return [normalize_response(item, omit_load_id=omit_load_id) for item in value]
    return value


def remap_state_references(command: str, payload: dict[str, Any], mapping: dict[str, int]) -> dict[str, Any]:
    """Rewrite only fields which Pantograph defines as state aliases."""
    rewritten = dict(payload)
    if command == "goal.delete":
        state_ids = rewritten.get("stateIds")
        if isinstance(state_ids, list):
            rewritten["stateIds"] = [mapping.get(str(state_id), state_id) for state_id in state_ids]
        return rewritten
    allowed = {
        "goal.tactic": {"stateId"},
        "goal.continue": {"target", "branch", "branch?"},
        "goal.subsume": {"stateId", "srcStateId?"},
        "goal.print": {"stateId"},
        "goal.save": {"id"},
    }.get(command, set())
    for field in allowed & STATE_REFERENCE_FIELDS:
        value = rewritten.get(field)
        if isinstance(value, (int, str)) and not isinstance(value, bool):
            rewritten[field] = mapping.get(str(value), value)
    return rewritten


def encode_request(command: str, payload: dict[str, Any], original_line: str) -> str:
    """Preserve Pantograph's compact command-line or JSON envelope protocol."""
    if original_line.lstrip().startswith("{"):
        return canonical_json({"cmd": command, "payload": payload})
    return f"{command} {canonical_json(payload)}"


def _command_and_payload(request: dict[str, Any]) -> tuple[str, dict[str, Any]]:
    command = request.get("command")
    payload = request.get("payload")
    if not isinstance(command, str) or not isinstance(payload, dict):
        raise RuntimeError("stored request lacks command/payload fields")
    return command, payload


def replay_exchange(
    command: list[str],
    requests: list[dict[str, Any]],
    responses: list[dict[str, Any]],
    cwd: Path,
    popen: Callable[..., Any] = subprocess.Popen,
) -> dict[str, Any]:
    """Replay ordered request/response documents against a fresh REPL."""
    req_by_seq = {row.get("sequence"): row for row in requests}
    resp_by_seq = {row.get("sequence"): row for row in responses}
    expected_sequences = list(range(1, len(requests) + 1))
    if len(req_by_seq) != len(requests) or sorted(req_by_seq) != expected_sequences:
        raise RuntimeError("request sequence is duplicated or has gaps")
    if len(resp_by_seq) != len(responses) or sorted(resp_by_seq) != expected_sequences:
        raise RuntimeError("every stored request must have exactly one response in sequence")

    child = popen(
        command, cwd=str(cwd), stdin=subprocess.PIPE, stdout=subprocess.PIPE,
        stderr=None, text=True, bufsize=1,
    )
    assert child.stdin is not None and child.stdout is not None
    try:
        greeting = child.stdout.readline()
        if greeting.strip() != "ready.":
            raise RuntimeError(f"Pantograph did not become ready (first line: {greeting[:300]!r})")

        state_map: dict[str, int] = {}
        for sequence in expected_sequences:
            req = req_by_seq[sequence]
            expected_response = resp_by_seq[sequence].get("response")
            if not isinstance(expected_response, (dict, list)):
                raise RuntimeError(f"stored response {sequence} has no JSON response value")
            command_name, original_payload = _command_and_payload(req)
            replay_payload = remap_state_references(command_name, original_payload, state_map)
            raw_request = req.get("rawLine")
            if not isinstance(raw_request, str):
                raise RuntimeError(f"stored request {sequence} has no raw protocol line")
            child.stdin.write(encode_request(command_name, replay_payload, raw_request) + "\n")
            child.stdin.flush()
            actual_response = json.loads(read_response(child.stdout))
            omit_load_id = command_name == "goal.load"
            if normalize_response(actual_response, omit_load_id=omit_load_id) != normalize_response(
                expected_response, omit_load_id=omit_load_id
            ):
                return {
                    "status": "mismatch",
                    "sequence": sequence,
                    "command": command_name,
                    "expected": normalize_response(expected_response, omit_load_id=omit_load_id),
                    "actual": normalize_response(actual_response, omit_load_id=omit_load_id),
                }

            _, expected_children = response_state_ids(command_name, original_payload, expected_response)
            _, actual_children = response_state_ids(command_name, replay_payload, actual_response)
            if len(expected_children) != len(actual_children):
                return {
                    "status": "mismatch",
                    "sequence": sequence,
                    "command": command_name,
                    "reason": "state-branch count differs despite normalized response comparison",
                }
            for old_id, new_id in zip(expected_children, actual_children):
                state_map[old_id] = int(new_id)

        child.stdin.close()
        return_code = child.wait()
        if return_code != 0:
            return {"status": "process_failed", "returnCode": return_code}
        return {"status": "matched", "requestCount": len(expected_sequences)}
    finally:
        if child.poll() is None:
            child.stdin.close()
            child.wait()


def _fetch_doc(target: ArangoTarget, collection: str, key: str) -> dict[str, Any]:
    document = request_json(
        "GET", db_url(target, f"/_api/document/{collection}/{key}"),
        username=target.username, password=target.password,
    )
    if not isinstance(document, dict):
        raise RuntimeError(f"missing {collection}/{key}")
    return document


def load_replay_inputs(target: ArangoTarget, session_id: str) -> tuple[dict[str, Any], str, list[dict[str, Any]], list[dict[str, Any]]]:
    session = _fetch_doc(target, "pantograph_sessions", arango_key("ps", session_id))
    if session.get("sessionId") != session_id:
        raise RuntimeError("session key resolves to a different session id")
    snapshot_key = session.get("sourceSnapshotKey")
    expected_snapshot_hash = session.get("sourceSnapshotSha256")
    if not isinstance(snapshot_key, str) or not isinstance(expected_snapshot_hash, str):
        raise RuntimeError("session has no exact source snapshot; replay is refused")
    snapshot = _fetch_doc(target, "pantograph_source_snapshots", snapshot_key)
    source_text = snapshot.get("sourceText")
    if not isinstance(source_text, str) or digest(source_text) != expected_snapshot_hash:
        raise RuntimeError("stored source snapshot failed SHA-256 verification")
    if snapshot.get("contentSha256") != expected_snapshot_hash:
        raise RuntimeError("snapshot document digest does not match session metadata")
    requests = query_all_rows(target, """
FOR request IN pantograph_requests
  FILTER request.sessionId == @sessionId
  SORT request.sequence
  RETURN request
""", {"sessionId": session_id})
    responses = query_all_rows(target, """
FOR response IN pantograph_responses
  FILTER response.sessionId == @sessionId
  SORT response.sequence
  RETURN response
""", {"sessionId": session_id})
    if any(not isinstance(row, dict) for row in requests + responses):
        raise RuntimeError("session log contains a malformed request or response document")
    return session, source_text, requests, responses


def parse_args() -> argparse.Namespace:
    load_repo_arango_env(Path(__file__).resolve().parents[2])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--session-id", required=True)
    parser.add_argument("--source-path", type=Path,
                        help="Current source file to compare with the stored snapshot; defaults to its path hint.")
    parser.add_argument("--cwd", type=Path,
                        help="Working directory for the recorded REPL command; defaults to the repository root.")
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default=arango_database())
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password())
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    target = ArangoTarget(args.endpoint.rstrip("/"), args.database, args.username, args.password)
    replay_binding: dict[str, Any] | None = None
    try:
        session, source_text, requests, responses = load_replay_inputs(target, args.session_id)
        replay_binding = {
            "sessionId": session.get("sessionId"),
            "rootEventKey": session.get("rootEventKey"),
            "sourceSnapshotSha256": session.get("sourceSnapshotSha256"),
            "environmentFingerprint": session.get("environmentFingerprint"),
            "buildFingerprint": session.get("buildFingerprint"),
            "requestCount": len(requests),
            "requestSha256s": [row.get("requestSha256") for row in requests],
            "responseSha256s": [row.get("responseSha256") for row in responses],
        }
        command = session.get("command")
        if not isinstance(command, list) or not command or any(not isinstance(arg, str) for arg in command):
            raise RuntimeError("session has no replayable command argument vector")
        cwd = (args.cwd or Path(__file__).resolve().parents[2]).resolve()
        if not cwd.is_dir():
            raise RuntimeError(f"replay working directory does not exist: {cwd}")
        source_hint = session.get("sourcePathHint")
        if args.source_path is None and not isinstance(source_hint, str):
            raise RuntimeError("session has no source path hint; pass --source-path")
        source_path = args.source_path or Path(source_hint)
        if not source_path.is_absolute():
            source_path = cwd / source_path
        if not source_path.is_file():
            raise RuntimeError("current source file is unavailable; pass --source-path to verify it")
        if digest(source_path.read_text(encoding="utf-8")) != digest(source_text):
            raise RuntimeError("current source differs from the immutable session snapshot")
        recorded_manifest = session.get("environmentManifest")
        recorded_environment_fp = session.get("environmentFingerprint")
        if not isinstance(recorded_manifest, dict) or not isinstance(recorded_environment_fp, str):
            raise RuntimeError("session has no independently computed environment manifest; replay is refused")
        if recorded_manifest.get("fingerprint") != recorded_environment_fp:
            raise RuntimeError("session and stored environment manifest fingerprints differ")
        current_manifest = build_environment_manifest(cwd, source_path, command)
        verify_environment_match(recorded_manifest, current_manifest)
        result = replay_exchange(command, requests, responses, cwd)
        # Bind the replay outcome to the exact session only after source and
        # environment freshness have both been checked above. This remains
        # interaction evidence, not a Lean proof or owner build receipt.
        result["session_binding"] = replay_binding
        print(json.dumps(result, sort_keys=True, ensure_ascii=False, indent=2))
        return 0 if result["status"] == "matched" else 1
    except (RuntimeError, OSError, ValueError, json.JSONDecodeError) as exc:
        failure = {"status": "refused_or_failed", "reason": str(exc)}
        if replay_binding is not None:
            failure["session_binding"] = replay_binding
        print(json.dumps(failure,
                         sort_keys=True, ensure_ascii=False), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
