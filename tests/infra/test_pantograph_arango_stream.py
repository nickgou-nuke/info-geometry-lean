from __future__ import annotations

from typing import Any

import pytest

from tools.infra.arango_raw_infotree_ingest import ArangoTarget
from tools.infra import pantograph_arango_stream as stream


class MemoryArango:
    """Small HTTP-boundary fake for append-only store contract checks."""

    def __init__(self) -> None:
        self.collections: dict[str, bool] = {}
        self.documents: dict[tuple[str, str], dict[str, Any]] = {}

    def request(self, method: str, url: str, *, payload: Any = None, **_kwargs: Any) -> Any:
        path = url.split("/_db/test/", 1)[1].split("?", 1)[0]
        if path == "_api/collection" and method == "GET":
            return {"result": [{"name": name} for name in self.collections]}
        if path == "_api/collection" and method == "POST":
            name = payload["name"]
            self.collections[name] = bool(payload.get("type") == 3)
            return {"name": name}
        if path.startswith("_api/collection/") and method == "GET":
            name = path.rsplit("/", 1)[1]
            return {"name": name} if name in self.collections else {}
        if path.startswith("_api/document/"):
            document_path = path.removeprefix("_api/document/")
            collection, _, key = document_path.partition("/")
            if method == "POST" and not key:
                key = payload["_key"]
            identity = (collection, key)
            if method == "POST":
                document = dict(payload)
                if identity in self.documents:
                    raise RuntimeError("HTTP 409 errorNum 1210 duplicate key")
                document["_id"] = f"{collection}/{key}"
                document["_rev"] = "1"
                self.documents[identity] = document
                return document
            if method == "GET":
                return self.documents[identity]
        raise AssertionError(f"unexpected fake Arango request: {method} {url}")


def test_event_identity_binds_parent_and_generation_local_scc(monkeypatch: pytest.MonkeyPatch) -> None:
    memory = MemoryArango()
    monkeypatch.setattr(stream, "request_json", memory.request)
    target = ArangoTarget("http://fake", "test", "user", "password")

    def root(parent: str | None, generation: str, scc: str) -> str:
        store = stream.PantographStore(
            target,
            f"session-{parent or 'root'}-{generation}-{scc}",
            "env-1",
            parent,
            "decl-1",
            generation,
            scc,
        )
        store.start(["repl", "Test"], "v4.34.1", None)
        assert store.last_event_key is not None
        return store.last_event_key

    first = root(None, "gen-a", "scc-x")
    same_tuple = root(None, "gen-a", "scc-x")
    other_generation = root(None, "gen-b", "scc-x")
    other_parent = root(first, "gen-a", "scc-x")

    assert first == same_tuple
    assert first != other_generation
    assert first != other_parent
    event = memory.documents[("pantograph_revision_events", first)]
    assert event["declFingerprint"] == "decl-1"
    assert event["sccGeneration"] == "gen-a"
    assert event["sccFingerprint"] == "scc-x"


def test_scc_cover_is_stored_once_and_referenced_by_events(monkeypatch: pytest.MonkeyPatch) -> None:
    memory = MemoryArango()
    monkeypatch.setattr(stream, "request_json", memory.request)
    target = ArangoTarget("http://fake", "test", "user", "password")
    occurrence = {"sccKey": "scc-1", "sccPatternHash": "pattern-1", "signatureKey": "sig-1"}
    store = stream.PantographStore(
        target, "session-cover", "env-1", None, "decl-1", "gen-1", "cover-fp",
        scc_occurrences=[occurrence],
    )
    store.start(["repl", "Test"], "v4.34.1", None)
    event = memory.documents[("pantograph_revision_events", store.last_event_key)]
    cover = memory.documents[("pantograph_scc_covers", event["sccCoverKey"])]
    assert cover["occurrences"] == [occurrence]
    assert event["sccFingerprint"] == "cover-fp"


def test_arango_cursor_reads_all_batches(monkeypatch: pytest.MonkeyPatch) -> None:
    target = ArangoTarget("http://fake", "test", "user", "password")
    calls: list[str] = []

    def fake_request(method: str, url: str, *, payload: Any = None, **_kwargs: Any) -> Any:
        assert method == "POST"
        calls.append(url)
        if url.endswith("/_api/cursor"):
            return {"result": [1, 2], "hasMore": True, "id": "cursor-1"}
        assert url.endswith("/_api/cursor/cursor-1")
        return {"result": [3], "hasMore": False}

    monkeypatch.setattr(stream, "request_json", fake_request)
    assert stream.query_all_rows(target, "RETURN 1", {}) == [1, 2, 3]
    assert len(calls) == 2


def test_request_and_response_events_form_append_only_branch(monkeypatch: pytest.MonkeyPatch) -> None:
    memory = MemoryArango()
    monkeypatch.setattr(stream, "request_json", memory.request)
    target = ArangoTarget("http://fake", "test", "user", "password")
    store = stream.PantographStore(
        target, "session-branch", "env-1", None, "decl-1", "gen-a", "scc-x"
    )
    store.start(["repl", "Test"], "v4.34.1", None)

    request_key = store.record_request(
        1, '{"cmd":"goal.start","payload":{"decl":"Test.foo"}}',
        "goal.start", {"decl": "Test.foo"},
    )
    retry_key = store.record_request(
        1, '{"cmd":"goal.start","payload":{"decl":"Test.foo"}}',
        "goal.start", {"decl": "Test.foo"},
    )
    assert retry_key == request_key
    request = memory.documents[("pantograph_requests", request_key)]
    request_event = request["revisionEventKey"]
    response = '{"stateId":1,"goals":[{"target":"True"}]}'
    store.record_response(1, request_key, response, json_load(response), "goal.start", {})

    response_docs = [
        document for (collection, _), document in memory.documents.items()
        if collection == "pantograph_responses"
    ]
    assert len(response_docs) == 1
    response_event = response_docs[0]["revisionEventKey"]
    events = memory.documents
    assert events[("pantograph_revision_events", request_event)]["parentEventKey"] == store.root_revision_event(
        None, None, ["repl", "Test"]
    )
    assert events[("pantograph_revision_events", response_event)]["parentEventKey"] == request_event
    assert ("pantograph_revision_edges", stream.arango_key("pre", f"{request_event}:{response_event}")) in events
    assert any(collection == "pantograph_states" for collection, _ in events)


def test_frontend_infotree_invocations_deduplicate_and_keep_occurrences(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path,
) -> None:
    import json

    memory = MemoryArango()
    monkeypatch.setattr(stream, "request_json", memory.request)
    target = ArangoTarget("http://fake", "test", "user", "password")
    invocation = {
        "goalBefore": "⊢ A ∧ B",
        "goalAfter": "⊢ A\n⊢ B",
        "tactic": "constructor",
        "usedConstants": ["And.intro", "And.intro"],
    }

    def ingest(session_id: str, boundary: list[int]) -> tuple[str, str]:
        store = stream.PantographStore(target, session_id, "env-1")
        store.start(["repl", "Test"], "v4.34.1", None)
        request = store.record_request(
            1,
            '{"cmd":"frontend.process","payload":{"invocations?":"trace.json"}}',
            "frontend.process",
            {"invocations?": "trace.json"},
        )
        store.record_response(
            1, request, '{"units":[]}', {"units": []}, "frontend.process", {"invocations?": "trace.json"}
        )
        invocation_path = tmp_path / f"{session_id}.json"
        invocation_path.write_text(
            json.dumps({"units": [{"invocations": [invocation]}]}), encoding="utf-8"
        )
        result = {"units": [{"boundary": boundary, "nInvocations": 1}]}
        store.record_frontend_invocations(1, result, invocation_path)
        occurrence = next(
            doc for (collection, _), doc in memory.documents.items()
            if collection == "pantograph_frontend_fragment_occurrences"
            and doc["sessionId"] == session_id
        )
        return occurrence["_to"].split("/", 1)[1], occurrence["_key"]

    first_fragment, first_occurrence = ingest("frontend-a", [0, 30])
    second_fragment, second_occurrence = ingest("frontend-b", [12, 42])

    assert first_fragment == second_fragment
    assert first_occurrence != second_occurrence
    assert len([
        key for collection, key in memory.documents
        if collection == "pantograph_frontend_fragments"
    ]) == 1
    assert len([
        key for collection, key in memory.documents
        if collection == "pantograph_frontend_fragment_occurrences"
    ]) == 2


def test_frontend_fragment_fingerprint_ignores_source_locations_and_constant_order() -> None:
    base = {
        "goalBefore": "⊢ A",
        "goalAfter": "no goals",
        "tactic": "exact h",
        "usedConstants": ["A.h", "A.theorem"],
    }
    reordered = {**base, "usedConstants": ["A.theorem", "A.h"]}
    assert stream.frontend_fragment_key(base)[0] == stream.frontend_fragment_key(reordered)[0]


def test_generation_lookup_checks_manifest_and_derives_labels(monkeypatch: pytest.MonkeyPatch) -> None:
    target = ArangoTarget("http://fake", "test", "user", "password")
    calls: list[tuple[str, str, Any]] = []

    def fake_request(method: str, url: str, *, payload: Any = None, **_kwargs: Any) -> Any:
        calls.append((method, url, payload))
        if url.endswith("ig_graph_generations/gen-1"):
            return {
                "status": "complete",
                "buildFingerprint": "env-1",
                "collections": {
                    "ig_scc": "ig_scc_g_gen-1",
                    "ig_decl_topologies": "ig_decl_topologies_g_gen-1",
                },
            }
        assert payload["bindVars"]["@declCollection"] == "ig_decl_topologies_g_gen-1"
        assert payload["bindVars"]["sccCollection"] == "ig_scc_g_gen-1"
        rows = [
            {
                "sccKey": "scc_17",
                "sccPatternHash": "pattern-scc-17",
                "signatureKey": "arch_abc",
                "patternHash": "pattern-decl",
                "roleHash": "role-decl",
            },
            {
                "sccKey": "scc_18",
                "sccPatternHash": "pattern-scc-18",
                "signatureKey": "arch_def",
                "patternHash": "pattern-decl",
                "roleHash": "role-decl",
            },
        ]
        return {"result": rows}

    monkeypatch.setattr(stream, "request_json", fake_request)
    decl_fp, generation, scc_fp, scc_occurrence, signature, cover = stream.resolve_generation_archetype(
        target, "gen-1", "A.foo", "env-1"
    )
    assert generation == "gen-1"
    assert scc_occurrence == signature == ""
    assert len(decl_fp) == 64
    assert len(scc_fp) == 64
    assert cover == [
        {"sccKey": "scc_17", "sccPatternHash": "pattern-scc-17", "signatureKey": "arch_abc"},
        {"sccKey": "scc_18", "sccPatternHash": "pattern-scc-18", "signatureKey": "arch_def"},
    ]
    assert len(calls) == 2


def test_generation_scc_cover_fingerprint_is_order_independent(monkeypatch: pytest.MonkeyPatch) -> None:
    target = ArangoTarget("http://fake", "test", "user", "password")
    rows = [
        {"sccKey": "scc_2", "sccPatternHash": "p2", "signatureKey": "sig-2", "patternHash": "p", "roleHash": "r"},
        {"sccKey": "scc_1", "sccPatternHash": "p1", "signatureKey": "sig-1", "patternHash": "p", "roleHash": "r"},
    ]

    def resolve_with(data: list[dict[str, str]]) -> str:
        def fake_request(method: str, url: str, *, payload: Any = None, **_kwargs: Any) -> Any:
            if url.endswith("ig_graph_generations/gen-1"):
                return {
                    "status": "complete", "buildFingerprint": "env-1",
                    "collections": {"ig_scc": "scc", "ig_decl_topologies": "decl"},
                }
            return {"result": data}

        monkeypatch.setattr(stream, "request_json", fake_request)
        return stream.resolve_generation_archetype(target, "gen-1", "A.foo", "env-1")[2]

    assert resolve_with(rows) == resolve_with(list(reversed(rows)))


def test_generation_lookup_rejects_different_build_fingerprint(monkeypatch: pytest.MonkeyPatch) -> None:
    target = ArangoTarget("http://fake", "test", "user", "password")
    monkeypatch.setattr(
        stream,
        "request_json",
        lambda *_args, **_kwargs: {
            "status": "complete",
            "buildFingerprint": "other-env",
            "collections": {},
        },
    )
    with pytest.raises(RuntimeError, match="build fingerprint"):
        stream.resolve_generation_archetype(target, "gen-1", "A.foo", "env-1")


def json_load(value: str) -> Any:
    import json

    return json.loads(value)
