"""Tests for F1 ArangoDB lane isolation across tools/alexandria callers and arango_ingest."""
from __future__ import annotations

import json
import sys
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any
from urllib.parse import parse_qs, urlparse

import pytest

from tools.alexandria import (
    arango_ingest,
    automathtext_arango_ingest,
    proof_synthesis_report,
    schema,
    txt2kg_hive_ingest,
    verify_automathtext_arango_descent,
)


def _forbid_network(*args: Any, **kwargs: Any) -> Any:
    raise AssertionError("Unexpected network call when target guard should have rejected")


@pytest.mark.parametrize(
    "endpoint,database",
    [
        ("http://127.0.0.1:8530", "alexandria"),
        ("http://127.0.0.1:8540", "alexandria"),
        ("http://127.0.0.1:8532", "infogeometry"),
        ("http://127.0.0.1:8532", "darwin_commits"),
        ("http://127.0.0.1:8532", "hive_live"),
        ("http://127.0.0.1:8532", "aiclaw_auto_rag"),
    ],
)
def test_alexandria_tools_reject_forbidden_targets_before_network(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    endpoint: str,
    database: str,
) -> None:
    monkeypatch.setattr("urllib.request.urlopen", _forbid_network)
    monkeypatch.setattr(arango_ingest, "urlopen", _forbid_network)

    # 1. arango_ingest.main()
    monkeypatch.setattr(
        sys,
        "argv",
        ["arango_ingest.py", "--search-view-only", "--endpoint", endpoint, "--database", database],
    )
    with pytest.raises(ValueError):
        arango_ingest.main()

    # 2. automathtext_arango_ingest.import_automath_graph()
    with pytest.raises(ValueError):
        automathtext_arango_ingest.import_automath_graph(
            input_dir=tmp_path,
            endpoint=endpoint,
            database=database,
            username="root",
            password="pw",
            dry_run=False,
            skip_indexes=True,
            require_all=False,
        )

    # 3. verify_automathtext_arango_descent.main()
    monkeypatch.setattr(
        sys,
        "argv",
        ["verify_automathtext_arango_descent.py", "--endpoint", endpoint, "--database", database],
    )
    with pytest.raises(ValueError):
        verify_automathtext_arango_descent.main()

    # 4. proof_synthesis_report.main()
    aql_file = tmp_path / "q.aql"
    aql_file.write_text("RETURN 1", encoding="utf-8")
    monkeypatch.setattr(
        sys,
        "argv",
        ["proof_synthesis_report.py", "--aql", str(aql_file), "--endpoint", endpoint, "--database", database],
    )
    with pytest.raises(ValueError):
        proof_synthesis_report.main()

    # 5. txt2kg_hive_ingest.ingest_txt2kg_arango()
    with pytest.raises(ValueError):
        txt2kg_hive_ingest.ingest_txt2kg_arango(
            endpoint=endpoint,
            database=database,
            username="root",
            password="pw",
            sources=[],
            chunks=[],
            triples=[],
            entities=[],
            relationships=[],
        )


def test_arango_ingest_defaults_ignore_8530_env_vars(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    for var in (
        "ALEXANDRIA_ARANGO_ENV_FILE",
        "ALEXANDRIA_ARANGO_ENDPOINT",
        "ALEXANDRIA_ARANGO_PORT",
        "ALEXANDRIA_ARANGO_DB",
        "ALEXANDRIA_ARANGO_DATABASE",
        "ALEXANDRIA_ARANGO_USERNAME",
        "ALEXANDRIA_ARANGO_USER",
        "ALEXANDRIA_ARANGO_PASSWORD",
        "ALEXANDRIA_ARANGO_PASS",
    ):
        monkeypatch.delenv(var, raising=False)

    monkeypatch.setenv("ARANGO_ENDPOINT", "http://127.0.0.1:8530")
    monkeypatch.setenv("ARANGO_DATABASE", "infogeometry")
    monkeypatch.setenv("ARANGO_USER", "infogeo_user")
    monkeypatch.setenv("ARANGO_PASS", "infogeo_pass")

    captured: dict[str, Any] = {}

    def _fake_ensure_search_view(endpoint: str, database: str, username: str, password: str) -> str:
        captured.update(
            {
                "endpoint": endpoint,
                "database": database,
                "username": username,
                "password": password,
            }
        )
        return "updated"

    monkeypatch.setattr(arango_ingest, "ensure_search_view", _fake_ensure_search_view)
    monkeypatch.setattr(sys, "argv", ["arango_ingest.py", "--search-view-only"])

    rc = arango_ingest.main()
    assert rc == 0
    assert captured["endpoint"] == "http://127.0.0.1:8532"
    assert captured["database"] == "alexandria"
    assert captured["username"] == "root"
    assert captured["password"] != "infogeo_pass"
    out = json.loads(capsys.readouterr().out)
    assert out["status"] == "updated"


def test_txt2kg_run_pipeline_defaults_to_8532_alexandria(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    for var in (
        "ALEXANDRIA_ARANGO_ENV_FILE",
        "ALEXANDRIA_ARANGO_ENDPOINT",
        "ALEXANDRIA_ARANGO_PORT",
        "ALEXANDRIA_ARANGO_DB",
        "ALEXANDRIA_ARANGO_DATABASE",
        "ALEXANDRIA_ARANGO_USERNAME",
        "ALEXANDRIA_ARANGO_USER",
        "ALEXANDRIA_ARANGO_PASSWORD",
        "ALEXANDRIA_ARANGO_PASS",
    ):
        monkeypatch.delenv(var, raising=False)
    monkeypatch.setenv("ARANGO_ENDPOINT", "http://127.0.0.1:8530")
    monkeypatch.setenv("ARANGO_DATABASE", "infogeometry")
    monkeypatch.setenv("ARANGO_USER", "infogeo_user")
    monkeypatch.setenv("ARANGO_PASS", "infogeo_pass")

    note = tmp_path / "note.md"
    note.write_text("# Clifford\nClifford algebra defines spinors.\n", encoding="utf-8")
    out_dir = tmp_path / "out"

    seen: dict[str, Any] = {}

    def _fake_ingest(**kwargs: Any) -> dict[str, Any]:
        seen.update(kwargs)
        return {"endpoint": kwargs["endpoint"], "database": kwargs["database"]}

    monkeypatch.setattr(txt2kg_hive_ingest, "ingest_txt2kg_arango", _fake_ingest)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "txt2kg_hive_ingest.py",
            "--input",
            str(note),
            "--output-dir",
            str(out_dir),
            "--extractor",
            "heuristic",
            "--ingest-arango",
        ],
    )
    assert txt2kg_hive_ingest.main() == 0
    assert seen["endpoint"] == "http://127.0.0.1:8532"
    assert seen["database"] == "alexandria"
    assert seen["password"] != "infogeo_pass"


def test_add_search_terms_preserves_precomputed_pdf_terms() -> None:
    row = {
        "title": "Theorem 1.2",
        "text": "Every Krein space admits a fundamental symmetry.",
        "searchTerms": ["krein", "symmetry", "theorem"],
        "provenance": {"sourceFormat": "pdf", "declName": ""},
    }
    updated = arango_ingest.add_search_terms(row)
    assert "krein" in updated["searchTerms"]
    assert "symmetry" in updated["searchTerms"]
    assert "theorem" in updated["searchTerms"]


def test_schema_and_arango_ingest_dag_parity() -> None:
    assert schema.DAG_EDGE_COLLECTION == "alexandria_dag_edges"
    assert "alexandria_dag_edges" in schema.EDGE_COLLECTIONS
    assert "alexandria_dag_edges" in arango_ingest.EDGE_COLLECTIONS
    assert arango_ingest.IMPORT_BATCH_ROWS == 1000
    assert ["contentHash"] in arango_ingest.INDEXES["alexandria_documents"]
    assert ["documentKey"] in arango_ingest.INDEXES["alexandria_dag_edges"]
    assert ["edgeType"] in arango_ingest.INDEXES["alexandria_dag_edges"]
    assert any("alexandria_dag_edges" in q for q in arango_ingest.REMOVE_DOCUMENT_QUERIES)
    dag_idx = next(i for i, q in enumerate(arango_ingest.REMOVE_DOCUMENT_QUERIES) if "alexandria_dag_edges" in q)
    chunk_idx = next(
        i for i, q in enumerate(arango_ingest.REMOVE_DOCUMENT_QUERIES) if "REMOVE c IN alexandria_chunks" in q
    )
    assert dag_idx < chunk_idx

    view_def = arango_ingest.search_view_definition()
    fields = view_def["links"]["alexandria_chunks"]["fields"]
    assert "text" in fields and "title" in fields and "searchTerms" in fields

    assert schema.has_valid_edge_endpoints({"_from": "alexandria_chunks/a", "_to": "alexandria_chunks/b"})
    assert not schema.has_valid_edge_endpoints({"_from": "bad", "_to": "alexandria_chunks/b"})
    assert not schema.has_valid_edge_endpoints({"_from": "alexandria_chunks/", "_to": "alexandria_chunks/b"})


def test_load_artifacts_strict_jsonl_rejects_malformed_and_accepts_comments(tmp_path: Path) -> None:
    # Blank lines, comment lines, and 0-byte files are valid
    (tmp_path / "alexandria_documents.jsonl").write_text(
        "# header comment\n\n" + json.dumps({"_key": "doc_1", "contentHash": "abc"}) + "\n",
        encoding="utf-8",
    )
    (tmp_path / "alexandria_chunks.jsonl").write_text("", encoding="utf-8")
    loaded = arango_ingest.load_artifacts(tmp_path, ["alexandria_documents", "alexandria_chunks"])
    assert len(loaded["alexandria_documents"]) == 1
    assert loaded["alexandria_chunks"] == []

    # 1. Corrupted JSON line
    bad_dir = tmp_path / "bad_json"
    bad_dir.mkdir()
    (bad_dir / "alexandria_chunks.jsonl").write_text('{"_key": "c1"}\n{not_json\n', encoding="utf-8")
    with pytest.raises(ValueError, match=":2: invalid JSON"):
        arango_ingest.load_artifacts(bad_dir, ["alexandria_chunks"])

    # 2. Non-dict JSON value
    non_dict_dir = tmp_path / "non_dict"
    non_dict_dir.mkdir()
    (non_dict_dir / "alexandria_chunks.jsonl").write_text("[1, 2, 3]\n", encoding="utf-8")
    with pytest.raises(ValueError, match="invalid object"):
        arango_ingest.load_artifacts(non_dict_dir, ["alexandria_chunks"])

    # 3. Nonfinite JSON (NaN)
    nan_dir = tmp_path / "nan_json"
    nan_dir.mkdir()
    (nan_dir / "alexandria_chunks.jsonl").write_text('{"_key": "c1", "x": NaN}\n', encoding="utf-8")
    with pytest.raises(ValueError, match="nonfinite JSON"):
        arango_ingest.load_artifacts(nan_dir, ["alexandria_chunks"])

    # 4. Invalid UTF-8 bytes
    utf8_dir = tmp_path / "bad_utf8"
    utf8_dir.mkdir()
    (utf8_dir / "alexandria_chunks.jsonl").write_bytes(b"\xff\xfe\n")
    with pytest.raises(ValueError):
        arango_ingest.load_artifacts(utf8_dir, ["alexandria_chunks"])


def test_drop_rows_for_documents_preserves_cross_doc_dag_edges() -> None:
    rows = {
        "alexandria_documents": [
            {"_key": "doc_a", "contentHash": "ha"},
            {"_key": "doc_b", "contentHash": "hb"},
        ],
        "alexandria_sections": [
            {"_key": "sec_a", "documentKey": "doc_a"},
            {"_key": "sec_b", "documentKey": "doc_b"},
        ],
        "alexandria_chunks": [
            {"_key": "ch_a", "documentKey": "doc_a"},
            {"_key": "ch_b", "documentKey": "doc_b"},
        ],
        "alexandria_entities": [
            {"_key": "ent_a", "documentKey": "doc_a", "chunkKey": "ch_a"},
            {"_key": "ent_b", "documentKey": "doc_b", "chunkKey": "ch_b"},
            {"_key": "ent_doc_only_b", "documentKey": "doc_b"},
        ],
        "alexandria_dag_edges": [
            {
                "_key": "dag_intra_a",
                "_from": "alexandria_chunks/ch_a",
                "_to": "alexandria_sections/sec_a",
                "documentKey": "doc_a",
                "edgeType": "chunk_references_result",
            },
            {
                "_key": "dag_intra_b",
                "_from": "alexandria_chunks/ch_b",
                "_to": "alexandria_sections/sec_b",
                "documentKey": "doc_b",
                "edgeType": "chunk_references_result",
            },
            {
                "_key": "dag_cross_a_to_b",
                "_from": "alexandria_documents/doc_a",
                "_to": "alexandria_documents/doc_b",
                "documentKey": "doc_a",
                "edgeType": "document_cites_document",
            },
            {
                "_key": "dag_cross_b_to_a",
                "_from": "alexandria_documents/doc_b",
                "_to": "alexandria_documents/doc_a",
                "documentKey": "doc_b",
                "edgeType": "document_cites_document",
            },
            {
                "_key": "dag_no_dockey_b",
                "_from": "alexandria_chunks/ch_b",
                "_to": "alexandria_chunks/ch_a",
            },
        ],
    }

    rows_copy = {k: list(v) for k, v in rows.items()}
    arango_ingest.drop_rows_for_documents(rows, {"doc_b"})
    assert [d["_key"] for d in rows["alexandria_documents"]] == ["doc_a"]
    assert [e["_key"] for e in rows["alexandria_entities"]] == ["ent_a"]
    assert [e["_key"] for e in rows["alexandria_dag_edges"]] == [
        "dag_intra_a",
        "dag_cross_a_to_b",
        "dag_cross_b_to_a",
    ]

    arango_ingest.drop_rows_for_documents(rows_copy, {"doc_a", "doc_b"})
    assert rows_copy["alexandria_documents"] == []
    assert rows_copy["alexandria_dag_edges"] == []


class _MockArangoState:
    def __init__(self) -> None:
        self.databases = ["_system", "alexandria"]
        self.collections: dict[str, dict[str, Any]] = {}
        self.rows: dict[str, dict[str, dict[str, Any]]] = {}
        self.indexes: dict[str, list[list[str]]] = {}
        self.views: dict[str, dict[str, Any]] = {}
        self.aql_calls: list[dict[str, Any]] = []


def _start_mock_arango(state: _MockArangoState) -> tuple[ThreadingHTTPServer, str]:
    class _Handler(BaseHTTPRequestHandler):
        def log_message(self, format: str, *args: Any) -> None:  # noqa: A002
            return

        def _send(self, status: int, payload: Any) -> None:
            body = json.dumps(payload).encode("utf-8")
            self.send_response(status)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(body)

        def do_GET(self) -> None:  # noqa: N802
            parsed = urlparse(self.path)
            if parsed.path == "/_api/database":
                self._send(200, {"result": state.databases})
                return
            if parsed.path.endswith("/_api/collection"):
                self._send(200, {"result": [{"name": n, **meta} for n, meta in state.collections.items()]})
                return
            if parsed.path.endswith("/_api/view"):
                self._send(200, {"result": [{"name": n, "type": "arangosearch"} for n in state.views]})
                return
            self._send(404, {"error": True})

        def do_PUT(self) -> None:  # noqa: N802
            parsed = urlparse(self.path)
            length = int(self.headers.get("Content-Length", "0"))
            body = json.loads(self.rfile.read(length).decode("utf-8") or "{}")
            if "/_api/view/" in parsed.path and parsed.path.endswith("/properties"):
                vname = parsed.path.split("/_api/view/", 1)[1].rsplit("/properties", 1)[0]
                state.views[vname] = body
                self._send(200, {"name": vname})
                return
            self._send(404, {"error": True})

        def do_POST(self) -> None:  # noqa: N802
            parsed = urlparse(self.path)
            qs = parse_qs(parsed.query)
            length = int(self.headers.get("Content-Length", "0"))
            raw = self.rfile.read(length).decode("utf-8")
            if parsed.path == "/_api/database":
                payload = json.loads(raw)
                if payload["name"] not in state.databases:
                    state.databases.append(payload["name"])
                self._send(201, {"result": True})
                return
            if parsed.path.endswith("/_api/collection"):
                payload = json.loads(raw)
                name = payload["name"]
                state.collections[name] = {"type": payload.get("type", 2)}
                state.rows.setdefault(name, {})
                self._send(200, {"name": name, "type": payload.get("type", 2)})
                return
            if parsed.path.endswith("/_api/index"):
                col = qs.get("collection", [""])[0]
                payload = json.loads(raw)
                state.indexes.setdefault(col, []).append(payload.get("fields", []))
                self._send(201, {"id": f"{col}/idx"})
                return
            if parsed.path.endswith("/_api/view"):
                payload = json.loads(raw)
                state.views[payload["name"]] = payload
                self._send(201, {"name": payload["name"]})
                return
            if parsed.path.endswith("/_api/import"):
                col = qs.get("collection", [""])[0]
                store = state.rows.setdefault(col, {})
                created = 0
                updated = 0
                for line in raw.splitlines():
                    if not line.strip():
                        continue
                    row = json.loads(line)
                    k = row["_key"]
                    row_copy = dict(row)
                    row_copy["_id"] = f"{col}/{k}"
                    if k in store:
                        updated += 1
                    else:
                        created += 1
                    store[k] = row_copy
                self._send(201, {"error": False, "created": created, "updated": updated, "errors": 0})
                return
            if parsed.path.endswith("/_api/cursor"):
                payload = json.loads(raw)
                query = payload.get("query", "")
                bind = payload.get("bindVars", {})
                state.aql_calls.append({"query": query, "bindVars": bind})
                if "RETURN [d._key, d.contentHash]" in query:
                    keys = set(bind.get("keys", []))
                    res = [
                        [k, doc.get("contentHash")]
                        for k, doc in state.rows.get("alexandria_documents", {}).items()
                        if k in keys
                    ]
                    self._send(201, {"result": res, "hasMore": False})
                    return
                if "REMOVE e IN alexandria_dag_edges" in query:
                    docs = set(bind.get("docs", []))
                    store = state.rows.get("alexandria_dag_edges", {})
                    for k in [k for k, v in store.items() if v.get("documentKey") in docs]:
                        del store[k]
                elif "REMOVE e IN alexandria_chunk_entity_edges" in query:
                    docs = set(bind.get("docs", []))
                    cids = {f"alexandria_chunks/{k}" for k, c in state.rows.get("alexandria_chunks", {}).items() if c.get("documentKey") in docs}
                    store = state.rows.get("alexandria_chunk_entity_edges", {})
                    for k in [k for k, v in store.items() if v.get("_from") in cids]:
                        del store[k]
                elif "REMOVE e IN alexandria_chunk_adjacent_edges" in query:
                    docs = set(bind.get("docs", []))
                    cids = {f"alexandria_chunks/{k}" for k, c in state.rows.get("alexandria_chunks", {}).items() if c.get("documentKey") in docs}
                    store = state.rows.get("alexandria_chunk_adjacent_edges", {})
                    for k in [k for k, v in store.items() if v.get("_from") in cids or v.get("_to") in cids]:
                        del store[k]
                elif "REMOVE e IN alexandria_section_chunk_edges" in query:
                    docs = set(bind.get("docs", []))
                    cids = {f"alexandria_chunks/{k}" for k, c in state.rows.get("alexandria_chunks", {}).items() if c.get("documentKey") in docs}
                    store = state.rows.get("alexandria_section_chunk_edges", {})
                    for k in [k for k, v in store.items() if v.get("_to") in cids]:
                        del store[k]
                elif "REMOVE r IN alexandria_entity_relation_edges" in query:
                    docs = set(bind.get("docs", []))
                    ckeys = {k for k, c in state.rows.get("alexandria_chunks", {}).items() if c.get("documentKey") in docs}
                    store = state.rows.get("alexandria_entity_relation_edges", {})
                    for k in [k for k, v in store.items() if v.get("chunkKey") in ckeys]:
                        del store[k]
                elif "REMOVE en IN alexandria_entities" in query:
                    docs = set(bind.get("docs", []))
                    ckeys = {k for k, c in state.rows.get("alexandria_chunks", {}).items() if c.get("documentKey") in docs}
                    store = state.rows.get("alexandria_entities", {})
                    for k in [k for k, v in store.items() if v.get("chunkKey") in ckeys]:
                        del store[k]
                elif "REMOVE c IN alexandria_chunks" in query:
                    docs = set(bind.get("docs", []))
                    store = state.rows.get("alexandria_chunks", {})
                    for k in [k for k, v in store.items() if v.get("documentKey") in docs]:
                        del store[k]
                elif "REMOVE s IN alexandria_sections" in query:
                    docs = set(bind.get("docs", []))
                    store = state.rows.get("alexandria_sections", {})
                    for k in [k for k, v in store.items() if v.get("documentKey") in docs]:
                        del store[k]
                elif "REMOVE e IN alexandria_document_section_edges" in query:
                    doc_ids = set(bind.get("docIds", []))
                    store = state.rows.get("alexandria_document_section_edges", {})
                    for k in [k for k, v in store.items() if v.get("_from") in doc_ids]:
                        del store[k]
                self._send(201, {"result": [], "hasMore": False})
                return
            self._send(404, {"error": True})

    server = ThreadingHTTPServer(("127.0.0.1", 0), _Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    return server, f"http://127.0.0.1:{server.server_address[1]}"


def _write_jsonl_dir(out_dir: Path, payload: dict[str, list[dict[str, Any]]]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    for col in arango_ingest.DOCUMENT_COLLECTIONS + arango_ingest.EDGE_COLLECTIONS:
        rows = payload.get(col, [])
        (out_dir / f"{col}.jsonl").write_text(
            "".join(json.dumps(r) + "\n" for r in rows),
            encoding="utf-8",
        )


def test_arango_ingest_mocked_http_idempotency_and_batching(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    state = _MockArangoState()
    server, endpoint = _start_mock_arango(state)
    try:
        v1_dir = tmp_path / "v1"
        _write_jsonl_dir(
            v1_dir,
            {
                "alexandria_documents": [
                    {"_key": "doc_a", "path": "/a.pdf", "title": "A", "contentHash": "hash_a1"},
                    {"_key": "doc_b", "path": "/b.pdf", "title": "B", "contentHash": "hash_b1"},
                ],
                "alexandria_sections": [
                    {"_key": "sec_a", "documentKey": "doc_a", "title": "Intro"},
                    {"_key": "sec_b", "documentKey": "doc_b", "title": "Intro"},
                ],
                "alexandria_chunks": [
                    {"_key": "ch_a", "documentKey": "doc_a", "sectionKey": "sec_a", "chunkKind": "theorem", "title": "Thm A", "text": "Krein"},
                    {"_key": "ch_b1", "documentKey": "doc_b", "sectionKey": "sec_b", "chunkKind": "theorem", "title": "Thm B1", "text": "Old B"},
                    {"_key": "ch_b2", "documentKey": "doc_b", "sectionKey": "sec_b", "chunkKind": "proof", "title": "Proof B1", "text": "Proof"},
                ],
                "alexandria_entities": [
                    {"_key": "ent_b", "documentKey": "doc_b", "chunkKey": "ch_b1", "entityType": "math_label", "surface": "thm 1"},
                ],
                "alexandria_dag_edges": [
                    {
                        "_key": "dag_b_proof",
                        "_from": "alexandria_chunks/ch_b2",
                        "_to": "alexandria_chunks/ch_b1",
                        "documentKey": "doc_b",
                        "edgeType": "proof_proves_theorem",
                    },
                    {
                        "_key": "dag_a_cites_b",
                        "_from": "alexandria_documents/doc_a",
                        "_to": "alexandria_documents/doc_b",
                        "documentKey": "doc_a",
                        "edgeType": "document_cites_document",
                    },
                ],
            },
        )

        # 1. Initial ingest
        monkeypatch.setattr(
            sys,
            "argv",
            ["arango_ingest.py", "--input-dir", str(v1_dir), "--endpoint", endpoint, "--database", "alexandria"],
        )
        assert arango_ingest.main() == 0
        summary1 = json.loads(capsys.readouterr().out)
        assert summary1["documents"] == 2
        assert state.collections["alexandria_dag_edges"]["type"] == 3
        assert "alexandria_chunks_search" in state.views
        assert len(state.rows["alexandria_dag_edges"]) == 2

        # 2. --skip-unchanged on identical artifacts -> 0 imported
        monkeypatch.setattr(
            sys,
            "argv",
            ["arango_ingest.py", "--input-dir", str(v1_dir), "--endpoint", endpoint, "--database", "alexandria", "--skip-unchanged"],
        )
        assert arango_ingest.main() == 0
        summary2 = json.loads(capsys.readouterr().out)
        assert summary2["skippedUnchanged"] == 2
        assert summary2["imported"] == {}

        # 3. --replace-documents on doc_b alone -> removes stale doc_b chunks & dag_b_proof, preserves dag_a_cites_b
        v2_dir = tmp_path / "v2_b_only"
        _write_jsonl_dir(
            v2_dir,
            {
                "alexandria_documents": [
                    {"_key": "doc_b", "path": "/b.pdf", "title": "B", "contentHash": "hash_b2"},
                ],
                "alexandria_sections": [
                    {"_key": "sec_b", "documentKey": "doc_b", "title": "Intro"},
                ],
                "alexandria_chunks": [
                    {"_key": "ch_b_new", "documentKey": "doc_b", "sectionKey": "sec_b", "chunkKind": "definition", "title": "Def B2", "text": "New B"},
                ],
                "alexandria_entities": [],
                "alexandria_dag_edges": [],
            },
        )
        monkeypatch.setattr(
            sys,
            "argv",
            ["arango_ingest.py", "--input-dir", str(v2_dir), "--endpoint", endpoint, "--database", "alexandria", "--replace-documents"],
        )
        assert arango_ingest.main() == 0
        _ = capsys.readouterr()
        assert set(state.rows["alexandria_chunks"]) == {"ch_a", "ch_b_new"}
        assert set(state.rows["alexandria_entities"]) == set()
        assert set(state.rows["alexandria_dag_edges"]) == {"dag_a_cites_b"}

        # 4. Batching test with >200 doc keys
        state.aql_calls.clear()
        target = arango_ingest._target(endpoint, "alexandria", "root", "pw")
        many_keys = [f"doc_{i}" for i in range(250)]
        _ = arango_ingest.existing_content_hashes(target, many_keys, batch=100)
        hash_queries = [c for c in state.aql_calls if "RETURN [d._key, d.contentHash]" in c["query"]]
        assert len(hash_queries) == 3

        state.aql_calls.clear()
        arango_ingest.remove_documents(target, many_keys, batch=100)
        dag_del_queries = [c for c in state.aql_calls if "REMOVE e IN alexandria_dag_edges" in c["query"]]
        assert len(dag_del_queries) == 3
    finally:
        server.shutdown()
        server.server_close()


def test_import_rows_raises_when_errors_count_positive(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        arango_ingest,
        "import_jsonl",
        lambda *args, **kwargs: {"error": False, "created": 0, "errors": 2},
    )
    with pytest.raises(RuntimeError, match="import into alexandria_chunks failed"):
        arango_ingest.import_rows(
            "http://127.0.0.1:8532",
            "alexandria",
            "root",
            "pw",
            "alexandria_chunks",
            [{"_key": "c1"}],
        )
