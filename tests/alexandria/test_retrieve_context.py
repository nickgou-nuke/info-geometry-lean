from __future__ import annotations

import json
import subprocess
import sys
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any

from tools.alexandria.retrieve_context import (
    retrieve_arango_context,
    retrieve_jsonl_context,
    safe_search_terms,
)

REPO = Path(__file__).resolve().parents[2]
TOOL = REPO / "tools" / "alexandria" / "retrieve_context.py"


def write_jsonl(path: Path, records: list[dict]) -> None:
    path.write_text("".join(json.dumps(record) + "\n" for record in records), encoding="utf-8")


class _MockArangoServer:
    def __init__(self, rows: list[dict[str, Any]]) -> None:
        self.rows = rows
        self.requests: list[dict[str, Any]] = []
        outer = self

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, format: str, *args: object) -> None:  # noqa: A003
                return

            def do_POST(self) -> None:  # noqa: N802
                length = int(self.headers.get("Content-Length", "0"))
                body = json.loads(self.rfile.read(length).decode("utf-8")) if length else {}
                outer.requests.append({"path": self.path, "body": body})
                payload = {
                    "error": False,
                    "hasMore": False,
                    "extra": {"warnings": []},
                    "result": outer.rows,
                }
                raw = json.dumps(payload).encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(raw)))
                self.end_headers()
                self.wfile.write(raw)

        self._server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.port = self._server.server_port
        self.endpoint = f"http://127.0.0.1:{self.port}"
        self._thread = threading.Thread(target=self._server.serve_forever, daemon=True)

    def __enter__(self) -> "_MockArangoServer":
        self._thread.start()
        return self

    def __exit__(self, *_: object) -> None:
        self._server.shutdown()
        self._server.server_close()


def test_retrieve_context_includes_source_and_score_breakdown(tmp_path: Path) -> None:
    write_jsonl(
        tmp_path / "alexandria_documents.jsonl",
        [
            {
                "_key": "doc_1",
                "title": "paper",
                "path": "paper.tex.md",
                "contentHash": "abc123",
                "sourceKind": "paper",
                "sourceFormat": "latex",
            }
        ],
    )
    write_jsonl(
        tmp_path / "alexandria_sections.jsonl",
        [{"_key": "sec_1", "documentKey": "doc_1", "title": "Main Results", "level": 1, "ordinal": 1}],
    )
    write_jsonl(
        tmp_path / "alexandria_chunks.jsonl",
        [
            {
                "_key": "chunk_1",
                "documentKey": "doc_1",
                "sectionKey": "sec_1",
                "ordinal": 1,
                "chunkKind": "theorem",
                "title": "Main Results",
                "text": "Theorem. A local Weyl symmetry statement.",
                "tokens": ["theorem", "local", "weyl", "symmetry", "statement"],
                "provenance": {"path": "paper.tex.md", "sourceUri": "file:///paper.tex.md", "sourceKind": "paper", "sourceFormat": "latex", "pageStart": 3},
            },
            {
                "_key": "chunk_2",
                "documentKey": "doc_1",
                "sectionKey": "sec_1",
                "ordinal": 2,
                "chunkKind": "proof",
                "title": "Main Results",
                "text": "Proof. Assume the candidate commutes.",
                "tokens": ["proof", "assume", "candidate", "commutes"],
                "provenance": {"path": "paper.tex.md", "sourceUri": "file:///paper.tex.md", "sourceKind": "paper", "sourceFormat": "latex", "pageStart": 4},
            },
        ],
    )
    write_jsonl(
        tmp_path / "alexandria_entities.jsonl",
        [
            {"_key": "ent_1", "chunkKey": "chunk_1", "entityType": "theorem", "surface": "Theorem", "normalized": "Theorem", "confidence": 1.0, "domain": "default"},
            {"_key": "ent_2", "chunkKey": "chunk_2", "entityType": "proof", "surface": "Proof", "normalized": "Proof", "confidence": 1.0, "domain": "default"},
        ],
    )
    write_jsonl(
        tmp_path / "alexandria_chunk_entity_edges.jsonl",
        [
            {"_key": "edge_1", "_from": "alexandria_chunks/chunk_1", "_to": "alexandria_entities/ent_1", "entityType": "theorem", "confidence": 1.0},
            {"_key": "edge_2", "_from": "alexandria_chunks/chunk_2", "_to": "alexandria_entities/ent_2", "entityType": "proof", "confidence": 1.0},
        ],
    )
    write_jsonl(
        tmp_path / "alexandria_chunk_adjacent_edges.jsonl",
        [{"_key": "adj_1", "_from": "alexandria_chunks/chunk_1", "_to": "alexandria_chunks/chunk_2", "kind": "adjacent", "weight": 1.0}],
    )
    write_jsonl(
        tmp_path / "alexandria_dag_edges.jsonl",
        [{"_key": "dag_1", "_from": "alexandria_chunks/chunk_2", "_to": "alexandria_chunks/chunk_1", "edgeType": "proof_proves_theorem", "confidence": 0.95}],
    )

    result = subprocess.run(
        [
            sys.executable,
            str(TOOL),
            "--query",
            "main results local weyl theorem",
            "--input-dir",
            str(tmp_path),
            "--top-k",
            "1",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    packet = json.loads(result.stdout)

    assert packet["authority"] == "retrieval_context_only"
    assert packet["sourceAuthority"] == "retrieval_context_only"
    assert "not verified lean proof" in packet["disclaimer"].lower()

    hit = packet["hits"][0]
    assert hit["source"]["sourceKind"] == "paper"
    assert hit["source"]["sourceUri"] == "file:///paper.tex.md"
    assert hit["contentHash"] == "abc123"
    assert hit["pageStart"] == 3
    assert hit["scoreBreakdown"]["lexical"] >= 2
    assert hit["scoreBreakdown"]["title"] >= 1
    assert hit["entities"]
    assert hit["dagNeighbors"] and hit["dagNeighbors"][0]["edgeType"] == "proof_proves_theorem"


def test_safe_search_terms_does_not_split_letter_digit_boundaries() -> None:
    assert safe_search_terms("xqzv99nonexistenttoken77") == ["xqzv99nonexistenttoken77"]
    terms = safe_search_terms("MeasureTheory.Measure.map_apply Cl22")
    assert "measuretheory.measure.map_apply" in terms
    assert "measuretheory" in terms
    assert "map" in terms
    assert "apply" in terms
    assert "cl22" in terms
    assert "22" not in terms


def test_retrieve_context_missing_dir_empty_query_and_negative_top_k(tmp_path: Path) -> None:
    missing = subprocess.run(
        [sys.executable, str(TOOL), "--input-dir", str(tmp_path / "missing"), "--query", "Clifford"],
        capture_output=True,
        text=True,
    )
    assert missing.returncode != 0
    assert "Traceback" not in missing.stderr

    neg = subprocess.run(
        [sys.executable, str(TOOL), "--input-dir", str(tmp_path), "--query", "Clifford", "--top-k", "-1"],
        capture_output=True,
        text=True,
    )
    assert neg.returncode == 2

    write_jsonl(tmp_path / "alexandria_chunks.jsonl", [{"_key": "c1", "text": "Clifford", "tokens": ["clifford"]}])
    for q in ("", "   "):
        empty = subprocess.run(
            [sys.executable, str(TOOL), "--input-dir", str(tmp_path), "--query", q],
            capture_output=True,
            text=True,
            check=True,
        )
        pkt = json.loads(empty.stdout)
        assert pkt["hits"] == []
        assert pkt["authority"] == "retrieval_context_only"


def test_retrieve_context_arango_mode_mock_and_lane_guard() -> None:
    sample_rows = [
        {
            "chunk": {
                "_key": "chk_1",
                "_id": "alexandria_chunks/chk_1",
                "documentKey": "doc_clifford",
                "chunkKind": "theorem",
                "title": "Hestenes Spinor Decomposition",
                "text": "Every Dirac-Hestenes spinor admits a multivector Clifford factorization.",
                "tokens": ["hestenes", "spinor", "clifford", "multivector"],
                "provenance": {"path": "/corpus/dirac-hestenes.pdf", "contentHash": "deadbeef1234", "pageStart": 7, "pageEnd": 8},
            },
            "document": {"_key": "doc_clifford", "title": "Dirac-Hestenes", "path": "/corpus/dirac-hestenes.pdf", "contentHash": "deadbeef1234"},
            "score": 8.42,
            "entities": [{"_key": "ent_1", "entityType": "concept", "surface": "Dirac-Hestenes spinor", "normalized": "dirac hestenes spinor"}],
            "adjNeighbors": [{"_key": "chk_2", "_id": "alexandria_chunks/chk_2", "chunkKind": "proof", "title": "Proof", "edgeType": "adjacent", "direction": "outbound"}],
            "dagNeighbors": [{"_key": "chk_2", "_id": "alexandria_chunks/chk_2", "chunkKind": "proof", "title": "Proof", "edgeType": "proof_proves_theorem", "direction": "inbound"}],
        }
    ]
    with _MockArangoServer(sample_rows) as srv:
        proc = subprocess.run(
            [
                sys.executable,
                str(TOOL),
                "--arango",
                "--endpoint",
                srv.endpoint,
                "--database",
                "alexandria_unit_test",
                "--query",
                "Hestenes spinor",
                "--limit",
                "3",
                "--hops",
                "2",
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        packet = json.loads(proc.stdout)
        assert packet["authority"] == "retrieval_context_only"
        assert packet["mode"] == "arango"
        assert len(packet["hits"]) == 1
        hit = packet["hits"][0]
        assert hit["documentKey"] == "doc_clifford"
        assert hit["contentHash"] == "deadbeef1234"
        assert hit["pageStart"] == 7
        assert hit["dagNeighbors"][0]["edgeType"] == "proof_proves_theorem"

        req = srv.requests[0]["body"]
        assert "OPTIONS {waitForSync: true}" in req["query"]
        assert req["bindVars"]["limit"] == 3
        assert req["bindVars"]["hops"] == 2
        assert req["bindVars"]["q"] == "Hestenes spinor"

        text_proc = subprocess.run(
            [
                sys.executable,
                str(TOOL),
                "--arango",
                "--endpoint",
                srv.endpoint,
                "--database",
                "alexandria_unit_test",
                "--query",
                "Hestenes spinor",
                "--format",
                "text",
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        assert "retrieval_context_only" in text_proc.stdout
        assert "NOT verified Lean proof evidence" in text_proc.stdout

    # Guard must reject :8530 / :8540 / infogeometry before any network I/O
    for bad_args in (
        ["--endpoint", "http://127.0.0.1:8530", "--database", "alexandria"],
        ["--endpoint", "http://127.0.0.1:8540", "--database", "alexandria"],
        ["--endpoint", "http://127.0.0.1:8532", "--database", "infogeometry"],
    ):
        bad = subprocess.run(
            [sys.executable, str(TOOL), "--arango", *bad_args, "--query", "Clifford"],
            capture_output=True,
            text=True,
        )
        assert bad.returncode == 2
        assert "Traceback" not in bad.stderr

    # Unreachable endpoint exits non-zero cleanly
    unreach = subprocess.run(
        [
            sys.executable,
            str(TOOL),
            "--arango",
            "--endpoint",
            "http://127.0.0.1:59999",
            "--database",
            "alexandria_missing",
            "--query",
            "Clifford",
        ],
        capture_output=True,
        text=True,
        timeout=15,
    )
    assert unreach.returncode == 1
    assert "Traceback" not in unreach.stderr


def test_retrieve_jsonl_context_negative_top_k_raises_value_error(tmp_path: Path) -> None:
    import pytest

    write_jsonl(tmp_path / "alexandria_chunks.jsonl", [{"_key": "c1", "text": "Krein", "tokens": ["krein"]}])
    with pytest.raises(ValueError, match="top_k must be >= 0"):
        retrieve_jsonl_context(tmp_path, "Krein", top_k=-1)
    with pytest.raises(ValueError, match="top_k must be >= 0"):
        retrieve_arango_context("Krein", endpoint="http://127.0.0.1:8532", database="alexandria_unit_test", top_k=-1)


def test_retrieve_context_hops2_dag_neighbor_direction_and_aql_contract(tmp_path: Path) -> None:
    from tools.alexandria.retrieve_context import ARANGO_RETRIEVE_AQL

    # Verify ARANGO_RETRIEVE_AQL evaluates traversal edge direction against the reached vertex v._id, not start c._id
    dag_block = ARANGO_RETRIEVE_AQL.split("LET dagNeighbors = (", 1)[1]
    assert 'direction: e._to == v._id ? "outbound" : "inbound"' in dag_block
    assert 'e._from == c._id ? "outbound" : "inbound"' not in dag_block

    write_jsonl(
        tmp_path / "alexandria_documents.jsonl",
        [{"_key": "doc_1", "title": "Chain Paper", "path": "chain.pdf", "contentHash": "chain123"}],
    )
    write_jsonl(tmp_path / "alexandria_sections.jsonl", [])
    write_jsonl(
        tmp_path / "alexandria_chunks.jsonl",
        [
            {
                "_key": "c_def",
                "documentKey": "doc_1",
                "ordinal": 1,
                "chunkKind": "definition",
                "title": "Definition 1.1",
                "text": "Definition 1.1: Base algebraic space.",
                "tokens": ["definition", "base", "algebraic", "space"],
            },
            {
                "_key": "c_thm",
                "documentKey": "doc_1",
                "ordinal": 2,
                "chunkKind": "theorem",
                "title": "Theorem 2.1",
                "text": "Theorem 2.1: By Definition 1.1 and [1], the chain holds.",
                "tokens": ["theorem", "definition", "chain", "holds"],
            },
            {
                "_key": "c_prf",
                "documentKey": "doc_1",
                "ordinal": 3,
                "chunkKind": "proof",
                "title": "Proof of Theorem 2.1",
                "text": "Proof of Theorem 2.1 using xqzvhop2unit99.",
                "tokens": ["proof", "theorem", "using", "xqzvhop2unit99"],
            },
            {
                "_key": "c_lem",
                "documentKey": "doc_1",
                "ordinal": 4,
                "chunkKind": "theorem",
                "title": "Lemma 3.1",
                "text": "Lemma 3.1 citing [1] with xqzvlemunit99.",
                "tokens": ["lemma", "citing", "xqzvlemunit99"],
            },
        ],
    )
    write_jsonl(
        tmp_path / "alexandria_entities.jsonl",
        [{"_key": "ent_bib1", "documentKey": "doc_1", "entityType": "bib_entry", "surface": "[1]", "normalized": "ref_1"}],
    )
    write_jsonl(tmp_path / "alexandria_chunk_entity_edges.jsonl", [])
    write_jsonl(tmp_path / "alexandria_chunk_adjacent_edges.jsonl", [])
    write_jsonl(
        tmp_path / "alexandria_dag_edges.jsonl",
        [
            {
                "_key": "d_prf_thm",
                "_from": "alexandria_chunks/c_prf",
                "_to": "alexandria_chunks/c_thm",
                "edgeType": "proof_proves_theorem",
                "confidence": 0.95,
            },
            {
                "_key": "d_thm_def",
                "_from": "alexandria_chunks/c_thm",
                "_to": "alexandria_chunks/c_def",
                "edgeType": "chunk_uses_definition",
                "confidence": 0.9,
            },
            {
                "_key": "d_thm_bib",
                "_from": "alexandria_chunks/c_thm",
                "_to": "alexandria_entities/ent_bib1",
                "edgeType": "chunk_cites_entry",
                "confidence": 0.9,
            },
            {
                "_key": "d_lem_bib",
                "_from": "alexandria_chunks/c_lem",
                "_to": "alexandria_entities/ent_bib1",
                "edgeType": "chunk_cites_entry",
                "confidence": 0.9,
            },
        ],
    )

    pkt_prf = retrieve_jsonl_context(tmp_path, "xqzvhop2unit99", top_k=5, hops=2)
    assert len(pkt_prf["hits"]) == 1
    prf_dirs = {(n["_id"], n["edgeType"]): n["direction"] for n in pkt_prf["hits"][0]["dagNeighbors"]}
    assert prf_dirs == {
        ("alexandria_chunks/c_thm", "proof_proves_theorem"): "outbound",
        ("alexandria_chunks/c_def", "chunk_uses_definition"): "outbound",
        ("alexandria_entities/ent_bib1", "chunk_cites_entry"): "outbound",
    }

    pkt_lem = retrieve_jsonl_context(tmp_path, "xqzvlemunit99", top_k=5, hops=2)
    assert len(pkt_lem["hits"]) == 1
    lem_dirs = {(n["_id"], n["edgeType"]): n["direction"] for n in pkt_lem["hits"][0]["dagNeighbors"]}
    assert lem_dirs == {
        ("alexandria_entities/ent_bib1", "chunk_cites_entry"): "outbound",
        ("alexandria_chunks/c_thm", "chunk_cites_entry"): "inbound",
    }

    with _MockArangoServer([]) as srv:
        retrieve_arango_context(
            "xqzvhop2unit99",
            endpoint=srv.endpoint,
            database="alexandria_unit_test",
            username="root",
            password="",
            top_k=5,
            hops=2,
        )
        sent_query = srv.requests[0]["body"]["query"]
        sent_dag_block = sent_query.split("LET dagNeighbors = (", 1)[1]
        assert 'direction: e._to == v._id ? "outbound" : "inbound"' in sent_dag_block
        assert srv.requests[0]["body"]["bindVars"]["hops"] == 2
