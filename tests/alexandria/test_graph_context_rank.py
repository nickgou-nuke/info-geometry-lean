from __future__ import annotations

import json
import subprocess
import sys
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any

import networkx as nx

from tools.alexandria.graph_context_rank import (
    activated_edges,
    build_graph,
    coarse_components,
    personalized_scores,
    query_abstraction_score,
    scc_quotient_scores,
    tokenize,
)

REPO = Path(__file__).resolve().parents[2]
TOOL = REPO / "tools" / "alexandria" / "graph_context_rank.py"


class _MockRankArangoServer:
    def __init__(self, seed_rows: list[dict[str, Any]], subgraph_row: dict[str, Any]) -> None:
        self.seed_rows = seed_rows
        self.subgraph_row = subgraph_row
        self.requests: list[dict[str, Any]] = []
        outer = self

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, format: str, *args: object) -> None:  # noqa: A003
                return

            def do_POST(self) -> None:  # noqa: N802
                length = int(self.headers.get("Content-Length", "0"))
                body = json.loads(self.rfile.read(length).decode("utf-8")) if length else {}
                outer.requests.append({"path": self.path, "body": body})
                q = str(body.get("query", ""))
                result = outer.seed_rows if "alexandria_chunks_search" in q else [outer.subgraph_row]
                payload = {
                    "error": False,
                    "hasMore": False,
                    "extra": {"warnings": []},
                    "result": result,
                }
                raw = json.dumps(payload).encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(raw)))
                self.end_headers()
                self.wfile.write(raw)

        self._server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.endpoint = f"http://127.0.0.1:{self._server.server_port}"
        self._thread = threading.Thread(target=self._server.serve_forever, daemon=True)

    def __enter__(self) -> "_MockRankArangoServer":
        self._thread.start()
        return self

    def __exit__(self, *_: object) -> None:
        self._server.shutdown()
        self._server.server_close()


def test_conductive_debruijn_edges_gain_query_aligned_weight() -> None:
    chunks = [
        {"_key": "chunk_a", "tokens": ["krein", "projection"]},
        {"_key": "chunk_b", "tokens": ["j", "self", "adjoint"]},
        {"_key": "chunk_c", "tokens": ["banach", "space"]},
    ]
    debruijn_edges = [
        {
            "_from": "alexandria_chunks/chunk_a",
            "_to": "alexandria_chunks/chunk_b",
            "transition_probability": 0.45,
            "overlap_symbols": ["Krein space", "projection"],
            "direction": "semantic_sequence_overlap",
        },
        {
            "_from": "alexandria_chunks/chunk_a",
            "_to": "alexandria_chunks/chunk_c",
            "transition_probability": 0.45,
            "overlap_symbols": ["Banach space"],
            "direction": "semantic_sequence_overlap",
        },
    ]

    graph = build_graph(
        nx,
        chunks,
        [],
        [],
        [],
        debruijn_edges,
        [],
        query_tokens=tokenize("Krein projection"),
        conductive=True,
    )

    assert graph["chunk_a"]["chunk_b"]["kind"] == "debruijn_sequence"
    assert graph["chunk_a"]["chunk_b"]["conductivity"] > graph["chunk_a"]["chunk_c"]["conductivity"]
    assert graph["chunk_a"]["chunk_b"]["weight"] > graph["chunk_a"]["chunk_c"]["weight"]
    active = activated_edges(graph, {chunk["_key"]: chunk for chunk in chunks}, limit=1)
    assert active[0]["to"] == "chunk_b"
    assert active[0]["overlap_symbols"] == ["Krein space", "projection"]


def test_coarse_components_group_connected_context_by_entities() -> None:
    chunks = [
        {"_key": "chunk_a", "tokens": ["krein", "operator"], "chunkKind": "definition", "text": "Definition. Krein operator."},
        {"_key": "chunk_b", "tokens": ["krein", "projection"], "chunkKind": "theorem", "text": "Theorem. Krein projection."},
    ]
    graph = build_graph(
        nx,
        chunks,
        [{"_key": "ent_krein", "normalized": "Krein space", "entityType": "concept", "confidence": 1.0}],
        [
            {"_from": "alexandria_chunks/chunk_a", "_to": "alexandria_entities/ent_krein"},
            {"_from": "alexandria_chunks/chunk_b", "_to": "alexandria_entities/ent_krein"},
        ],
        [],
        [],
        [],
        query_tokens=tokenize("Krein operator theory"),
        conductive=True,
    )
    entities_for_chunk = {
        "chunk_a": [{"normalized": "Krein space"}],
        "chunk_b": [{"normalized": "Krein space"}],
    }
    components = coarse_components(
        nx,
        graph,
        chunks,
        entities_for_chunk,
        {"chunk_a": 0.3, "chunk_b": 0.4},
        tokenize("Krein operator theory"),
    )

    assert query_abstraction_score(tokenize("Krein operator theory")) >= 0.5
    assert components[0]["memberCount"] == 2
    assert "Krein space" in components[0]["representativeTerms"]


def test_scc_quotient_scores_distribute_component_score_to_cycle_members() -> None:
    graph = nx.DiGraph()
    graph.add_edge("a", "b", weight=1.0)
    graph.add_edge("b", "a", weight=1.0)
    graph.add_edge("b", "c", weight=0.5)

    scores, quotient = scc_quotient_scores(nx, graph, {"a": 1.0})

    cycle = next(row for row in quotient if set(row["members"]) == {"a", "b"})
    assert cycle["internalCycle"] is True
    assert scores["a"] == scores["b"]
    assert scores["a"] > 0


def test_build_graph_dag_edges_bidirectional_flow() -> None:
    chunks = [
        {"_key": "thm_1", "tokens": ["drazin", "inverse", "peirce"], "chunkKind": "theorem"},
        {"_key": "prf_1", "tokens": ["proof", "projector"], "chunkKind": "proof"},
    ]
    dag_edges = [
        {
            "_from": "alexandria_chunks/prf_1",
            "_to": "alexandria_chunks/thm_1",
            "edgeType": "proof_proves_theorem",
            "confidence": 0.9,
        }
    ]
    graph = build_graph(nx, chunks, [], [], [], [], [], dag_edges=dag_edges)
    assert graph["prf_1"]["thm_1"]["kind"] == "dag:proof_proves_theorem"
    assert graph["thm_1"]["prf_1"]["kind"] == "dag_reverse:proof_proves_theorem"
    assert abs(graph["thm_1"]["prf_1"]["weight"] - 0.675) < 1e-6

    pr = personalized_scores(graph, {"thm_1": 1.0})
    assert pr["prf_1"] > 0.0


def test_graph_context_rank_cli_arango_mock_and_guards(tmp_path: Path) -> None:
    missing = subprocess.run(
        [sys.executable, str(TOOL), "--input-dir", str(tmp_path / "missing"), "--query", "Peirce"],
        capture_output=True,
        text=True,
    )
    assert missing.returncode != 0

    bad_k = subprocess.run(
        [sys.executable, str(TOOL), "--input-dir", str(tmp_path), "--query", "Peirce", "--top-k", "-1"],
        capture_output=True,
        text=True,
    )
    assert bad_k.returncode == 2

    bad_guard = subprocess.run(
        [
            sys.executable,
            str(TOOL),
            "--arango",
            "--endpoint",
            "http://127.0.0.1:8530",
            "--database",
            "infogeometry",
            "--query",
            "Peirce",
        ],
        capture_output=True,
        text=True,
    )
    assert bad_guard.returncode == 2

    seed_rows = [
        {
            "chunk": {
                "_key": "thm_peirce",
                "_id": "alexandria_chunks/thm_peirce",
                "documentKey": "doc_peirce",
                "chunkKind": "theorem",
                "title": "Peirce Drazin Inverse",
                "text": "The Drazin inverse decomposes via Peirce orthogonal projections.",
                "tokens": ["drazin", "inverse", "peirce", "projections"],
                "provenance": {"path": "/corpus/peirce.pdf", "contentHash": "hash_p", "pageStart": 2},
            },
            "bm25Score": 7.5,
            "adj": [],
            "dag": [
                {
                    "edge": {
                        "_key": "dag_p1",
                        "_from": "alexandria_chunks/prf_peirce",
                        "_to": "alexandria_chunks/thm_peirce",
                        "edgeType": "proof_proves_theorem",
                        "confidence": 0.9,
                    },
                    "node": {
                        "_key": "prf_peirce",
                        "_id": "alexandria_chunks/prf_peirce",
                        "documentKey": "doc_peirce",
                        "chunkKind": "proof",
                        "title": "Proof of Peirce Drazin",
                        "text": "Proof using idempotent decomposition.",
                        "tokens": ["proof", "idempotent", "decomposition"],
                        "provenance": {"path": "/corpus/peirce.pdf", "contentHash": "hash_p", "pageStart": 3},
                    },
                }
            ],
        }
    ]
    subgraph_row = {
        "chunkEntities": [
            {
                "edge": {"_from": "alexandria_chunks/thm_peirce", "_to": "alexandria_entities/ent_1"},
                "entity": {"_key": "ent_1", "entityType": "concept", "surface": "Drazin inverse", "normalized": "drazin inverse", "confidence": 0.9},
            }
        ],
        "entityRelations": [],
        "documents": [{"_key": "doc_peirce", "title": "Peirce Drazin Paper", "path": "/corpus/peirce.pdf", "contentHash": "hash_p"}],
    }

    with _MockRankArangoServer(seed_rows, subgraph_row) as srv:
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
                "Peirce Drazin inverse",
                "--top-k",
                "4",
            ],
            capture_output=True,
            text=True,
            check=True,
        )
        packet = json.loads(proc.stdout)
        assert packet["authority"] == "retrieval_context_only"
        assert packet["mode"] == "arango"
        assert packet["graph"]["nodeCount"] == 2
        assert packet["seeds"][0]["chunkKey"] == "thm_peirce"
        assert len(packet["hits"]) == 2
        assert packet["hits"][0]["graphScore"] > 0
        assert "lexicalScore" in packet["hits"][0]
        assert packet["hits"][0]["dagNeighbors"]
        # BUG-02: non-seed PPR-promoted proof hit also has dagNeighbors
        proof_hit = next(h for h in packet["hits"] if h["chunkKey"] == "prf_peirce")
        assert proof_hit["dagNeighbors"]
        assert proof_hit["dagNeighbors"][0]["direction"] == "outbound"


def test_rank_jsonl_context_seed_k_zero_and_negative_bounds(tmp_path: Path) -> None:
    import pytest

    from tools.alexandria.graph_context_rank import rank_jsonl_context

    for name in (
        "alexandria_documents",
        "alexandria_entities",
        "alexandria_chunk_entity_edges",
        "alexandria_chunk_adjacent_edges",
        "alexandria_entity_relation_edges",
        "alexandria_debruijn_edges",
        "alexandria_dag_edges",
    ):
        (tmp_path / f"{name}.jsonl").write_text("", encoding="utf-8")
    (tmp_path / "alexandria_chunks.jsonl").write_text(
        json.dumps({"_key": "c1", "title": "Peirce", "text": "Peirce projection", "tokens": ["peirce", "projection"]}) + "\n",
        encoding="utf-8",
    )

    pkt = rank_jsonl_context(nx, tmp_path, "Peirce projection", top_k=5, seed_k=0)
    assert pkt["seeds"] == []
    assert pkt["hits"] == []

    with pytest.raises(ValueError, match="top_k must be >= 0"):
        rank_jsonl_context(nx, tmp_path, "Peirce", top_k=-1)
    with pytest.raises(ValueError, match="seed_k must be >= 0"):
        rank_jsonl_context(nx, tmp_path, "Peirce", seed_k=-1)


def test_rank_arango_context_hops2_no_bogus_chunk_to_chunk_dag_neighbors() -> None:
    from tools.alexandria.graph_context_rank import rank_arango_context

    thm_chunk = {
        "_key": "thm_1",
        "_id": "alexandria_chunks/thm_1",
        "documentKey": "doc_1",
        "chunkKind": "theorem",
        "title": "Theorem 1.1",
        "text": "Theorem 1.1 (XQZVSHARED): Operator cites [1].",
        "tokens": ["theorem", "xqzvshared", "operator", "cites"],
        "provenance": {"path": "/corpus/shared.pdf", "contentHash": "hash_s", "pageStart": 1},
    }
    lem_chunk = {
        "_key": "lem_2",
        "_id": "alexandria_chunks/lem_2",
        "documentKey": "doc_1",
        "chunkKind": "theorem",
        "title": "Lemma 2.1",
        "text": "Lemma 2.1: Auxiliary orthogonal result citing [1] and Theorem 1.1.",
        "tokens": ["lemma", "auxiliary", "orthogonal", "result"],
        "provenance": {"path": "/corpus/shared.pdf", "contentHash": "hash_s", "pageStart": 2},
    }
    prf_chunk = {
        "_key": "prf_2",
        "_id": "alexandria_chunks/prf_2",
        "documentKey": "doc_1",
        "chunkKind": "proof",
        "title": "Proof of Lemma 2.1",
        "text": "Proof of Lemma 2.1. Direct check. QED.",
        "tokens": ["proof", "direct", "check"],
        "provenance": {"path": "/corpus/shared.pdf", "contentHash": "hash_s", "pageStart": 2},
    }
    bib_entity = {
        "_key": "ent_bib1",
        "_id": "alexandria_entities/ent_bib1",
        "documentKey": "doc_1",
        "entityType": "bib_entry",
        "surface": "[1]",
        "normalized": "ref_1",
        "confidence": 0.9,
    }

    seed_rows = [
        {
            "chunk": thm_chunk,
            "bm25Score": 8.0,
            "adj": [],
            "dag": [
                {
                    "edge": {
                        "_key": "dag_cite_thm",
                        "_from": "alexandria_chunks/thm_1",
                        "_to": "alexandria_entities/ent_bib1",
                        "edgeType": "chunk_cites_entry",
                        "confidence": 0.9,
                    },
                    "node": bib_entity,
                },
                {
                    "edge": {
                        "_key": "dag_cite_lem",
                        "_from": "alexandria_chunks/lem_2",
                        "_to": "alexandria_entities/ent_bib1",
                        "edgeType": "chunk_cites_entry",
                        "confidence": 0.9,
                    },
                    "node": lem_chunk,
                },
                {
                    "edge": {
                        "_key": "dag_ref_lem_thm",
                        "_from": "alexandria_chunks/lem_2",
                        "_to": "alexandria_chunks/thm_1",
                        "edgeType": "chunk_references_result",
                        "confidence": 0.9,
                    },
                    "node": lem_chunk,
                },
                {
                    "edge": {
                        "_key": "dag_prf_lem",
                        "_from": "alexandria_chunks/prf_2",
                        "_to": "alexandria_chunks/lem_2",
                        "edgeType": "proof_proves_theorem",
                        "confidence": 0.9,
                    },
                    "node": prf_chunk,
                },
            ],
        }
    ]
    subgraph_row = {
        "chunkEntities": [
            {
                "edge": {"_from": "alexandria_chunks/thm_1", "_to": "alexandria_entities/ent_bib1"},
                "entity": bib_entity,
            },
            {
                "edge": {"_from": "alexandria_chunks/lem_2", "_to": "alexandria_entities/ent_bib1"},
                "entity": bib_entity,
            },
        ],
        "entityRelations": [],
        "documents": [{"_key": "doc_1", "title": "Shared Bib Paper", "path": "/corpus/shared.pdf", "contentHash": "hash_s"}],
    }

    with _MockRankArangoServer(seed_rows, subgraph_row) as srv:
        pkt = rank_arango_context(
            nx,
            "xqzvshared",
            endpoint=srv.endpoint,
            database="alexandria_unit_test",
            username="root",
            password="",
            top_k=10,
            seed_k=5,
            hops=2,
        )

    by_key = {h["chunkKey"]: h for h in pkt["hits"]}
    assert {"thm_1", "lem_2", "prf_2"}.issubset(by_key.keys())

    # thm_1 has genuine 1-hop entity chunk_cites_entry and 1-hop lem_2 reference, NEVER bogus chunk-to-chunk chunk_cites_entry or 2-hop prf_2
    thm_dag = by_key["thm_1"]["dagNeighbors"]
    assert any(n["_id"] == "alexandria_entities/ent_bib1" and n["edgeType"] == "chunk_cites_entry" and n["direction"] == "outbound" for n in thm_dag)
    assert any(n["_id"] == "alexandria_chunks/lem_2" and n["edgeType"] == "chunk_references_result" and n["direction"] == "inbound" for n in thm_dag)
    assert not any(n["edgeType"] == "chunk_cites_entry" and str(n.get("_id", "")).startswith("alexandria_chunks/") for n in thm_dag)
    assert not any(n["_id"] == "alexandria_chunks/prf_2" for n in thm_dag)

    # lem_2 does NOT have bogus thm_1 chunk_cites_entry, and retains genuine 2-hop chunk-to-chunk neighbors
    lem_dag = by_key["lem_2"]["dagNeighbors"]
    assert not any(n["edgeType"] == "chunk_cites_entry" and str(n.get("_id", "")).startswith("alexandria_chunks/") for n in lem_dag)
    assert any(n["_id"] == "alexandria_chunks/thm_1" and n["edgeType"] == "chunk_references_result" and n["direction"] == "outbound" for n in lem_dag)
    assert any(n["_id"] == "alexandria_chunks/prf_2" and n["edgeType"] == "proof_proves_theorem" and n["direction"] == "inbound" for n in lem_dag)

    # prf_2 has genuine 2-hop proof_proves_theorem -> lem_2, NEVER thm_1
    prf_dag = by_key["prf_2"]["dagNeighbors"]
    assert any(n["_id"] == "alexandria_chunks/lem_2" and n["edgeType"] == "proof_proves_theorem" and n["direction"] == "outbound" for n in prf_dag)
    assert not any(n["_id"] == "alexandria_chunks/thm_1" for n in prf_dag)
