from __future__ import annotations

from typing import Any

from tools.alexandria.automathtext_arango_ingest import DOCUMENT_COLLECTIONS, EDGE_COLLECTIONS
from tools.alexandria.verify_automathtext_arango_descent import run_checks


def _count_runner(counts: dict[str, int], failures: dict[str, list[dict[str, Any]]] | None = None):
    failures = failures or {}

    def runner(query: str, bind_vars: dict[str, Any] | None = None) -> list[Any]:
        stripped = query.strip()
        if stripped.startswith("RETURN LENGTH("):
            collection = stripped.removeprefix("RETURN LENGTH(").removesuffix(")")
            return [counts.get(collection, 0)]
        for marker, rows in failures.items():
            if marker in query:
                return rows
        return []

    return runner


def test_run_checks_accepts_closed_automath_graph() -> None:
    counts = {collection: 1 for collection in DOCUMENT_COLLECTIONS + EDGE_COLLECTIONS}

    report = run_checks(_count_runner(counts))

    assert report["ok"] is True
    assert report["blocking_failure_count"] == 0
    assert report["authority"] == "provenance_retrieval_check_only_not_proof_authority"
    assert report["collection_counts"]["automath_fragments"] == 1
    assert "chunks_descend_to_fragments" in report["passed_checks"]


def test_run_checks_requires_raw_descent_collections_nonempty() -> None:
    counts = {collection: 0 for collection in DOCUMENT_COLLECTIONS + EDGE_COLLECTIONS}

    report = run_checks(_count_runner(counts))

    assert report["ok"] is False
    assert report["blocking_failure_count"] == 3
    names = {failure["name"] for failure in report["failures"]}
    assert "automath_fragments_nonempty" in names
    assert "automath_chunks_nonempty" in names
    assert "automath_ancestry_edges_nonempty" in names


def test_run_checks_reports_structural_orphan_failure() -> None:
    counts = {collection: 1 for collection in DOCUMENT_COLLECTIONS + EDGE_COLLECTIONS}
    failures = {
        "FOR e IN automath_triples": [
            {
                "edge": {"_key": "bad", "_from": "automath_chunks/missing", "_to": "automath_entities/e"},
                "missingFrom": True,
                "missingTo": False,
            }
        ]
    }

    report = run_checks(_count_runner(counts, failures))

    assert report["ok"] is False
    failed = {failure["name"]: failure for failure in report["failures"]}
    assert "automath_triples_endpoints_resolve" in failed
    assert failed["automath_triples_endpoints_resolve"]["sample_count"] == 1


def test_run_checks_reports_missing_theorem_shape_descent() -> None:
    counts = {collection: 1 for collection in DOCUMENT_COLLECTIONS + EDGE_COLLECTIONS}
    failures = {
        "FOR s IN automath_theorem_shapes": [
            {
                "theoremShape": {"_key": "shape_bad", "source_chunk": "missing"},
                "missingChunk": True,
                "missingFragment": False,
                "missingAncestryEdge": True,
            }
        ]
    }

    report = run_checks(_count_runner(counts, failures))

    assert report["ok"] is False
    names = {failure["name"] for failure in report["failures"]}
    assert "theorem_shapes_descend_to_chunks_and_fragments" in names
