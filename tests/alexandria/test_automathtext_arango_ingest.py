from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools.alexandria.automathtext_arango_ingest import (
    DOCUMENT_COLLECTIONS,
    EDGE_COLLECTIONS,
    batched_jsonl,
    build_import_plan,
    import_automath_graph,
    validate_edge_endpoints,
)


def _jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8")


def test_build_import_plan_classifies_automath_collections(tmp_path: Path) -> None:
    _jsonl(tmp_path / "automath_fragments.jsonl", [{"_key": "frag"}])
    _jsonl(tmp_path / "automath_triples.jsonl", [{"_key": "edge", "_from": "automath_fragments/frag", "_to": "automath_chunks/chunk"}])

    plan = {row.collection: row for row in build_import_plan(tmp_path)}

    assert set(DOCUMENT_COLLECTIONS).issubset(plan)
    assert set(EDGE_COLLECTIONS).issubset(plan)
    assert plan["automath_fragments"].present is True
    assert plan["automath_fragments"].edge is False
    assert plan["automath_fragments"].count == 1
    assert plan["automath_triples"].present is True
    assert plan["automath_triples"].edge is True
    assert plan["automath_triples"].count == 1
    assert plan["automath_chunks"].present is False


def test_dry_run_writes_report_without_network(tmp_path: Path) -> None:
    _jsonl(tmp_path / "automath_fragments.jsonl", [{"_key": "frag", "ancestry_hash": "h"}])
    report_path = tmp_path / "report.json"

    report = import_automath_graph(
        input_dir=tmp_path,
        endpoint="http://127.0.0.1:1",
        database="alexandria_test",
        username="root",
        password="pw",
        dry_run=True,
        skip_indexes=False,
        require_all=False,
        json_out=report_path,
    )

    assert report["dry_run"] is True
    assert report["authority"] == "graph_context_only_not_proof_authority"
    assert any(row["collection"] == "automath_fragments" and row["count"] == 1 for row in report["collections"])
    assert report_path.exists()
    assert json.loads(report_path.read_text(encoding="utf-8"))["database"] == "alexandria_test"


def test_require_all_rejects_partial_graph(tmp_path: Path) -> None:
    _jsonl(tmp_path / "automath_fragments.jsonl", [{"_key": "frag"}])

    with pytest.raises(FileNotFoundError):
        import_automath_graph(
            input_dir=tmp_path,
            endpoint="http://127.0.0.1:1",
            database="alexandria_test",
            username="root",
            password="pw",
            dry_run=True,
            skip_indexes=False,
            require_all=True,
            json_out=None,
        )


def test_edge_endpoint_validation_is_strict() -> None:
    validate_edge_endpoints(
        [{"_key": "ok", "_from": "automath_chunks/a", "_to": "automath_entities/b"}],
        collection="automath_triples",
    )
    with pytest.raises(ValueError):
        validate_edge_endpoints([{"_key": "bad", "_from": "automath_chunks/a"}], collection="automath_triples")

def test_batched_jsonl_keeps_import_payloads_bounded(tmp_path: Path) -> None:
    path = tmp_path / "automath_triples.jsonl"
    _jsonl(
        path,
        [
            {"_key": f"edge-{idx}", "_from": "automath_chunks/a", "_to": "automath_entities/b"}
            for idx in range(5)
        ],
    )

    batches = list(batched_jsonl(path, batch_size=2))

    assert [len(batch) for batch in batches] == [2, 2, 1]
    assert batches[0][0]["_key"] == "edge-0"

