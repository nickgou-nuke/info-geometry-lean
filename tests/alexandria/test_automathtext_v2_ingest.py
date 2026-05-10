from __future__ import annotations

import json
import gzip
from pathlib import Path

from tools.alexandria.automathtext_v2_ingest import build_outputs


def _jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8")


def _read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def test_automathtext_ingest_emits_triples_and_debruijn_edges(tmp_path: Path) -> None:
    source = tmp_path / "math_web" / "90-100" / "sample.jsonl"
    _jsonl(
        source,
        [
            {
                "id": "krein-1",
                "meta": json.dumps({"domain": "math_web", "source": "unit"}),
                "text": "Theorem. For all x in a Krein space, if A is J-self-adjoint then the projection P has closed range. Proof. Hence x lies in the range of A.",
                "tokens": 31,
                "score": 0.99,
                "url": "https://example.invalid/krein",
            }
        ],
    )
    out = tmp_path / "out"
    summary = build_outputs(
        input_paths=[source],
        output_dir=out,
        dataset="OpenSQZ/AutoMathText-V2",
        run_id="test-run",
        max_rows=None,
        max_chars=500,
        overlap_chars=0,
        entity_term=[],
    )

    assert summary["counts"]["fragments"] == 1
    assert summary["counts"]["chunks"] == 1
    assert summary["counts"]["triples"] >= 3
    assert summary["counts"]["expr_edges"] >= 1
    assert summary["counts"]["theorem_shapes"] >= 1
    assert summary["counts"]["ancestry_edges"] >= 2
    assert summary["alexandria_counts"]["documents"] == 1
    assert summary["alexandria_counts"]["chunks"] == 1
    assert summary["alexandria_counts"]["chunk_entity_edges"] >= 1
    assert (out / "automathtext_ingest_summary.json").exists()

    fragments = _read_jsonl(out / "automath_fragments.jsonl")
    chunks = _read_jsonl(out / "automath_chunks.jsonl")
    ancestry_edges = _read_jsonl(out / "automath_ancestry_edges.jsonl")
    assert fragments[0]["_key"] == fragments[0]["key"]
    assert fragments[0]["ancestry_hash"]
    assert fragments[0]["ancestry_path"] == [fragments[0]["ancestry_hash"]]
    assert fragments[0]["parent_ancestry_hash"] is None
    assert chunks[0]["parent_ancestry_hash"] == fragments[0]["ancestry_hash"]
    assert any(row["role"] == "fragment_to_chunk" for row in ancestry_edges)

    triples = _read_jsonl(out / "automath_triples.jsonl")
    assert any(row["predicate"] == "mentions" for row in triples)
    assert any(row["predicate"] == "has_theorem_shape" for row in triples)

    entities = _read_jsonl(out / "automath_entities.jsonl")
    normalized = {row["normalized"] for row in entities}
    assert "krein space" in normalized
    assert "j-self-adjoint" in normalized
    assert "closed range" in normalized

    expr_edges = _read_jsonl(out / "automath_expr_edges.jsonl")
    assert any(row["predicate"] == "bound_by" and row["deBruijnIdx"] == 0 for row in expr_edges)

    shapes = _read_jsonl(out / "automath_theorem_shapes.jsonl")
    assert shapes[0]["authority"] == "theorem_shape_candidate"
    assert shapes[0]["debruijn_histogram"]
    assert shapes[0]["parent_ancestry_hash"] == chunks[0]["ancestry_hash"]


def test_automathtext_ingest_preserves_raw_authority_boundary(tmp_path: Path) -> None:
    source = tmp_path / "sample.jsonl"
    _jsonl(source, [{"id": "drazin", "text": "Definition. A Drazin inverse is an operator satisfying algebraic equations."}])
    out = tmp_path / "out"
    summary = build_outputs(
        input_paths=[source],
        output_dir=out,
        dataset="OpenSQZ/AutoMathText-V2",
        run_id="boundary-run",
        max_rows=1,
        max_chars=500,
        overlap_chars=0,
        entity_term=[],
    )
    assert summary["authority"] == {
        "graph_context_only": True,
        "lean_remains_proof_authority": True,
        "not_a_proof": True,
    }
    chunks = _read_jsonl(out / "automath_chunks.jsonl")
    assert chunks[0]["authority"] == "raw_text_context_only"
    shapes = _read_jsonl(out / "automath_theorem_shapes.jsonl")
    assert shapes[0]["authority"] == "theorem_shape_candidate"

def test_automathtext_ingest_deep_dag_rows_have_chain_of_custody(tmp_path: Path) -> None:
    source = tmp_path / "sample.jsonl"
    _jsonl(
        source,
        [
            {
                "id": "chain",
                "parent_id": "hf://OpenSQZ/AutoMathText-V2/math_web/90-100/train-00000.parquet:42",
                "meta": json.dumps({"domain": "math_web", "source": "unit", "parent": "ignored-parent"}),
                "text": "Lemma. For all x, a Moore-Penrose projection has range equal to a star projection.",
            }
        ],
    )
    out = tmp_path / "out"
    build_outputs(
        input_paths=[source],
        output_dir=out,
        dataset="OpenSQZ/AutoMathText-V2",
        run_id="ancestry-run",
        max_rows=1,
        max_chars=500,
        overlap_chars=0,
        entity_term=[],
    )

    for filename in [
        "automath_fragments.jsonl",
        "automath_chunks.jsonl",
        "automath_entities.jsonl",
        "automath_triples.jsonl",
        "automath_expr_nodes.jsonl",
        "automath_expr_edges.jsonl",
        "automath_theorem_shapes.jsonl",
        "automath_ancestry_edges.jsonl",
        "automath_overlay_nodes.jsonl",
        "automath_overlay_edges.jsonl",
    ]:
        rows = _read_jsonl(out / filename)
        assert rows, filename
        for row in rows:
            assert row["ancestry_hash"], (filename, row)
            assert row["ancestry_path"], (filename, row)
            assert row["ancestry_path"][-1] == row["ancestry_hash"], (filename, row)

    fragment = _read_jsonl(out / "automath_fragments.jsonl")[0]
    chunk = _read_jsonl(out / "automath_chunks.jsonl")[0]
    shape = _read_jsonl(out / "automath_theorem_shapes.jsonl")[0]
    assert fragment["parent_id"] == "hf://OpenSQZ/AutoMathText-V2/math_web/90-100/train-00000.parquet:42"
    assert shape["ancestry_path"][:2] == [fragment["ancestry_hash"], chunk["ancestry_hash"]]
    assert shape["parent_ancestry_hash"] == chunk["ancestry_hash"]


def test_automathtext_sharded_ingest_writes_bounded_retrieval_only_shards(tmp_path: Path) -> None:
    source = tmp_path / "sample.jsonl"
    _jsonl(
        source,
        [
            {
                "id": f"row-{idx}",
                "meta": json.dumps({"domain": "math_web", "source": "unit"}),
                "text": f"Theorem. For all x, Drazin projection row {idx} has closed range. Proof. Hence x lies in range.",
            }
            for idx in range(5)
        ],
    )
    out = tmp_path / "sharded"

    from tools.alexandria.automathtext_v2_ingest import build_sharded_outputs

    summary = build_sharded_outputs(
        input_paths=[source],
        output_dir=out,
        dataset="OpenSQZ/AutoMathText-V2",
        run_id="sharded-run",
        max_rows=None,
        max_chars=500,
        overlap_chars=0,
        entity_term=[],
        shard_rows=2,
    )

    assert summary["schema"] == "info_geometry.automathtext_v2.sharded_ingest_summary.v1"
    assert summary["counts"]["source_rows"] == 5
    assert summary["counts"]["shards"] == 3
    assert summary["authority"] == {
        "graph_context_only": True,
        "lean_remains_proof_authority": True,
        "not_a_proof": True,
    }
    shard_dirs = sorted((out / "shards").glob("shard_*"))
    assert [p.name for p in shard_dirs] == ["shard_000000", "shard_000001", "shard_000002"]
    assert [_read_jsonl(p / "automath_fragments.jsonl") for p in shard_dirs]
    assert [json.loads((p / "summary.json").read_text())["counts"]["fragments"] for p in shard_dirs] == [2, 2, 1]
    first_fragment = _read_jsonl(shard_dirs[0] / "automath_fragments.jsonl")[0]
    assert first_fragment["source_file"].endswith("sample.jsonl")
    assert first_fragment["authority"] == "raw_text_context_only"
    top_summary = json.loads((out / "summary.json").read_text())
    assert top_summary["counts"]["fragments"] == 5


def test_automathtext_filtered_gzip_shards_keep_operator_theorem_rows(tmp_path: Path) -> None:
    source = tmp_path / "sample.jsonl"
    _jsonl(
        source,
        [
            {
                "id": "keep-operator-theorem",
                "text": "Theorem. A Moore-Penrose projection has closed range and is self-adjoint.",
            },
            {
                "id": "reject-operator-no-marker",
                "text": "A Drazin inverse appears in ordinary explanatory prose.",
            },
            {
                "id": "reject-marker-no-operator",
                "text": "Theorem. Every triangle has three sides.",
            },
            {
                "id": "keep-krein-lemma",
                "text": "Lemma. A Krein space with a J-self-adjoint bounded operator has a projection context.",
            },
        ],
    )
    out = tmp_path / "filtered-gzip"

    from tools.alexandria.automathtext_v2_ingest import build_sharded_outputs

    summary = build_sharded_outputs(
        input_paths=[source],
        output_dir=out,
        dataset="OpenSQZ/AutoMathText-V2",
        run_id="filtered-gzip-run",
        max_rows=None,
        max_chars=500,
        overlap_chars=0,
        entity_term=[],
        shard_rows=2,
        filter_operator_corridor=True,
        require_theorem_marker=True,
        gzip_output=True,
    )

    assert summary["counts"]["source_rows"] == 4
    assert summary["counts"]["kept_rows"] == 2
    assert summary["counts"]["rejected_rows"] == 2
    assert summary["counts"]["shards"] == 1
    assert summary["filter"]["operator_corridor"] is True
    assert summary["filter"]["require_theorem_marker"] is True
    assert summary["output"]["gzip"] is True
    assert summary["filter"]["term_hits"]["moore-penrose"] == 1
    assert summary["filter"]["term_hits"]["krein"] == 1
    shard = out / "shards" / "shard_000000"
    assert (shard / "automath_fragments.jsonl.gz").exists()
    assert not (shard / "automath_fragments.jsonl").exists()
    with gzip.open(shard / "automath_fragments.jsonl.gz", "rt", encoding="utf-8") as handle:
        fragments = [json.loads(line) for line in handle if line.strip()]
    assert [row["source_id"] for row in fragments] == ["keep-operator-theorem", "keep-krein-lemma"]
    assert all(row["authority"] == "raw_text_context_only" for row in fragments)

def test_automathtext_ingest_emits_alexandria_ranker_interface(tmp_path: Path) -> None:
    source = tmp_path / "sample.jsonl"
    _jsonl(
        source,
        [
            {
                "id": "ranker-1",
                "meta": json.dumps({"domain": "math_web", "source": "unit"}),
                "text": "Definition. A Krein space has a fundamental symmetry J.\n\nLemma. If P is J-self-adjoint and P is a projection, then P is a J-projection with closed range.",
                "score": 0.9,
            }
        ],
    )
    out = tmp_path / "ranker-out"
    build_outputs(
        input_paths=[source],
        output_dir=out,
        dataset="OpenSQZ/AutoMathText-V2",
        run_id="ranker-run",
        max_rows=1,
        max_chars=90,
        overlap_chars=0,
        entity_term=[],
    )

    expected = [
        "alexandria_documents.jsonl",
        "alexandria_sections.jsonl",
        "alexandria_chunks.jsonl",
        "alexandria_entities.jsonl",
        "alexandria_document_section_edges.jsonl",
        "alexandria_section_chunk_edges.jsonl",
        "alexandria_chunk_entity_edges.jsonl",
        "alexandria_chunk_adjacent_edges.jsonl",
        "alexandria_entity_relation_edges.jsonl",
        "automath_debruijn_edges.jsonl",
        "automathtext_ingest_summary.json",
    ]
    for filename in expected:
        assert (out / filename).exists(), filename

    alex_chunks = _read_jsonl(out / "alexandria_chunks.jsonl")
    assert len(alex_chunks) >= 2
    assert all(row["_key"].startswith("chunk_") for row in alex_chunks)
    assert all(isinstance(row["tokens"], list) and row["tokens"] for row in alex_chunks)
    assert all(row["authority"] == "raw_text_context_only" for row in alex_chunks)
    assert alex_chunks[0]["provenance"]["sourceDataset"] == "OpenSQZ/AutoMathText-V2"

    chunk_entity_edges = _read_jsonl(out / "alexandria_chunk_entity_edges.jsonl")
    assert chunk_entity_edges
    assert all(row["_from"].startswith("alexandria_chunks/") for row in chunk_entity_edges)
    assert all(row["_to"].startswith("alexandria_entities/") for row in chunk_entity_edges)

    adjacent = _read_jsonl(out / "alexandria_chunk_adjacent_edges.jsonl")
    debruijn = _read_jsonl(out / "automath_debruijn_edges.jsonl")
    assert adjacent
    assert debruijn
    assert debruijn[0]["edgeKind"] == "debruijn_sequence"
    assert debruijn[0]["_from"].startswith("alexandria_chunks/")

    relations = _read_jsonl(out / "alexandria_entity_relation_edges.jsonl")
    assert any(row["relationType"] == "implies_candidate" for row in relations)

