from __future__ import annotations

import json
from pathlib import Path

from tools.alexandria.materialize_coarse_scc_overlay import materialize


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("".join(json.dumps(row) + "\n" for row in rows), encoding="utf-8")


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def test_materialize_coarse_scc_overlay_preserves_member_descent(tmp_path: Path) -> None:
    write_jsonl(
        tmp_path / "alexandria_chunks.jsonl",
        [
            {"_key": "chunk_a", "text": "A", "tokens": ["krein"], "ancestry_path": ["frag", "a"]},
            {"_key": "chunk_b", "text": "B", "tokens": ["drazin"], "ancestry_path": ["frag", "b"]},
        ],
    )
    write_jsonl(
        tmp_path / "alexandria_entities.jsonl",
        [{"_key": "ent_krein", "normalized": "Krein space", "entityType": "concept", "confidence": 1.0}],
    )
    write_jsonl(
        tmp_path / "alexandria_chunk_entity_edges.jsonl",
        [
            {"_from": "alexandria_chunks/chunk_a", "_to": "alexandria_entities/ent_krein"},
            {"_from": "alexandria_chunks/chunk_b", "_to": "alexandria_entities/ent_krein"},
        ],
    )
    write_jsonl(tmp_path / "alexandria_chunk_adjacent_edges.jsonl", [])
    write_jsonl(
        tmp_path / "automath_debruijn_edges.jsonl",
        [
            {"_from": "alexandria_chunks/chunk_a", "_to": "alexandria_chunks/chunk_b", "weight": 1.0, "overlap_symbols": ["Krein space"]},
            {"_from": "alexandria_chunks/chunk_b", "_to": "alexandria_chunks/chunk_a", "weight": 1.0, "overlap_symbols": ["Krein space"]},
        ],
    )
    write_jsonl(tmp_path / "alexandria_entity_relation_edges.jsonl", [])

    summary = materialize(tmp_path, tmp_path / "coarse", query="Krein", conductive=True)

    assert summary["counts"]["coarse_scc_nodes"] == 1
    nodes = read_jsonl(tmp_path / "coarse" / "alexandria_coarse_scc_nodes.jsonl")
    members = read_jsonl(tmp_path / "coarse" / "alexandria_coarse_scc_membership_edges.jsonl")
    assert nodes[0]["memberCount"] == 2
    assert "Krein space" in nodes[0]["representativeTerms"]
    assert {edge["_to"] for edge in members} == {"alexandria_chunks/chunk_a", "alexandria_chunks/chunk_b"}
