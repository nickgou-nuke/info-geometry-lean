import json
from pathlib import Path

from tools.infra.blueprint_alexandria_bridge import build_nodes
from tools.infra.blueprint_arango_match import match_node
from tools.infra.paperproof_training_effects import rows_from_packet


def _jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row, ensure_ascii=True) + "\n" for row in rows), encoding="utf-8")


def test_blueprint_alexandria_bridge_builds_nodes_with_candidates(tmp_path: Path) -> None:
    input_dir = tmp_path / "alexandria"
    records = tmp_path / "records.jsonl"
    _jsonl(
        input_dir / "alexandria_chunks.jsonl",
        [
            {
                "_key": "chunk1",
                "chunkKind": "theorem",
                "title": "Projective normalization is scale invariant",
                "text": "The normalized projective count shape is invariant under positive scaling.",
                "provenance": {"path": "paper.md"},
            }
        ],
    )
    _jsonl(
        input_dir / "alexandria_entities.jsonl",
        [{"_key": "entity1", "entityType": "identifier", "surface": "normalizedShape", "normalized": "normalizedShape"}],
    )
    _jsonl(input_dir / "alexandria_chunk_entity_edges.jsonl", [{"_from": "chunks/chunk1", "_to": "entities/entity1"}])
    _jsonl(
        records,
        [
            {
                "schema": "info_geometry.leansearch_local.record.v1",
                "name": "Demo.normalizedShape_scale_counts",
                "kind": "theorem",
                "module": "Demo",
                "file": "lean/Demo.lean",
                "line": 3,
                "doc": "Scale invariance of normalized projective shapes.",
                "type": "normalizedShape counts = normalizedShape scaledCounts",
                "nameTokens": ["demo", "normalized", "shape", "scale", "counts"],
                "searchTokens": ["normalized", "shape", "scale", "projective", "counts", "invariant"],
            }
        ],
    )

    nodes = build_nodes(input_dir=input_dir, records=records, top_k=3, include_kinds={"theorem"}, max_nodes=None)

    assert nodes[0]["schema"] == "info_geometry.blueprint_alexandria_node.v1"
    assert nodes[0]["candidate_repo_decls"][0]["name"] == "Demo.normalizedShape_scale_counts"
    assert nodes[0]["authority"]["lean_remains_proof_authority"] is True


def test_blueprint_arango_match_recommends_apex_from_local_records(tmp_path: Path) -> None:
    records = tmp_path / "records.jsonl"
    _jsonl(
        records,
        [
            {
                "name": "Demo.projectiveGauge",
                "kind": "theorem",
                "module": "Demo",
                "file": "lean/Demo.lean",
                "line": 7,
                "doc": "Canonical projective gauge section.",
                "type": "Projective gauge theorem",
                "nameTokens": ["projective", "gauge"],
                "searchTokens": ["canonical", "projective", "gauge", "section"],
            }
        ],
    )
    node = {
        "id": "blueprint:test",
        "title": "Canonical projective gauge section",
        "kind": "theorem",
        "suggested_lean_name": "canonicalProjectiveGauge",
        "informal_statement": "The gauge section is canonical.",
        "entities": [{"normalized": "projective gauge"}],
    }

    match = match_node(node, records=records, top_k=1)

    assert match["recommended_apex"]["decl"] == "Demo.projectiveGauge"
    assert "arango_causal_chiral_cone_prompt.py" in match["next_step"]


def test_paperproof_training_effects_labels_tactic_steps() -> None:
    packet = {
        "source": "jixia",
        "theorem": "Demo.thm",
        "source_file": "lean/Demo.lean",
        "steps": [
            {
                "index": 0,
                "tactic": "constructor",
                "goals_before": [{"pp": "⊢ P ∧ Q"}],
                "goals_after": [{"pp": "⊢ P"}, {"pp": "⊢ Q"}],
                "hypotheses_before": [],
                "hypotheses_after": [],
            },
            {
                "index": 1,
                "tactic": "exact hp",
                "goals_before": [{"pp": "⊢ P"}],
                "goals_after": [],
                "hypotheses_before": [{"name": "hp", "type": "P"}],
                "hypotheses_after": [{"name": "hp", "type": "P"}],
            },
        ],
    }

    rows = rows_from_packet(packet)

    assert "splits_goal" in rows[0]["effect_labels"]
    assert "constructs_goal" in rows[0]["effect_labels"]
    assert "closes_goal" in rows[1]["effect_labels"]
    assert "uses_term_or_lemma" in rows[1]["effect_labels"]
