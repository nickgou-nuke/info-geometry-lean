import json
from pathlib import Path

from tools.infra.paperproof_bidirectional_cone import build_bidirectional_cone


def test_build_bidirectional_cone_glues_forward_forest_to_backward_cone() -> None:
    forest = {
        "id": "forest:demo",
        "source_file": "lean/Demo.lean",
        "nodes": [
            {"id": "proof:demo", "kind": "proof", "source_file": "lean/Demo.lean"},
            {"id": "goal:g0", "kind": "goal", "text": "⊢ True"},
            {"id": "tactic:t0", "kind": "tactic", "text": "exact Demo.trivial", "references": ["Demo.trivial"]},
            {"id": "ref:r0", "kind": "reference", "text": "Demo.trivial"},
            {"id": "closed:c0", "kind": "closed_goal", "text": "no goals"},
        ],
        "edges": [
            {"from": "goal:g0", "to": "tactic:t0", "role": "transformed_by"},
            {"from": "tactic:t0", "to": "closed:c0", "role": "closes_goal"},
            {"from": "tactic:t0", "to": "ref:r0", "role": "depends_on"},
        ],
    }
    cone = {
        "schema": "info_geometry.causal_chiral_cone_prompt.v1",
        "apex": {
            "name": "Demo.thm",
            "node": {"raw_name": "Demo.thm", "file": "lean/Demo.lean", "line": 3},
            "component": {"_key": "component_demo", "representative": "Demo.thm"},
        },
        "members": [
            {
                "component_id": "topology_overlay/component_demo",
                "members": [
                    {"node": {"raw_name": "Demo.thm", "file": "lean/Demo.lean", "line": 3}},
                    {"node": {"raw_name": "Demo.trivial", "file": "lean/Demo.lean", "line": 1}},
                ],
            }
        ],
        "source_excerpts": [{"name": "Demo.trivial", "file": "lean/Demo.lean", "line": 1}],
        "backward_cone": [{"component": {"_key": "component_dep", "representative": "Demo.trivial"}}],
        "forward_cone": [],
    }

    joined = build_bidirectional_cone(forest, cone)

    roles = {edge["role"] for edge in joined["edges"]}
    assert joined["schema"] == "info_geometry.bidirectional_proof_cone.v1"
    assert "forward_transformed_by" in roles
    assert "forward_closes_goal" in roles
    assert "backward_cone_context" in roles
    assert "apex_declaration" in roles
    assert "grounded_by_decl" in roles
    assert joined["summary"]["grounding_edges"] >= 1
    assert joined["authority"]["lean_remains_proof_authority"] is True


def test_paperproof_bidirectional_cone_cli(tmp_path: Path) -> None:
    forest = tmp_path / "forest.jsonl"
    cone = tmp_path / "cone.json"
    out = tmp_path / "joined.jsonl"
    forest.write_text(
        json.dumps(
            {
                "id": "forest:demo",
                "source_file": "lean/Demo.lean",
                "nodes": [{"id": "goal:g0", "kind": "goal", "text": "⊢ True"}],
                "edges": [],
            }
        )
        + "\n",
        encoding="utf-8",
    )
    cone.write_text(
        json.dumps(
            {
                "apex": {
                    "name": "Demo.thm",
                    "node": {"raw_name": "Demo.thm", "file": "lean/Demo.lean"},
                    "component": {"_key": "component_demo", "representative": "Demo.thm"},
                }
            }
        ),
        encoding="utf-8",
    )

    from tools.infra.paperproof_bidirectional_cone import main
    import sys

    old = sys.argv
    try:
        sys.argv = [
            "paperproof_bidirectional_cone.py",
            "--proof-forest",
            str(forest),
            "--cone-packet",
            str(cone),
            "--out",
            str(out),
        ]
        assert main() == 0
    finally:
        sys.argv = old

    row = json.loads(out.read_text(encoding="utf-8"))
    assert row["schema"] == "info_geometry.bidirectional_proof_cone.v1"
    assert row["summary"]["cone_nodes"] >= 1
