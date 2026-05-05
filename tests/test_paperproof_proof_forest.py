import json
from pathlib import Path

from tools.infra.paperproof_proof_forest import build_forest


def test_build_forest_creates_goal_tactic_and_hypothesis_edges() -> None:
    packet = {
        "id": "Demo.thm",
        "source": "paperproof_rpc",
        "theorem": "Demo.thm",
        "source_file": "lean/Demo.lean",
        "steps": [
            {
                "index": 0,
                "tactic": "constructor",
                "range": {"start": [1, 2], "stop": [1, 13]},
                "references": [],
                "goals_before": [{"pp": "⊢ P ∧ Q", "raw": {"id": "g0"}}],
                "goals_after": [{"pp": "⊢ P", "raw": {"id": "g1"}}, {"pp": "⊢ Q", "raw": {"id": "g2"}}],
                "hypotheses_before": [{"name": "hp", "type": "P", "raw": {"id": "h1"}}],
                "hypotheses_after": [{"name": "hp", "type": "P", "raw": {"id": "h1"}}],
            },
            {
                "index": 1,
                "tactic": "exact hp",
                "range": {"start": [2, 2], "stop": [2, 10]},
                "references": ["h1"],
                "goals_before": [{"pp": "⊢ P", "raw": {"id": "g1"}}],
                "goals_after": [],
                "hypotheses_before": [{"name": "hp", "type": "P", "raw": {"id": "h1"}}],
                "hypotheses_after": [],
            },
        ],
    }

    forest = build_forest(packet)

    kinds = {node["kind"] for node in forest["nodes"]}
    roles = {edge["role"] for edge in forest["edges"]}
    assert forest["schema"] == "info_geometry.paperproof_forest.v1"
    assert {"proof", "goal", "tactic", "hypothesis", "closed_goal", "reference"} <= kinds
    assert {"transformed_by", "produces_goal", "goal_child", "available_hypothesis", "closes_goal", "depends_on"} <= roles
    assert forest["summary"]["tactics"] == 2
    assert forest["summary"]["goals"] == 3
    assert forest["authority"]["lean_remains_proof_authority"] is True


def test_paperproof_proof_forest_cli(tmp_path: Path) -> None:
    trace = tmp_path / "trace.jsonl"
    out = tmp_path / "forest.jsonl"
    trace.write_text(
        json.dumps(
            {
                "id": "Demo.trivial",
                "steps": [
                    {
                        "index": 0,
                        "tactic": "trivial",
                        "goals_before": [{"pp": "⊢ True"}],
                        "goals_after": [],
                    }
                ],
            }
        )
        + "\n",
        encoding="utf-8",
    )

    from tools.infra.paperproof_proof_forest import main
    import sys

    old = sys.argv
    try:
        sys.argv = ["paperproof_proof_forest.py", "--paperproof-trace", str(trace), "--out", str(out)]
        assert main() == 0
    finally:
        sys.argv = old

    row = json.loads(out.read_text(encoding="utf-8"))
    assert row["summary"]["tactics"] == 1
    assert any(edge["role"] == "closes_goal" for edge in row["edges"])
