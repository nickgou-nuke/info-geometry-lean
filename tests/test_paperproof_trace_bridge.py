import json
from pathlib import Path

from tools.infra.paperproof_trace_bridge import build_packets, render_markdown


def test_build_packets_from_jixia_tactics(tmp_path: Path) -> None:
    tactics = tmp_path / "jixia_tactic_transitions.jsonl"
    tactics.write_text(
        json.dumps(
            {
                "source_file": "lean/Demo.lean",
                "tactic_syntax": "exact hp",
                "references": ["hp"],
                "before": [
                    {
                        "pp": "⊢ P",
                        "type": "P",
                        "context": [{"userName": "hp", "type": "P"}],
                    }
                ],
                "after": [],
            }
        )
        + "\n",
        encoding="utf-8",
    )

    packets = build_packets(jixia_tactics=[tactics], sft=[])

    assert packets[0]["schema"] == "info_geometry.paperproof_trace.v1"
    assert packets[0]["source_file"] == "lean/Demo.lean"
    assert packets[0]["steps"][0]["tactic"] == "exact hp"
    assert packets[0]["steps"][0]["node_class"] == "leaf"
    assert packets[0]["steps"][0]["info_kind"] == "tactic"
    assert packets[0]["steps"][0]["is_leaf_transition"] is True
    assert packets[0]["steps"][0]["hypotheses_before"][0]["name"] == "hp"
    assert packets[0]["steps"][0]["solved"] is True


def test_build_packets_preserves_aggregate_tactic_classification(tmp_path: Path) -> None:
    tactics = tmp_path / "jixia_tactic_transitions.jsonl"
    tactics.write_text(
        json.dumps(
            {
                "source_file": "lean/Demo.lean",
                "tactic_syntax": "Tactic.tacticSeq [...]",
                "node_class": "aggregate",
                "info_kind": "tactic",
                "is_leaf_transition": False,
                "references": [],
                "before": [{"pp": "⊢ True", "type": "True"}],
                "after": [],
            }
        )
        + "\n",
        encoding="utf-8",
    )

    packets = build_packets(jixia_tactics=[tactics], sft=[])

    assert packets[0]["steps"][0]["node_class"] == "aggregate"
    assert packets[0]["steps"][0]["is_leaf_transition"] is False


def test_render_markdown_mentions_goals_and_tactics(tmp_path: Path) -> None:
    sft = tmp_path / "tactic_sft.jsonl"
    sft.write_text(
        json.dumps(
            {
                "source": "jixia",
                "theorem": "Demo.thm",
                "lean_file": "lean/Demo.lean",
                "goal_before": "⊢ True",
                "tactic": "trivial",
                "goal_after": "no goals",
            }
        )
        + "\n",
        encoding="utf-8",
    )

    packets = build_packets(jixia_tactics=[], sft=[sft])
    md = render_markdown(packets)

    assert "`Demo.thm`" in md
    assert "`trivial`" in md
    assert "(leaf)" in md
    assert "Goals after: `no goals`" in md
