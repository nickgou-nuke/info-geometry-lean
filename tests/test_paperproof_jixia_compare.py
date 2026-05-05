import json
from pathlib import Path

from tools.infra.paperproof_jixia_compare import build_report, render_markdown


def test_build_report_matches_paperproof_trace_against_jixia(tmp_path: Path) -> None:
    paperproof = tmp_path / "paperproof.jsonl"
    jixia = tmp_path / "jixia.jsonl"
    paperproof.write_text(
        json.dumps(
            {
                "schema": "info_geometry.paperproof_trace.v1",
                "source_file": "lean/Demo.lean",
                "steps": [
                    {
                        "tactic": "trivial",
                        "range": {"start": [1, 2], "stop": [1, 9]},
                        "goals_before": [{"pp": "⊢ True"}],
                        "goals_after": [],
                    }
                ],
            }
        )
        + "\n",
        encoding="utf-8",
    )
    jixia.write_text(
        json.dumps(
            {
                "schema": "info_geometry.jixia.tactic_transition.v1",
                "source_file": "lean/Demo.lean",
                "tactic_syntax": "trivial",
                "range": {"start": [1, 2], "stop": [1, 9]},
                "before": [{"pp": "⊢ True"}],
                "after": [],
            }
        )
        + "\n",
        encoding="utf-8",
    )

    report = build_report(paperproof_trace=paperproof, jixia_tactics=jixia)

    assert report["groups"] == 1
    assert report["totals"]["paperproof_steps"] == 1
    assert report["totals"]["jixia_steps"] == 1
    assert report["totals"]["exact_signature_matches"] == 1
    assert report["totals"]["tactic_text_matches"] == 1
    assert report["authority"]["lean_remains_proof_authority"] is True


def test_render_markdown_contains_group_summary(tmp_path: Path) -> None:
    report = {
        "totals": {
            "paperproof_steps": 1,
            "jixia_steps": 2,
            "exact_signature_matches": 0,
            "tactic_text_matches": 1,
            "range_matches": 1,
            "before_goal_matches": 1,
            "after_goal_matches": 0,
        },
        "comparisons": [
            {
                "source_key": "lean/Demo.lean",
                "paperproof_steps": 1,
                "jixia_steps": 2,
                "step_count_delta": -1,
                "exact_signature_matches": 0,
                "tactic_text_matches": 1,
                "range_matches": 1,
            }
        ],
    }

    md = render_markdown(report)

    assert "Paperproof/Jixia" in md
    assert "`lean/Demo.lean`" in md
    assert "Step count delta" in md
