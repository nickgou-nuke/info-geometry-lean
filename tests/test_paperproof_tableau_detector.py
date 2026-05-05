import json

from tools.infra.paperproof_tableau_detector import profile_trace
from tools.infra.paperproof_training_effects import rows_from_packet


def test_profile_trace_detects_tableau_like_contradiction_shape() -> None:
    packet = {
        "id": "Demo.tableau",
        "theorem": "Demo.tableau",
        "steps": [
            {
                "index": 0,
                "tactic": "by_contra h",
                "goals_before": [{"pp": "⊢ P"}],
                "goals_after": [{"pp": "⊢ False"}],
            },
            {
                "index": 1,
                "tactic": "contradiction",
                "goals_before": [{"pp": "⊢ False"}],
                "goals_after": [],
            },
        ],
    }

    profile = profile_trace(packet)

    assert profile["schema"] == "info_geometry.paperproof_tableau_profile.v1"
    assert profile["tableau_like"] is True
    assert profile["entry_tactic"] == "by_contra h"
    assert "contradiction_entry" in profile["strategy_labels"]
    assert "top_down_false_goal" in profile["strategy_labels"]
    assert profile["contradiction_closure_steps"] == 1


def test_training_effects_adds_tableau_labels() -> None:
    packet = {
        "source": "paperproof_rpc",
        "theorem": "Demo.tableau",
        "steps": [
            {
                "index": 0,
                "tactic": "by_contra h",
                "goals_before": [{"pp": "⊢ P"}],
                "goals_after": [{"pp": "⊢ False"}],
                "hypotheses_before": [],
                "hypotheses_after": [{"name": "h", "type": "¬P"}],
            },
            {
                "index": 1,
                "tactic": "contradiction",
                "goals_before": [{"pp": "⊢ False"}],
                "goals_after": [],
                "hypotheses_before": [{"name": "h", "type": "False"}],
                "hypotheses_after": [],
            },
        ],
    }

    rows = rows_from_packet(packet)

    assert "starts_tableau_mode" in rows[0]["effect_labels"]
    assert "contradiction_entry" in rows[0]["effect_labels"]
    assert "contradiction_closure" in rows[1]["effect_labels"]
    assert "closes_tableau_branch" in rows[1]["effect_labels"]
