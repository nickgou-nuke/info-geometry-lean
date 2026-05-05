import json
from pathlib import Path

from tools.infra.paperproof_rpc_export_schema import packet_from_doc


def test_packet_from_paperproof_rpc_array() -> None:
    doc = [
        {
            "tacticString": "exact hp",
            "goalBefore": {
                "username": "case",
                "type": "P",
                "id": "m1",
                "hyps": [{"username": "hp", "type": "P", "id": "f1", "isProof": "proof", "value": None}],
            },
            "goalsAfter": [],
            "spawnedGoals": [],
            "tacticDependsOn": ["f1"],
            "position": {"start": {"line": 2, "character": 2}, "stop": {"line": 2, "character": 10}},
            "theorems": [],
        }
    ]

    packet = packet_from_doc(doc, theorem="Demo.thm", source_file="lean/Demo.lean")

    assert packet["schema"] == "info_geometry.paperproof_trace.v1"
    assert packet["source"] == "paperproof_rpc"
    assert packet["step_count"] == 1
    assert packet["steps"][0]["tactic"] == "exact hp"
    assert packet["steps"][0]["hypotheses_before"][0]["name"] == "hp"
    assert packet["steps"][0]["solved"] is True
    assert packet["authority"]["lean_remains_proof_authority"] is True


def test_packet_from_wrapped_webview_shape() -> None:
    doc = {
        "theorem": "Demo.andIntro",
        "file": "lean/Demo.lean",
        "proofTree": [
            {
                "tacticString": "constructor",
                "goalBefore": {"type": "P ∧ Q", "hyps": []},
                "goalsAfter": [{"type": "P", "hyps": []}, {"type": "Q", "hyps": []}],
                "spawnedGoals": [],
            }
        ],
    }

    packet = packet_from_doc(doc)

    assert packet["theorem"] == "Demo.andIntro"
    assert packet["source_file"] == "lean/Demo.lean"
    assert packet["steps"][0]["goals_after"][0]["pp"] == "P"
    assert packet["steps"][0]["solved"] is False
