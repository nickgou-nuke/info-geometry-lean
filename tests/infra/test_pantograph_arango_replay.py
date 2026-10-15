from __future__ import annotations

import io
import json
from pathlib import Path
from typing import Any

import pytest

from tools.infra import pantograph_arango_replay as replay


class CaptureInput:
    def __init__(self) -> None:
        self.lines: list[str] = []
        self.closed = False

    def write(self, value: str) -> int:
        self.lines.append(value)
        return len(value)

    def flush(self) -> None:
        pass

    def close(self) -> None:
        self.closed = True


class FakeProcess:
    def __init__(self, responses: list[dict[str, Any]]) -> None:
        self.stdin = CaptureInput()
        self.stdout = io.StringIO("ready.\n" + "".join(json.dumps(row) + "\n" for row in responses))
        self.return_code: int | None = None

    def poll(self) -> int | None:
        return self.return_code

    def wait(self) -> int:
        self.return_code = 0
        return 0


def test_replay_remaps_local_state_ids_and_ignores_them_in_comparison(tmp_path: Path) -> None:
    requests = [
        {
            "sequence": 1,
            "command": "goal.start",
            "payload": {"copyFrom": "A.theorem"},
            "rawLine": '{"cmd":"goal.start","payload":{"copyFrom":"A.theorem"}}',
        },
        {
            "sequence": 2,
            "command": "goal.tactic",
            "payload": {"stateId": 44, "tactic": "exact A.theorem"},
            "rawLine": '{"cmd":"goal.tactic","payload":{"stateId":44,"tactic":"exact A.theorem"}}',
        },
    ]
    responses = [
        {"sequence": 1, "response": {"stateId": 44, "root": "_uniq.old"}},
        {
            "sequence": 2,
            "response": {
                "nextStateId": 45, "goals": [], "hasSorry": False,
                "hasUnsafe": False, "messages": [],
            },
        },
    ]
    process = FakeProcess([
        {"stateId": 8, "root": "_uniq.new"},
        {"nextStateId": 9, "goals": [], "hasSorry": False, "hasUnsafe": False, "messages": []},
    ])

    result = replay.replay_exchange(
        ["repl", "A"], requests, responses, tmp_path,
        popen=lambda *_args, **_kwargs: process,
    )

    assert result == {"status": "matched", "requestCount": 2}
    second_request = json.loads(process.stdin.lines[1])
    assert second_request["payload"]["stateId"] == 8
    assert process.stdin.closed


def test_replay_detects_goal_or_diagnostic_divergence(tmp_path: Path) -> None:
    request = {
        "sequence": 1, "command": "goal.start", "payload": {"expr": "True"},
        "rawLine": '{"cmd":"goal.start","payload":{"expr":"True"}}',
    }
    expected = {"sequence": 1, "response": {"stateId": 3, "root": "_uniq.a", "goals": ["⊢ True"]}}
    process = FakeProcess([{"stateId": 0, "root": "_uniq.b", "goals": ["⊢ False"]}])
    result = replay.replay_exchange(
        ["repl", "Init"], [request], [expected], tmp_path,
        popen=lambda *_args, **_kwargs: process,
    )
    assert result["status"] == "mismatch"
    assert result["sequence"] == 1


def test_replay_restores_a_branch_using_fresh_process_state_ids(tmp_path: Path) -> None:
    commands = [
        ("goal.start", {"expr": "∀ (p : Prop), p → p ∧ p"}),
        ("goal.tactic", {"stateId": 70, "tactic": "intro p h"}),
        ("goal.tactic", {"stateId": 71, "tactic": "apply And.intro"}),
        ("goal.tactic", {"stateId": 72, "goalId": 0, "tactic": "exact h"}),
        ("goal.tactic", {"stateId": 73, "goalId": 0, "tactic": "exact h"}),
        ("goal.continue", {"target": 74, "branch": 73}),
    ]
    original_lines = [
        json.dumps({"cmd": command, "payload": payload})
        for command, payload in commands
    ]
    requests = [
        {
            "sequence": index,
            "command": command,
            "payload": payload,
            "rawLine": original_lines[index - 1],
        }
        for index, (command, payload) in enumerate(commands, start=1)
    ]
    expected_responses = [
        {"stateId": 70, "root": "_uniq.old"},
        {"nextStateId": 71, "goals": [{"target": "p ∧ p"}], "messages": []},
        {"nextStateId": 72, "goals": [{"target": "p"}, {"target": "p"}], "messages": []},
        {"nextStateId": 73, "goals": [{"target": "p"}], "messages": []},
        {"nextStateId": 74, "goals": [], "messages": []},
        {"nextStateId": 75, "goals": [{"target": "p"}], "messages": []},
    ]
    responses = [
        {"sequence": index, "response": response}
        for index, response in enumerate(expected_responses, start=1)
    ]
    process = FakeProcess([
        {"stateId": 4, "root": "_uniq.fresh"},
        {"nextStateId": 5, "goals": [{"target": "p ∧ p"}], "messages": []},
        {"nextStateId": 6, "goals": [{"target": "p"}, {"target": "p"}], "messages": []},
        {"nextStateId": 7, "goals": [{"target": "p"}], "messages": []},
        {"nextStateId": 8, "goals": [], "messages": []},
        {"nextStateId": 9, "goals": [{"target": "p"}], "messages": []},
    ])

    result = replay.replay_exchange(
        ["repl", "Init"], requests, responses, tmp_path,
        popen=lambda *_args, **_kwargs: process,
    )

    assert result == {"status": "matched", "requestCount": 6}
    continued = json.loads(process.stdin.lines[5])
    assert continued["payload"]["target"] == 8
    assert continued["payload"]["branch"] == 7


def test_replay_refuses_missing_or_noncontiguous_responses(tmp_path: Path) -> None:
    request = {"sequence": 2, "command": "stat", "payload": {}, "rawLine": "stat {}"}
    with pytest.raises(RuntimeError, match="duplicated or has gaps"):
        replay.replay_exchange(["repl", "Init"], [request], [], tmp_path)
