from __future__ import annotations

import json
from pathlib import Path

from tools.infra import goal_loop


def run_cli(tmp_path: Path, *args: str) -> int:
    return goal_loop.main(["--session", "s1", "--state-dir", str(tmp_path), *args])


def load_state(tmp_path: Path) -> goal_loop.GoalState:
    state = goal_loop.load_state(tmp_path, "s1")
    assert state is not None
    return state


def test_empty_goal_rejected(tmp_path: Path) -> None:
    assert run_cli(tmp_path, "set") == 2
    assert goal_loop.load_state(tmp_path, "s1") is None


def test_subgoal_is_in_continuation_prompt(tmp_path: Path, capsys) -> None:
    assert run_cli(tmp_path, "set", "close native AFP debt") == 0
    assert run_cli(tmp_path, "subgoal", "build the touched Lean modules") == 0
    assert run_cli(tmp_path, "continuation") == 0
    out = capsys.readouterr().out
    assert "close native AFP debt" in out
    assert "Additional criteria" in out
    assert "build the touched Lean modules" in out


def test_judge_done_marks_goal_done(tmp_path: Path) -> None:
    assert run_cli(tmp_path, "set", "ship proof") == 0
    assert run_cli(tmp_path, "judge", "--json", '{"done": true, "reason": "proof built"}') == 0
    state = load_state(tmp_path)
    assert state.status == "done"
    assert state.last_verdict == "done"
    assert state.last_reason == "proof built"


def test_bad_judge_json_fails_open_then_auto_pauses(tmp_path: Path) -> None:
    assert run_cli(tmp_path, "set", "ship proof") == 0
    for expected in [1, 2]:
        assert run_cli(tmp_path, "judge", "--json", "not json") == 0
        state = load_state(tmp_path)
        assert state.status == "active"
        assert state.last_verdict == "continue"
        assert state.consecutive_parse_failures == expected

    assert run_cli(tmp_path, "judge", "--json", "not json") == 0
    state = load_state(tmp_path)
    assert state.status == "paused"
    assert "stricter model" in (state.paused_reason or "")


def test_state_file_is_strict_json_object(tmp_path: Path) -> None:
    assert run_cli(tmp_path, "set", "native closure") == 0
    raw = json.loads((tmp_path / "s1.json").read_text(encoding="utf-8"))
    assert raw["goal"] == "native closure"
    assert raw["status"] == "active"
