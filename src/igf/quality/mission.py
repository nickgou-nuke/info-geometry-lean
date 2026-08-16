"""
Mission State and Closure Loop Engine for IGF Quality.
Canonical implementation powering tools/quality/mission_state.py.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Any, Optional

from igf.common.json_io import dump_json, load_json_dict
from igf.common.time_utils import utc_now_iso

VALID_SOCKET_CLASSES = {
    "closed_by_kernel",
    "closed_by_mathlib",
    "closed_by_repo_owner",
    "literature_owned_unformalized",
    "open_problem_socket",
    "invalid_or_overclaimed_socket",
}

OPEN_PROBLEM_STOP = "open_problem_socket"


class MissionStateManager:
    """Manages persistent closure mission states and history journals."""

    def __init__(self, root_dir: Optional[Path] = None):
        if root_dir is None:
            root_dir = Path(__file__).resolve().parents[3]
        self.root_dir = root_dir
        self.state_file = self.root_dir / ".codex" / "mission" / "state.json"
        self.history_file = self.state_file.parent / "history.jsonl"

    def load(self) -> dict[str, Any]:
        """Loads state dictionary or returns empty default."""
        if not self.state_file.exists():
            return {
                "status": "idle",
                "goal": None,
                "subgoal": None,
                "last_verified": None,
                "next_blocker": None,
                "build_target": None,
                "scope_file": None,
                "socket_classification": None,
                "turns_used": 0,
                "max_turns": 30,
                "consecutive_blockers": 0,
            }
        return load_json_dict(self.state_file)

    def save(self, state: dict[str, Any]) -> None:
        """Saves state atomically."""
        dump_json(self.state_file, state)

    def append_history(self, event: dict[str, Any]) -> None:
        """Appends event journal record."""
        self.history_file.parent.mkdir(parents=True, exist_ok=True)
        record = {**event, "ts": utc_now_iso()}
        with self.history_file.open("a", encoding="utf-8") as f:
            import json
            f.write(json.dumps(record) + "\n")
