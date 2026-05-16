#!/usr/bin/env python3
"""Repo-local Hermes-style standing goal loop support.

This tool implements the deterministic state machine around a standing goal:
set, pause, resume, clear, subgoal, judge, and continuation-prompt rendering.

It intentionally does not call an LLM.  A runner may supply the judge verdict as
strict JSON via ``judge --json`` or ``judge --json-file``.  Bad JSON is handled
like Hermes: fail open until the consecutive parse-failure budget is exhausted,
then pause the loop and point the caller at the judge configuration.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any


DEFAULT_MAX_TURNS = 20
DEFAULT_MAX_CONSECUTIVE_PARSE_FAILURES = 3
DEFAULT_STATE_DIR = Path("artifacts/goal-loop")

CONTINUATION_PROMPT_TEMPLATE = (
    "[Continuing toward your standing goal]\n"
    "Goal: {goal}\n\n"
    "Continue working toward this goal. Take the next concrete step. "
    "If you believe the goal is complete, state so explicitly and stop. "
    "If you are blocked and need input from the user, say so clearly and stop."
)

CONTINUATION_PROMPT_WITH_SUBGOALS_TEMPLATE = (
    "[Continuing toward your standing goal]\n"
    "Goal: {goal}\n\n"
    "Additional criteria the user added mid-loop:\n"
    "{subgoals_block}\n\n"
    "Continue working toward the goal AND all additional criteria. Take the next "
    "concrete step. If you believe the goal and every additional criterion are "
    "complete, state so explicitly and stop. If you are blocked and need input "
    "from the user, say so clearly and stop."
)


@dataclass
class GoalState:
    goal: str
    status: str = "active"
    turns_used: int = 0
    max_turns: int = DEFAULT_MAX_TURNS
    created_at: float = 0.0
    last_turn_at: float = 0.0
    last_verdict: str | None = None
    last_reason: str | None = None
    paused_reason: str | None = None
    consecutive_parse_failures: int = 0
    subgoals: list[str] = field(default_factory=list)

    @classmethod
    def new(cls, goal: str, *, max_turns: int = DEFAULT_MAX_TURNS) -> "GoalState":
        now = time.time()
        return cls(goal=goal, max_turns=max_turns, created_at=now, last_turn_at=now)

    @classmethod
    def from_json(cls, raw: str) -> "GoalState":
        data = json.loads(raw)
        subgoals = data.get("subgoals") or []
        if not isinstance(subgoals, list):
            subgoals = []
        return cls(
            goal=str(data.get("goal", "")),
            status=str(data.get("status", "active")),
            turns_used=int(data.get("turns_used", 0) or 0),
            max_turns=int(data.get("max_turns", DEFAULT_MAX_TURNS) or DEFAULT_MAX_TURNS),
            created_at=float(data.get("created_at", 0.0) or 0.0),
            last_turn_at=float(data.get("last_turn_at", 0.0) or 0.0),
            last_verdict=data.get("last_verdict"),
            last_reason=data.get("last_reason"),
            paused_reason=data.get("paused_reason"),
            consecutive_parse_failures=int(data.get("consecutive_parse_failures", 0) or 0),
            subgoals=[str(s).strip() for s in subgoals if str(s).strip()],
        )

    def to_json(self) -> str:
        return json.dumps(asdict(self), ensure_ascii=False, indent=2) + "\n"

    def render_subgoals_block(self) -> str:
        return "\n".join(f"- {i}. {text}" for i, text in enumerate(self.subgoals, start=1))

    def continuation_prompt(self) -> str:
        if self.subgoals:
            return CONTINUATION_PROMPT_WITH_SUBGOALS_TEMPLATE.format(
                goal=self.goal,
                subgoals_block=self.render_subgoals_block(),
            )
        return CONTINUATION_PROMPT_TEMPLATE.format(goal=self.goal)


def sanitize_session_id(session_id: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9_.-]+", "_", session_id.strip())
    if not cleaned:
        raise ValueError("session id cannot be empty")
    return cleaned


def state_path(state_dir: Path, session_id: str) -> Path:
    return state_dir / f"{sanitize_session_id(session_id)}.json"


def load_state(state_dir: Path, session_id: str) -> GoalState | None:
    path = state_path(state_dir, session_id)
    if not path.exists():
        return None
    return GoalState.from_json(path.read_text(encoding="utf-8"))


def save_state(state_dir: Path, session_id: str, state: GoalState) -> Path:
    state_dir.mkdir(parents=True, exist_ok=True)
    path = state_path(state_dir, session_id)
    path.write_text(state.to_json(), encoding="utf-8")
    return path


def parse_judge_json(raw: str) -> tuple[bool, str]:
    data = json.loads(raw)
    if not isinstance(data, dict):
        raise ValueError("judge output must be a JSON object")
    done = data.get("done")
    reason = data.get("reason")
    if not isinstance(done, bool):
        raise ValueError("judge output field 'done' must be boolean")
    if not isinstance(reason, str) or not reason.strip():
        raise ValueError("judge output field 'reason' must be a nonempty string")
    return done, reason.strip()


def cmd_set(args: argparse.Namespace) -> int:
    goal = " ".join(args.goal).strip()
    if not goal:
        print("error: goal text cannot be empty", file=sys.stderr)
        return 2
    state = GoalState.new(goal, max_turns=args.max_turns)
    path = save_state(args.state_dir, args.session, state)
    print(f"goal set: {path}")
    return 0


def require_state(args: argparse.Namespace) -> GoalState:
    state = load_state(args.state_dir, args.session)
    if state is None:
        raise SystemExit("error: no goal state for session")
    return state


def cmd_status(args: argparse.Namespace) -> int:
    state = load_state(args.state_dir, args.session)
    if state is None:
        print(json.dumps({"status": "missing"}, indent=2))
        return 1
    print(state.to_json(), end="")
    return 0


def cmd_pause(args: argparse.Namespace) -> int:
    state = require_state(args)
    state.status = "paused"
    state.paused_reason = args.reason
    state.last_turn_at = time.time()
    save_state(args.state_dir, args.session, state)
    print("goal paused")
    return 0


def cmd_resume(args: argparse.Namespace) -> int:
    state = require_state(args)
    if state.status in {"done", "cleared"}:
        print(f"error: cannot resume goal with status {state.status}", file=sys.stderr)
        return 2
    state.status = "active"
    state.paused_reason = None
    state.last_turn_at = time.time()
    save_state(args.state_dir, args.session, state)
    print("goal resumed")
    return 0


def cmd_clear(args: argparse.Namespace) -> int:
    state = load_state(args.state_dir, args.session)
    if state is None:
        print("goal already clear")
        return 0
    state.status = "cleared"
    state.paused_reason = "cleared by user"
    state.last_turn_at = time.time()
    save_state(args.state_dir, args.session, state)
    print("goal cleared")
    return 0


def cmd_subgoal(args: argparse.Namespace) -> int:
    text = " ".join(args.text).strip()
    if not text:
        print("error: subgoal text cannot be empty", file=sys.stderr)
        return 2
    state = require_state(args)
    state.subgoals.append(text)
    state.last_turn_at = time.time()
    save_state(args.state_dir, args.session, state)
    print(f"subgoal added: {len(state.subgoals)}")
    return 0


def cmd_preempt(args: argparse.Namespace) -> int:
    state = require_state(args)
    if state.status == "active":
        state.status = "paused"
        state.paused_reason = "user message preempted continuation"
        state.last_turn_at = time.time()
        save_state(args.state_dir, args.session, state)
    print("goal continuation preempted")
    return 0


def cmd_continuation(args: argparse.Namespace) -> int:
    state = require_state(args)
    if state.status != "active":
        print(f"error: goal is {state.status}, not active", file=sys.stderr)
        return 2
    if state.turns_used >= state.max_turns:
        state.status = "paused"
        state.paused_reason = "turn budget exhausted"
        save_state(args.state_dir, args.session, state)
        print("error: turn budget exhausted; goal auto-paused", file=sys.stderr)
        return 2
    print(state.continuation_prompt())
    return 0


def _read_judge_raw(args: argparse.Namespace) -> str:
    if args.json is not None:
        return args.json
    if args.json_file is not None:
        return Path(args.json_file).read_text(encoding="utf-8")
    return sys.stdin.read()


def cmd_judge(args: argparse.Namespace) -> int:
    state = require_state(args)
    if state.status not in {"active", "paused"}:
        print(f"goal status unchanged: {state.status}")
        return 0

    try:
        done, reason = parse_judge_json(_read_judge_raw(args))
    except Exception as exc:
        state.last_verdict = "continue"
        state.last_reason = f"judge parse failure: {exc}"
        state.consecutive_parse_failures += 1
        state.last_turn_at = time.time()
        if state.consecutive_parse_failures >= args.max_parse_failures:
            state.status = "paused"
            state.paused_reason = "judge returned bad JSON repeatedly; route goal_judge to a stricter model"
        save_state(args.state_dir, args.session, state)
        print(state.to_json(), end="")
        return 0

    state.consecutive_parse_failures = 0
    state.last_reason = reason
    state.last_turn_at = time.time()
    if done:
        state.status = "done"
        state.last_verdict = "done"
    else:
        state.last_verdict = "continue"
        if state.status == "paused" and not args.keep_paused:
            state.status = "active"
        if state.status == "active":
            state.turns_used += 1
            if state.turns_used >= state.max_turns:
                state.status = "paused"
                state.paused_reason = "turn budget exhausted"
    save_state(args.state_dir, args.session, state)
    print(state.to_json(), end="")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--session", default="default", help="session id")
    parser.add_argument("--state-dir", type=Path, default=DEFAULT_STATE_DIR)
    sub = parser.add_subparsers(dest="command", required=True)

    p_set = sub.add_parser("set", help="set a standing goal")
    p_set.add_argument("--max-turns", type=int, default=DEFAULT_MAX_TURNS)
    p_set.add_argument("goal", nargs=argparse.REMAINDER)
    p_set.set_defaults(func=cmd_set)

    p_status = sub.add_parser("status", help="show goal state")
    p_status.set_defaults(func=cmd_status)

    p_pause = sub.add_parser("pause", help="pause goal")
    p_pause.add_argument("--reason", default="paused by user")
    p_pause.set_defaults(func=cmd_pause)

    p_resume = sub.add_parser("resume", help="resume goal")
    p_resume.set_defaults(func=cmd_resume)

    p_clear = sub.add_parser("clear", help="clear goal")
    p_clear.set_defaults(func=cmd_clear)

    p_subgoal = sub.add_parser("subgoal", help="add a first-class subgoal")
    p_subgoal.add_argument("text", nargs=argparse.REMAINDER)
    p_subgoal.set_defaults(func=cmd_subgoal)

    p_preempt = sub.add_parser("preempt", help="pause because a real user message arrived")
    p_preempt.set_defaults(func=cmd_preempt)

    p_cont = sub.add_parser("continuation", help="render the continuation prompt")
    p_cont.set_defaults(func=cmd_continuation)

    p_judge = sub.add_parser("judge", help="apply strict JSON judge result")
    p_judge.add_argument("--json")
    p_judge.add_argument("--json-file")
    p_judge.add_argument("--keep-paused", action="store_true")
    p_judge.add_argument(
        "--max-parse-failures",
        type=int,
        default=DEFAULT_MAX_CONSECUTIVE_PARSE_FAILURES,
    )
    p_judge.set_defaults(func=cmd_judge)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
