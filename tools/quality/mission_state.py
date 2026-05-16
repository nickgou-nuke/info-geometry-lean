#!/usr/bin/env python3
"""
Mission State Manager for info-geometry-lean closure debt loop.

Usage:
  python3 tools/quality/mission_state.py get              # print current state JSON
  python3 tools/quality/mission_state.py set-goal "<goal>" --scope <file> --build <module>
  python3 tools/quality/mission_state.py set-subgoal "<subgoal>"
  python3 tools/quality/mission_state.py verify "<theorem_name>"    # mark last_verified
  python3 tools/quality/mission_state.py block "<reason>"           # set next_blocker
  python3 tools/quality/mission_state.py classify <socket_class>    # set socket_classification
  python3 tools/quality/mission_state.py pause
  python3 tools/quality/mission_state.py resume
  python3 tools/quality/mission_state.py clear
  python3 tools/quality/mission_state.py tick                       # increment turns_used
  python3 tools/quality/mission_state.py status                     # human-readable status

Socket classes (socket_classification):
  closed_by_kernel
  closed_by_mathlib
  closed_by_repo_owner
  literature_owned_unformalized
  open_problem_socket
  invalid_or_overclaimed_socket

Exit codes:
  0 — success
  1 — state error (invalid transition, open_problem_socket stop signal)
  2 — file I/O error
"""
from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path

STATE_FILE = Path(__file__).resolve().parents[2] / ".codex" / "mission" / "state.json"
HISTORY_FILE = STATE_FILE.parent / "history.jsonl"

VALID_SOCKET_CLASSES = {
    "closed_by_kernel",
    "closed_by_mathlib",
    "closed_by_repo_owner",
    "literature_owned_unformalized",
    "open_problem_socket",
    "invalid_or_overclaimed_socket",
}

OPEN_PROBLEM_STOP = "open_problem_socket"


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load() -> dict:
    try:
        return json.loads(STATE_FILE.read_text())
    except (OSError, json.JSONDecodeError) as e:
        print(f"ERROR: cannot load state: {e}", file=sys.stderr)
        sys.exit(2)


def save(state: dict) -> None:
    try:
        STATE_FILE.write_text(json.dumps(state, indent=2) + "\n")
    except OSError as e:
        print(f"ERROR: cannot save state: {e}", file=sys.stderr)
        sys.exit(2)


def append_history(event: dict) -> None:
    try:
        with HISTORY_FILE.open("a") as f:
            f.write(json.dumps({**event, "ts": _now()}) + "\n")
    except OSError:
        pass  # history is advisory


def cmd_get() -> None:
    print(json.dumps(load(), indent=2))


def cmd_set_goal(goal: str, scope: str | None, build: str | None) -> None:
    state = load()
    state.update({
        "goal": goal,
        "subgoal": None,
        "last_verified": None,
        "next_blocker": None,
        "build_target": build,
        "status": "active",
        "turns_used": 0,
        "consecutive_blocked": 0,
        "scope_file": scope,
        "baseline_debt": None,
        "socket_classification": None,
    })
    save(state)
    append_history({"event": "set_goal", "goal": goal, "scope": scope, "build": build})
    print(f"Mission set: {goal!r}")


def cmd_set_subgoal(subgoal: str) -> None:
    state = load()
    if state.get("status") not in ("active", "paused"):
        print("ERROR: no active mission — run set-goal first", file=sys.stderr)
        sys.exit(1)
    state["subgoal"] = subgoal
    state["consecutive_blocked"] = 0
    save(state)
    append_history({"event": "set_subgoal", "subgoal": subgoal})
    print(f"Subgoal set: {subgoal!r}")


def cmd_verify(theorem: str) -> None:
    state = load()
    state["last_verified"] = theorem
    state["subgoal"] = None
    state["next_blocker"] = None
    state["consecutive_blocked"] = 0
    save(state)
    append_history({"event": "verified", "theorem": theorem})
    print(f"Verified: {theorem}")


def cmd_block(reason: str) -> None:
    state = load()
    state["next_blocker"] = reason
    state["consecutive_blocked"] = state.get("consecutive_blocked", 0) + 1
    if state["consecutive_blocked"] >= 3:
        state["status"] = "paused"
        save(state)
        append_history({"event": "auto_paused", "reason": f"3x blocked: {reason}"})
        print(f"AUTO-PAUSED after 3 consecutive blocks: {reason}")
        sys.exit(1)
    save(state)
    append_history({"event": "blocked", "reason": reason})
    print(f"Blocked: {reason} (count: {state['consecutive_blocked']})")


def cmd_classify(socket_class: str) -> None:
    if socket_class not in VALID_SOCKET_CLASSES:
        print(f"ERROR: unknown class {socket_class!r}. Valid: {sorted(VALID_SOCKET_CLASSES)}", file=sys.stderr)
        sys.exit(1)
    state = load()
    state["socket_classification"] = socket_class
    save(state)
    append_history({"event": "classify", "class": socket_class})

    if socket_class == OPEN_PROBLEM_STOP:
        print(f"OPEN PROBLEM SOCKET — loop must stop. Emit report entry, do not fake a proof.")
        sys.exit(1)  # signal to caller: stop, do not continue
    print(f"Socket classified: {socket_class}")


def cmd_pause() -> None:
    state = load()
    state["status"] = "paused"
    save(state)
    append_history({"event": "pause"})
    print("Mission paused.")


def cmd_resume() -> None:
    state = load()
    if state.get("status") == "idle":
        print("ERROR: no mission to resume", file=sys.stderr)
        sys.exit(1)
    state["status"] = "active"
    state["consecutive_blocked"] = 0
    save(state)
    append_history({"event": "resume"})
    print(f"Mission resumed: {state.get('goal')!r}")


def cmd_clear() -> None:
    state = {
        "goal": None, "subgoal": None, "last_verified": None,
        "next_blocker": None, "build_target": None, "status": "idle",
        "turns_used": 0, "max_turns": 30, "consecutive_blocked": 0,
        "scope_file": None, "baseline_debt": None, "socket_classification": None,
    }
    save(state)
    append_history({"event": "clear"})
    print("Mission cleared.")


def cmd_tick() -> None:
    state = load()
    state["turns_used"] = state.get("turns_used", 0) + 1
    if state["turns_used"] >= state.get("max_turns", 30):
        state["status"] = "paused"
        save(state)
        append_history({"event": "budget_exhausted", "turns": state["turns_used"]})
        print(f"BUDGET EXHAUSTED at turn {state['turns_used']} — auto-paused.")
        sys.exit(1)
    save(state)
    print(f"Turn {state['turns_used']}/{state.get('max_turns', 30)}")


def cmd_status() -> None:
    s = load()
    print(f"Status         : {s.get('status', 'idle')}")
    print(f"Goal           : {s.get('goal') or '(none)'}")
    print(f"Subgoal        : {s.get('subgoal') or '(none)'}")
    print(f"Last verified  : {s.get('last_verified') or '(none)'}")
    print(f"Next blocker   : {s.get('next_blocker') or '(none)'}")
    print(f"Build target   : {s.get('build_target') or '(none)'}")
    print(f"Scope file     : {s.get('scope_file') or '(none)'}")
    print(f"Classification : {s.get('socket_classification') or '(none)'}")
    print(f"Turns used     : {s.get('turns_used', 0)}/{s.get('max_turns', 30)}")
    print(f"Consecutive blk: {s.get('consecutive_blocked', 0)}")


# ── entry point ──────────────────────────────────────────────────────────────

def main() -> None:
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        sys.exit(0)

    cmd = args[0]

    if cmd == "get":
        cmd_get()
    elif cmd == "set-goal":
        if len(args) < 2:
            print("Usage: set-goal <goal> [--scope <file>] [--build <module>]", file=sys.stderr)
            sys.exit(1)
        goal = args[1]
        scope = args[args.index("--scope") + 1] if "--scope" in args else None
        build = args[args.index("--build") + 1] if "--build" in args else None
        cmd_set_goal(goal, scope, build)
    elif cmd == "set-subgoal":
        if len(args) < 2:
            print("Usage: set-subgoal <subgoal>", file=sys.stderr); sys.exit(1)
        cmd_set_subgoal(args[1])
    elif cmd == "verify":
        if len(args) < 2:
            print("Usage: verify <theorem_name>", file=sys.stderr); sys.exit(1)
        cmd_verify(args[1])
    elif cmd == "block":
        if len(args) < 2:
            print("Usage: block <reason>", file=sys.stderr); sys.exit(1)
        cmd_block(args[1])
    elif cmd == "classify":
        if len(args) < 2:
            print(f"Usage: classify <class>  ({' | '.join(sorted(VALID_SOCKET_CLASSES))})", file=sys.stderr)
            sys.exit(1)
        cmd_classify(args[1])
    elif cmd == "pause":
        cmd_pause()
    elif cmd == "resume":
        cmd_resume()
    elif cmd == "clear":
        cmd_clear()
    elif cmd == "tick":
        cmd_tick()
    elif cmd == "status":
        cmd_status()
    else:
        print(f"Unknown command: {cmd!r}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
