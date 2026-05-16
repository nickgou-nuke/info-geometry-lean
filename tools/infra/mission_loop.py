#!/usr/bin/env python3
"""Persistent mission loop for native closure debt work.

This is a repo-local orchestration wrapper around the standing goal state machine
in `tools/infra/goal_loop.py`.

The loop is eternal at the mission level: it never marks the repository mission
itself as done. Individual debt sockets may close; the mission re-arms on the
next open socket until the user clears or pauses it.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.goal_loop import GoalState, load_state as load_goal_state, save_state as save_goal_state
else:
    from tools.infra.goal_loop import GoalState, load_state as load_goal_state, save_state as save_goal_state


DEFAULT_STATE_DIR = Path("artifacts/mission-loop")
DEFAULT_GOAL_STATE_DIR = Path("artifacts/goal-loop")
DEFAULT_HEARTBEAT_LOG = Path("artifacts/hermes_loop/heartbeat/native_closure_mission.log")
DEFAULT_LEDGER = Path("reports/closure/socket-owner-ledger.json")
DEFAULT_GATE_POLICY = Path("tools/quality/closure_debt_gate.json")
DEFAULT_BUILD_TARGET = "InfoGeometry.Canonical.All"
DEFAULT_MISSION = "Pay the Native Closure Debts of the repository"
DEFAULT_MODE = "eternal"

TERMINAL_SOCKET_STATUSES = {
    "done",
    "closed",
    "closed_by_repo_owner",
    "closed_by_mathlib",
    "resolved",
}


@dataclass
class MissionState:
    session: str
    mission: str = DEFAULT_MISSION
    mode: str = DEFAULT_MODE
    scope: str = ""
    ledger: str = str(DEFAULT_LEDGER)
    gate_policy: str = str(DEFAULT_GATE_POLICY)
    build_target: str = DEFAULT_BUILD_TARGET
    heartbeat_log: str = str(DEFAULT_HEARTBEAT_LOG)
    status: str = "active"
    created_at: float = 0.0
    last_tick_at: float = 0.0
    ticks_used: int = 0
    current_socket_id: str | None = None
    current_socket_title: str | None = None
    closed_sockets: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)

    @classmethod
    def new(
        cls,
        session: str,
        *,
        mission: str = DEFAULT_MISSION,
        scope: str = "",
        ledger: str = str(DEFAULT_LEDGER),
        gate_policy: str = str(DEFAULT_GATE_POLICY),
        build_target: str = DEFAULT_BUILD_TARGET,
        heartbeat_log: str = str(DEFAULT_HEARTBEAT_LOG),
    ) -> "MissionState":
        now = time.time()
        return cls(
            session=session,
            mission=mission,
            scope=scope,
            ledger=ledger,
            gate_policy=gate_policy,
            build_target=build_target,
            heartbeat_log=heartbeat_log,
            created_at=now,
            last_tick_at=now,
        )

    @classmethod
    def from_json(cls, raw: str) -> "MissionState":
        data = json.loads(raw)
        return cls(
            session=str(data.get("session", "")),
            mission=str(data.get("mission", DEFAULT_MISSION)),
            mode=str(data.get("mode", DEFAULT_MODE)),
            scope=str(data.get("scope", "")),
            ledger=str(data.get("ledger", DEFAULT_LEDGER)),
            gate_policy=str(data.get("gate_policy", DEFAULT_GATE_POLICY)),
            build_target=str(data.get("build_target", DEFAULT_BUILD_TARGET)),
            heartbeat_log=str(data.get("heartbeat_log", DEFAULT_HEARTBEAT_LOG)),
            status=str(data.get("status", "active")),
            created_at=float(data.get("created_at", 0.0) or 0.0),
            last_tick_at=float(data.get("last_tick_at", 0.0) or 0.0),
            ticks_used=int(data.get("ticks_used", 0) or 0),
            current_socket_id=data.get("current_socket_id"),
            current_socket_title=data.get("current_socket_title"),
            closed_sockets=[str(s) for s in (data.get("closed_sockets") or []) if str(s).strip()],
            notes=[str(s) for s in (data.get("notes") or []) if str(s).strip()],
        )

    def to_json(self) -> str:
        return json.dumps(asdict(self), ensure_ascii=False, indent=2) + "\n"


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def sanitize_session_id(session_id: str) -> str:
    cleaned = "".join(ch if ch.isalnum() or ch in "_.-" else "_" for ch in session_id.strip())
    if not cleaned:
        raise ValueError("session id cannot be empty")
    return cleaned


def state_path(state_dir: Path, session_id: str) -> Path:
    return state_dir / f"{sanitize_session_id(session_id)}.json"


def load_mission_state(state_dir: Path, session_id: str) -> MissionState | None:
    path = state_path(state_dir, session_id)
    if not path.exists():
        return None
    return MissionState.from_json(path.read_text(encoding="utf-8"))


def save_mission_state(state_dir: Path, session_id: str, state: MissionState) -> Path:
    state_dir.mkdir(parents=True, exist_ok=True)
    path = state_path(state_dir, session_id)
    path.write_text(state.to_json(), encoding="utf-8")
    return path


def write_heartbeat_log(path: Path, *, state: MissionState, socket_id: str | None, verdict: dict[str, Any] | None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        f"## heartbeat {utc_now()}",
        f"mission: {state.mission}",
        f"session: {state.session}",
        f"status: {state.status}",
        f"socket: {socket_id or ''}",
        f"ticks_used: {state.ticks_used}",
    ]
    if verdict is not None:
        lines.append(f"judge_done: {verdict.get('done')}")
        lines.append(f"judge_status: {verdict.get('status', '')}")
        lines.append(f"judge_reason: {verdict.get('reason', '')}")
    with path.open("a", encoding="utf-8") as handle:
        handle.write("\n".join(lines) + "\n")


def load_ledger_rows(ledger_path: Path) -> list[dict[str, Any]]:
    if not ledger_path.exists():
        return []
    try:
        data = json.loads(ledger_path.read_text(encoding="utf-8"))
    except Exception:
        return []
    if isinstance(data, dict):
        rows = data.get("sockets") or data.get("rows") or []
    else:
        rows = data
    if not isinstance(rows, list):
        return []
    out: list[dict[str, Any]] = []
    for row in rows:
        if isinstance(row, dict):
            out.append(row)
    return out


def socket_is_open(row: dict[str, Any], closed_sockets: set[str]) -> bool:
    socket_id = str(row.get("id") or row.get("socket") or "").strip()
    if not socket_id or socket_id in closed_sockets:
        return False
    status = str(row.get("status") or "").strip().lower()
    if status in TERMINAL_SOCKET_STATUSES:
        return False
    return True


def select_next_socket(rows: list[dict[str, Any]], closed_sockets: set[str]) -> dict[str, Any] | None:
    for row in rows:
        if socket_is_open(row, closed_sockets):
            return row
    return None


def socket_label(row: dict[str, Any]) -> str:
    socket_id = str(row.get("id") or row.get("socket") or "unknown").strip()
    owner_target = str(row.get("owner_target") or row.get("socket") or "").strip()
    if owner_target:
        return f"{socket_id}: {owner_target}"
    return socket_id


def sync_goal_state(
    *,
    goal_state_dir: Path,
    session: str,
    mission: str,
    socket_label_text: str | None,
    max_turns: int,
) -> GoalState:
    goal = load_goal_state(goal_state_dir, session)
    if goal is None:
        goal = GoalState.new(mission, max_turns=max_turns)
    else:
        goal.goal = mission
        goal.max_turns = max_turns
    goal.status = "active"
    goal.paused_reason = None
    goal.turns_used = 0
    if socket_label_text and socket_label_text not in goal.subgoals:
        goal.subgoals.append(socket_label_text)
    goal.last_turn_at = time.time()
    save_goal_state(goal_state_dir, session, goal)
    return goal


def run_cmd(cmd: list[str]) -> tuple[int, str, str]:
    proc = subprocess.run(cmd, capture_output=True, text=True)
    return proc.returncode, proc.stdout, proc.stderr


def load_json_response(path: Path | None) -> dict[str, Any] | None:
    if path is None or not path.exists():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None
    return data if isinstance(data, dict) else None


def evaluate_tick(
    *,
    lean_file: Path | None,
    response_file: Path | None,
    baseline_debt: int | None,
    gate_policy: Path | None,
    build_target: str | None,
) -> dict[str, Any]:
    verdict: dict[str, Any] = {
        "build": {"ran": False, "returncode": None, "stdout": "", "stderr": ""},
        "gate": {"ran": False, "returncode": None, "stdout": "", "stderr": ""},
        "judge": {"ran": False, "returncode": None, "stdout": "", "stderr": ""},
        "status": "continue",
        "reason": "",
    }

    if build_target:
        verdict["build"]["ran"] = True
        cmd = ["lake", "build", build_target]
        rc, out, err = run_cmd(cmd)
        verdict["build"].update({"returncode": rc, "stdout": out, "stderr": err})
        if rc != 0:
            verdict["status"] = "blocked"
            verdict["reason"] = f"build failed for {build_target}: {err[:300].strip()}"
            return verdict

    if gate_policy is not None:
        verdict["gate"]["ran"] = True
        cmd = ["python3", "tools/quality/check_closure_debt_gate.py", "--policy", str(gate_policy)]
        rc, out, err = run_cmd(cmd)
        verdict["gate"].update({"returncode": rc, "stdout": out, "stderr": err})
        if rc != 0:
            verdict["status"] = "blocked"
            verdict["reason"] = f"closure gate failed: {err[:300].strip() or out[:300].strip()}"
            return verdict

    if lean_file is not None and response_file is not None and baseline_debt is not None:
        verdict["judge"]["ran"] = True
        cmd = [
            "python3",
            "tools/quality/mission_judge.py",
            str(lean_file),
            str(response_file),
            str(baseline_debt),
        ]
        rc, out, err = run_cmd(cmd)
        verdict["judge"].update({"returncode": rc, "stdout": out, "stderr": err})
        verdict["judge_json"] = load_json_response(response_file)
        try:
            parsed = json.loads(out) if out.strip() else {}
        except Exception:
            parsed = {}
        if rc == 0:
            verdict["status"] = "done"
            verdict["reason"] = str(parsed.get("reason") or "all checks pass")
        elif rc == 2:
            verdict["status"] = "blocked"
            verdict["reason"] = str(parsed.get("reason") or err[:300].strip() or "blocked")
        else:
            verdict["status"] = "continue"
            verdict["reason"] = str(parsed.get("reason") or "continue")
        return verdict

    verdict["reason"] = "tick prepared"
    return verdict


def build_packet(
    *,
    mission: MissionState,
    goal: GoalState | None,
    socket_row: dict[str, Any] | None,
    verdict: dict[str, Any] | None,
    open_count: int,
) -> dict[str, Any]:
    goal_prompt = goal.continuation_prompt() if goal is not None else ""
    return {
        "schema": "info_geometry.mission_loop_packet.v1",
        "mission": {
            "session": mission.session,
            "mission": mission.mission,
            "mode": mission.mode,
            "scope": mission.scope,
            "status": mission.status,
            "ticks_used": mission.ticks_used,
            "created_at": mission.created_at,
            "last_tick_at": mission.last_tick_at,
        },
        "socket": {
            "id": (socket_row or {}).get("id") or (socket_row or {}).get("socket") or "",
            "title": socket_label(socket_row) if socket_row else "",
            "owner_class": (socket_row or {}).get("owner_class") or "",
            "owner_target": (socket_row or {}).get("owner_target") or "",
            "status": (socket_row or {}).get("status") or "",
        },
        "counts": {
            "open_sockets": open_count,
            "closed_sockets": len(mission.closed_sockets),
        },
        "goal_prompt": goal_prompt,
        "verdict": verdict or {},
        "recommended_commands": {
            "lean": f"lake env lean {socket_row.get('lean_file', '')}" if socket_row else "",
            "build": f"lake build {mission.build_target}" if mission.build_target else "",
            "gate": f"python3 tools/quality/check_closure_debt_gate.py --policy {mission.gate_policy}",
            "judge": (
                "python3 tools/quality/mission_judge.py "
                "<lean_file> <response_file> <baseline_debt_count>"
            ),
        },
    }


def mission_set(args: argparse.Namespace) -> int:
    mission_text = " ".join(args.mission).strip() or DEFAULT_MISSION
    state = MissionState.new(
        args.session,
        mission=mission_text,
        scope=args.scope,
        ledger=str(args.ledger),
        gate_policy=str(args.gate_policy),
        build_target=args.build_target,
        heartbeat_log=str(args.heartbeat_log),
    )
    save_mission_state(args.state_dir, args.session, state)
    sync_goal_state(
        goal_state_dir=args.goal_state_dir,
        session=args.session,
        mission=mission_text,
        socket_label_text=None,
        max_turns=args.max_turns,
    )
    print(state.to_json(), end="")
    return 0


def mission_status(args: argparse.Namespace) -> int:
    state = load_mission_state(args.state_dir, args.session)
    if state is None:
        print(json.dumps({"status": "missing"}, indent=2))
        return 1
    goal = load_goal_state(args.goal_state_dir, args.session)
    rows = load_ledger_rows(Path(state.ledger))
    packet = build_packet(
        mission=state,
        goal=goal,
        socket_row=None,
        verdict=None,
        open_count=sum(1 for row in rows if socket_is_open(row, set(state.closed_sockets))),
    )
    print(json.dumps(packet, ensure_ascii=False, indent=2))
    return 0


def mission_pause(args: argparse.Namespace) -> int:
    state = load_mission_state(args.state_dir, args.session)
    if state is None:
        print("error: no mission state for session", file=sys.stderr)
        return 2
    state.status = "paused"
    state.notes.append(args.reason)
    state.last_tick_at = time.time()
    save_mission_state(args.state_dir, args.session, state)

    goal = load_goal_state(args.goal_state_dir, args.session)
    if goal is not None:
        goal.status = "paused"
        goal.paused_reason = args.reason
        goal.last_turn_at = time.time()
        save_goal_state(args.goal_state_dir, args.session, goal)
    print("mission paused")
    return 0


def mission_resume(args: argparse.Namespace) -> int:
    state = load_mission_state(args.state_dir, args.session)
    if state is None:
        print("error: no mission state for session", file=sys.stderr)
        return 2
    state.status = "active"
    state.last_tick_at = time.time()
    save_mission_state(args.state_dir, args.session, state)

    goal = load_goal_state(args.goal_state_dir, args.session)
    if goal is not None and goal.status != "cleared":
        goal.status = "active"
        goal.paused_reason = None
        goal.last_turn_at = time.time()
        save_goal_state(args.goal_state_dir, args.session, goal)
    print("mission resumed")
    return 0


def mission_clear(args: argparse.Namespace) -> int:
    state = load_mission_state(args.state_dir, args.session)
    if state is not None:
        state.status = "cleared"
        state.notes.append("cleared by user")
        state.last_tick_at = time.time()
        save_mission_state(args.state_dir, args.session, state)

    goal = load_goal_state(args.goal_state_dir, args.session)
    if goal is not None:
        goal.status = "cleared"
        goal.paused_reason = "cleared by user"
        goal.last_turn_at = time.time()
        save_goal_state(args.goal_state_dir, args.session, goal)
    print("mission cleared")
    return 0


def mission_heartbeat(args: argparse.Namespace) -> int:
    state = load_mission_state(args.state_dir, args.session)
    if state is None:
        print("error: no mission state for session", file=sys.stderr)
        return 2
    if state.status != "active":
        print(f"error: mission is {state.status}, not active", file=sys.stderr)
        return 2

    rows = load_ledger_rows(Path(state.ledger))
    closed = set(state.closed_sockets)
    socket_row = None
    if state.current_socket_id:
        for row in rows:
            row_id = str(row.get("id") or row.get("socket") or "").strip()
            if row_id == state.current_socket_id and socket_is_open(row, closed):
                socket_row = row
                break
    if socket_row is None:
        socket_row = select_next_socket(rows, closed)

    socket_id = str(socket_row.get("id") or socket_row.get("socket") or "").strip() if socket_row else None
    socket_title = socket_label(socket_row) if socket_row else None

    goal = sync_goal_state(
        goal_state_dir=args.goal_state_dir,
        session=args.session,
        mission=state.mission,
        socket_label_text=socket_title,
        max_turns=args.max_turns,
    )

    verdict = evaluate_tick(
        lean_file=args.lean_file,
        response_file=args.response_file,
        baseline_debt=args.baseline_debt,
        gate_policy=args.gate_policy if args.run_gate else None,
        build_target=args.build_target if args.run_build else None,
    )

    if verdict["status"] == "done" and socket_id:
        if socket_id not in state.closed_sockets:
            state.closed_sockets.append(socket_id)
        state.current_socket_id = None
        state.current_socket_title = None
    elif socket_id:
        state.current_socket_id = socket_id
        state.current_socket_title = socket_title

    state.ticks_used += 1
    state.last_tick_at = time.time()
    if verdict["status"] == "blocked":
        state.status = "paused"
        state.notes.append(verdict.get("reason", "blocked"))
    save_mission_state(args.state_dir, args.session, state)

    open_count = sum(1 for row in rows if socket_is_open(row, set(state.closed_sockets)))
    packet = build_packet(
        mission=state,
        goal=goal,
        socket_row=socket_row,
        verdict=verdict,
        open_count=open_count,
    )
    write_heartbeat_log(Path(state.heartbeat_log), state=state, socket_id=socket_id, verdict=verdict)
    print(json.dumps(packet, ensure_ascii=False, indent=2))
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--session", default="default", help="mission session id")
    parser.add_argument("--state-dir", type=Path, default=DEFAULT_STATE_DIR)
    parser.add_argument("--goal-state-dir", type=Path, default=DEFAULT_GOAL_STATE_DIR)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER)
    parser.add_argument("--gate-policy", type=Path, default=DEFAULT_GATE_POLICY)
    parser.add_argument("--heartbeat-log", type=Path, default=DEFAULT_HEARTBEAT_LOG)
    parser.add_argument("--build-target", default=DEFAULT_BUILD_TARGET)
    parser.add_argument("--scope", default="")
    parser.add_argument("--max-turns", type=int, default=1)
    parser.add_argument("--run-build", action="store_true", help="Run the target build during heartbeat")
    parser.add_argument("--run-gate", action="store_true", help="Run the closure debt gate during heartbeat")
    parser.add_argument("--lean-file", type=Path, help="Lean file to judge on this tick")
    parser.add_argument("--response-file", type=Path, help="Response file to judge on this tick")
    parser.add_argument("--baseline-debt", type=int, help="Baseline debt count for the judge")

    sub = parser.add_subparsers(dest="command", required=True)

    p_set = sub.add_parser("set", help="start or reset the eternal mission")
    p_set.add_argument("mission", nargs=argparse.REMAINDER)
    p_set.set_defaults(func=mission_set)

    p_status = sub.add_parser("status", help="show mission state")
    p_status.set_defaults(func=mission_status)

    p_pause = sub.add_parser("pause", help="pause the mission")
    p_pause.add_argument("--reason", default="paused by user")
    p_pause.set_defaults(func=mission_pause)

    p_resume = sub.add_parser("resume", help="resume the mission")
    p_resume.set_defaults(func=mission_resume)

    p_clear = sub.add_parser("clear", help="clear the mission")
    p_clear.set_defaults(func=mission_clear)

    p_hb = sub.add_parser("heartbeat", help="run one mission heartbeat tick")
    p_hb.set_defaults(func=mission_heartbeat)

    return parser.parse_args()


def main() -> int:
    args = parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
