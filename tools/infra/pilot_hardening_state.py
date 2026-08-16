#!/usr/bin/env python3
"""Track superorganism pilot cleanliness and decide when to switch to hard mode."""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
_SRC = REPO_ROOT / "src"
if str(_SRC) not in sys.path:
    sys.path.insert(0, str(_SRC))
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from igf.common.time_utils import utc_now_iso

DEFAULT_STATE_PATH = REPO_ROOT / "reports" / "verification" / "pilot" / "state" / "superorganism_pilot_state.json"
utc_now = utc_now_iso


def _to_int(value: Any, fallback: int) -> int:
    try:
        return int(value)
    except Exception:
        return fallback


def _as_bool(value: object) -> bool:
    if isinstance(value, bool):
        return value
    if not isinstance(value, str):
        return False
    return value.strip().lower() in {"1", "true", "yes", "y", "on"}


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}
    if isinstance(payload, dict):
        return payload
    return {}


def _safe_get(mapping: Any, key: str, default: Any) -> Any:
    if isinstance(mapping, dict):
        return mapping.get(key, default)
    return default


def _load_state(path: Path) -> dict[str, Any]:
    payload = _load_json(path)
    return {
        "version": 1,
        "clean_streak": _to_int(payload.get("clean_streak"), 0),
        "runs": payload.get("runs") if isinstance(payload.get("runs"), list) else [],
        "updated_at": str(payload.get("updated_at", "")),
        "notes": payload.get("notes") if isinstance(payload.get("notes"), list) else [],
    }


def _write_state(path: Path, state: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    state["version"] = 1
    state["updated_at"] = utc_now()
    path.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _read_summary(path: Path) -> tuple[bool, dict[str, Any]]:
    payload = _load_json(path)
    if not payload:
        return False, {"reason": "pilot_report_missing"}
    summary = payload.get("summary") if isinstance(payload, dict) else None
    if not isinstance(summary, dict):
        return False, {"reason": "pilot_report_missing_summary"}
    failed_hard = _to_int(summary.get("failed_hard"), 1)
    failed_soft = _to_int(summary.get("failed_soft"), 1)
    return failed_hard == 0 and failed_soft == 0, {
        "failed_hard": failed_hard,
        "failed_soft": failed_soft,
    }


def _is_clean(run_exit_code: int, report_path: Path | None) -> bool:
    if run_exit_code != 0:
        return False
    if report_path is None:
        return False
    clean, metrics = _read_summary(report_path)
    if not clean:
        return False
    return True


def _record_run(
    state: dict[str, Any],
    *,
    run_id: str,
    run_exit_code: int,
    clean: bool,
    report_metrics: dict[str, Any],
    max_history: int,
) -> None:
    history = [row for row in state.get("runs", []) if isinstance(row, dict)]
    row = {
        "run_id": run_id,
        "exit_code": int(run_exit_code),
        "clean": bool(clean),
        "timestamp": utc_now(),
        "metrics": report_metrics,
    }
    history.append(row)
    if len(history) > max_history:
        history = history[-max_history:]
    state["runs"] = history
    state["clean_streak"] = _to_int(
        (state.get("clean_streak")),
        0,
    )
    if clean:
        state["clean_streak"] = _to_int(state.get("clean_streak"), 0) + 1
    else:
        state["clean_streak"] = 0


def _decide_mode(*, clean_streak: int, threshold: int, force_hard: bool) -> bool:
    return bool(force_hard or (clean_streak >= threshold))


def build_hardening_note_section(payload: dict[str, Any]) -> list[str]:
    """Render canonical hardening progress lines for summary artifacts."""

    hard_mode = bool(payload.get("hard_mode", False))
    clean_streak = _to_int(payload.get("clean_streak"), 0)
    threshold = _to_int(payload.get("hard_mode_threshold"), 4)
    clean = bool(payload.get("clean", False))
    continue_on_error = bool(payload.get("continue_on_error", True))
    run_id = str(payload.get("run_id", "")).strip()

    mode = "hard" if hard_mode else "soft"
    run_status = "clean" if clean else "failed"
    soft_to_hard = bool(clean_streak >= threshold)
    streak_delta = "toward" if clean else "against"

    section = [
        "",
        "## Superorganism Pilot Hardening Note",
    ]
    if run_id:
        section.append(f"- run id: {run_id}")
    section.extend(
        [
            f"- run status: {run_status}",
            f"- hard-mode streak: {clean_streak}/{threshold}",
            f"- streak progress: {streak_delta}",
            f"- mode now: {mode}",
            f"- continue-on-error: {str(continue_on_error).lower()}",
        ]
    )
    if soft_to_hard and run_status == "clean":
        section.append("- hard-mode threshold reached this run.")
    return section


def _append_markdown(path: Path | None, payload: dict[str, Any]) -> None:
    if not path:
        return
    section = build_hardening_note_section(payload)
    if not section:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write("\n".join(section) + "\n")


def _emit_outputs(path: Path | None, payload: dict[str, Any]) -> None:
    if not path:
        return
    lines = [
        f"hard_mode={str(payload['hard_mode']).lower()}",
        f"clean_streak={int(payload['clean_streak'])}",
        f"hard_mode_threshold={int(payload['hard_mode_threshold'])}",
        f"continue_on_error={str(not payload['hard_mode']).lower()}",
        f"policy_path={payload['policy_path']}",
    ]
    if payload.get("run_id"):
        lines.append(f"run_id={payload['run_id']}")
    with path.open("a", encoding="utf-8") as handle:
        handle.write("\n".join(lines) + "\n")


def _emit_json(path: Path | None, payload: dict[str, Any]) -> None:
    if not path:
        return
    lines = {
        "hard_mode": bool(payload["hard_mode"]),
        "clean_streak": int(payload["clean_streak"]),
        "hard_mode_threshold": int(payload["hard_mode_threshold"]),
        "policy_path": str(payload["policy_path"]),
        "continue_on_error": bool(payload["continue_on_error"]),
        "clean": bool(payload.get("clean", False)),
        "run_id": str(payload.get("run_id", "")),
    }
    path.write_text(json.dumps(lines, sort_keys=True, indent=2) + "\n", encoding="utf-8")


def action_read(args: argparse.Namespace) -> dict[str, Any]:
    state = _load_state(args.state)
    threshold = max(1, int(args.hard_mode_threshold))
    clean_streak = _to_int(state.get("clean_streak"), 0)
    hard_mode = _decide_mode(
        clean_streak=clean_streak,
        threshold=threshold,
        force_hard=_as_bool(args.force_hard),
    )
    policy_path = (
        args.hard_policy_path
        if hard_mode
        else args.soft_policy_path
    )
    payload = {
        "hard_mode": hard_mode,
        "clean_streak": clean_streak,
        "hard_mode_threshold": threshold,
        "policy_path": policy_path,
        "continue_on_error": not hard_mode,
        "run_id": str(args.run_id or ""),
        "source": "read",
    }
    _emit_outputs(args.github_output, payload)
    _emit_json(args.json_out, payload)
    return payload


def action_update(args: argparse.Namespace) -> dict[str, Any]:
    state = _load_state(args.state)
    report_path = Path(args.pilot_report) if args.pilot_report else None
    clean, metrics = _read_summary(report_path) if report_path else (False, {})
    if not args.pilot_report or not Path(args.pilot_report).exists():
        metrics = {"reason": "pilot_report_missing", "failed_hard": 1, "failed_soft": 1}

    run_exit_code = _to_int(args.exit_code, 0)
    is_clean = _is_clean(run_exit_code, report_path)
    if not clean and report_path:
        clean = False
    _record_run(
        state,
        run_id=str(args.run_id or ""),
        run_exit_code=run_exit_code,
        clean=is_clean,
        report_metrics=metrics,
        max_history=max(1, int(args.max_history)),
    )
    threshold = max(1, int(args.hard_mode_threshold))
    hard_mode = _decide_mode(
        clean_streak=state["clean_streak"],
        threshold=threshold,
        force_hard=_as_bool(args.force_hard),
    )
    policy_path = args.hard_policy_path if hard_mode else args.soft_policy_path
    _write_state(args.state, state)
    payload = {
        "hard_mode": hard_mode,
        "clean_streak": state["clean_streak"],
        "hard_mode_threshold": threshold,
        "policy_path": policy_path,
        "continue_on_error": not hard_mode,
        "clean": is_clean,
        "run_id": str(args.run_id or ""),
        "source": "update",
    }
    _emit_outputs(args.github_output, payload)
    _emit_json(args.json_out, payload)
    _append_markdown(Path(args.markdown_out) if args.markdown_out else None, payload)
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", type=Path, default=DEFAULT_STATE_PATH, help="State file path")
    parser.add_argument("--hard-policy-path", type=str, default="tools/infra/verification_policy_pilot_hard.yaml")
    parser.add_argument("--soft-policy-path", type=str, default="tools/infra/verification_policy_pilot.yaml")
    parser.add_argument("--hard-mode-threshold", type=int, default=4)
    parser.add_argument("--force-hard", type=str, default="false")
    parser.add_argument("--action", choices=["read", "update"], default="read")
    parser.add_argument("--pilot-report", type=str, default="")
    parser.add_argument("--run-id", type=str, default="")
    parser.add_argument("--exit-code", type=int, default=0)
    parser.add_argument("--max-history", type=int, default=20)
    parser.add_argument("--github-output", type=Path, help="Optional $GITHUB_OUTPUT style file")
    parser.add_argument("--json-out", type=Path, help="Optional JSON output file")
    parser.add_argument(
        "--markdown-out",
        type=Path,
        help="Optional markdown artifact path for hardening streak note.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.action == "read":
        payload = action_read(args)
    else:
        payload = action_update(args)
    print(json.dumps(payload, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
