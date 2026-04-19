#!/usr/bin/env python3
"""Rate-limit explicit Gemini CLI use for the theorem-factory workflow.

This guard does not run Gemini. It records explicit operator-approved usage so
agents do not silently poll or loop through Gemini CLI.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
import time
from pathlib import Path
from typing import Any


DEFAULT_STATE = Path("artifacts/gemini_cli_guard/state.json")
DEFAULT_MIN_INTERVAL_SECONDS = 1800
DEFAULT_MAX_CALLS_PER_DAY = 12
DEFAULT_JITTER_SECONDS = 900


def load_state(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {"schema": "gemini_cli_guard.v1", "events": []}
    state = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(state, dict):
        raise ValueError(f"state is not a JSON object: {path}")
    events = state.get("events", [])
    if not isinstance(events, list):
        raise ValueError(f"state events is not a list: {path}")
    state["events"] = [event for event in events if isinstance(event, dict)]
    return state


def write_state(path: Path, state: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def recent_events(state: dict[str, Any], now: float, window_seconds: int) -> list[dict[str, Any]]:
    cutoff = now - window_seconds
    return [event for event in state.get("events", []) if float(event.get("time", 0)) >= cutoff]


def evaluate(
    state: dict[str, Any],
    *,
    now: float,
    min_interval_seconds: int,
    max_calls_per_day: int,
    jitter_seconds: int,
) -> tuple[bool, str, int]:
    if min_interval_seconds < 0:
        return False, "invalid policy: min_interval_seconds must be non-negative", 0
    if jitter_seconds < 0:
        return False, "invalid policy: jitter_seconds must be non-negative", 0
    if max_calls_per_day < 1:
        return False, "invalid policy: max_calls_per_day must be at least 1", 0

    events = sorted(state.get("events", []), key=lambda item: float(item.get("time", 0)))
    last = events[-1] if events else None
    if last:
        required_interval = min_interval_seconds + int(last.get("jitter_seconds", 0))
        elapsed = now - float(last.get("time", 0))
        if elapsed < required_interval:
            wait = int(required_interval - elapsed)
            return False, f"irregular dream interval not elapsed; wait {wait}s", wait

    day_events = recent_events(state, now, 24 * 60 * 60)
    if len(day_events) >= max_calls_per_day:
        oldest = min(float(event.get("time", 0)) for event in day_events)
        wait = int((oldest + 24 * 60 * 60) - now)
        return False, f"daily Gemini CLI limit reached; wait {max(wait, 0)}s", max(wait, 0)

    return True, "allowed", 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", type=Path, default=DEFAULT_STATE)
    parser.add_argument("--min-interval-seconds", type=int, default=DEFAULT_MIN_INTERVAL_SECONDS)
    parser.add_argument("--max-calls-per-day", type=int, default=DEFAULT_MAX_CALLS_PER_DAY)
    parser.add_argument("--jitter-seconds", type=int, default=DEFAULT_JITTER_SECONDS)
    parser.add_argument("--reason", default="explicit operator request")
    parser.add_argument("--operator", default="goutev")
    parser.add_argument("--now", type=float, help=argparse.SUPPRESS)
    parser.add_argument("--check", action="store_true", help="Only check allowance; do not record usage.")
    parser.add_argument("--json", action="store_true", help="Emit JSON status.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    now = args.now if args.now is not None else time.time()
    try:
        state = load_state(args.state)
    except Exception as exc:  # noqa: BLE001 - guard must fail closed.
        payload = {
            "allowed": False,
            "reason": f"invalid guard state: {exc}",
            "wait_seconds": 0,
            "state": str(args.state),
            "check_only": args.check,
        }
        if args.json:
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            print(f"DENY: {payload['reason']}", file=sys.stderr)
        return 2

    allowed, reason, wait_seconds = evaluate(
        state,
        now=now,
        min_interval_seconds=args.min_interval_seconds,
        max_calls_per_day=args.max_calls_per_day,
        jitter_seconds=args.jitter_seconds,
    )

    if allowed and not args.check:
        jitter = random.randint(0, max(args.jitter_seconds, 0))
        events = list(state.get("events", []))
        events.append(
            {
                "time": now,
                "iso_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now)),
                "jitter_seconds": jitter,
                "operator": args.operator,
                "reason": args.reason,
            }
        )
        state = {
            "schema": "gemini_cli_guard.v1",
            "updated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now)),
            "policy": {
                "min_interval_seconds": args.min_interval_seconds,
                "max_calls_per_day": args.max_calls_per_day,
                "jitter_seconds": args.jitter_seconds,
                "explicit_operator_only": True,
                "auto_route": False,
                "mode": "irregular_dreaming_sidecar",
            },
            "events": events[-200:],
        }
        write_state(args.state, state)

    payload = {
        "allowed": allowed,
        "reason": reason,
        "wait_seconds": wait_seconds,
        "state": str(args.state),
        "check_only": args.check,
        "mode": "irregular_dreaming_sidecar",
    }
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"{'ALLOW' if allowed else 'DENY'}: {reason}")
    return 0 if allowed else 2


if __name__ == "__main__":
    raise SystemExit(main())
