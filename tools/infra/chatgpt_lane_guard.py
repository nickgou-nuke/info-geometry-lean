#!/usr/bin/env python3
"""Shared single-flight guard for ChatGPT browser lanes.

This module is intentionally independent from aiClaw's REST client so direct
browser-harness scripts can share the same queue/busy marker discipline as
`tools/infra/aiclaw_chat.py` without importing the localBridge transport.
"""

from __future__ import annotations

import datetime as dt
import fcntl
import json
import os
import re
import uuid
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Iterator


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_QUEUE_ROOT = REPO_ROOT / "tmp" / "aiclaw_queue"
DEFAULT_PLATFORM = "chatgpt"


def utc_now() -> str:
    return dt.datetime.now(dt.UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def safe_platform_name(platform: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", platform).strip("_") or "platform"


def queue_paths(queue_root: Path, platform: str) -> dict[str, Path]:
    root = queue_root / safe_platform_name(platform)
    return {
        "root": root,
        "lock": root / "lane.lock",
        "busy": root / "busy.json",
        "released": root / "released",
    }


def ensure_queue_dirs(paths: dict[str, Path]) -> None:
    paths["root"].mkdir(parents=True, exist_ok=True)
    paths["released"].mkdir(parents=True, exist_ok=True)


def read_json_file(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {}
    return value if isinstance(value, dict) else {}


def write_json_file(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def resolve_queue_root(queue_root: str | Path | None = None) -> Path:
    raw = queue_root or os.environ.get("AICLAW_QUEUE_ROOT") or DEFAULT_QUEUE_ROOT
    path = Path(raw)
    return path if path.is_absolute() else REPO_ROOT / path


@contextmanager
def browser_chatgpt_lane(
    *,
    source: str,
    platform: str = DEFAULT_PLATFORM,
    queue_root: str | Path | None = None,
    prompt_chars: int | None = None,
    reason: str = "browser_harness_send",
) -> Iterator[dict[str, Any]]:
    """Hold the shared ChatGPT lane while a direct browser-harness sender runs.

    Normal completion archives and removes `busy.json`.  Exceptions leave
    `busy.json` in place because the prompt may have reached the browser and
    must be inspected read-only before reuse.
    """
    paths = queue_paths(resolve_queue_root(queue_root), platform)
    ensure_queue_dirs(paths)
    job_id = f"{dt.datetime.now(dt.UTC).strftime('%Y%m%dT%H%M%SZ')}_{os.getpid()}_{uuid.uuid4().hex[:8]}"

    with paths["lock"].open("a+", encoding="utf-8") as lock_file:
        try:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise RuntimeError(
                f"CHATGPT_LANE_BUSY: queue lock is held for platform={platform!r}"
            ) from exc

        try:
            existing_busy = read_json_file(paths["busy"])
            if existing_busy:
                raise RuntimeError(
                    "CHATGPT_LANE_BUSY: unresolved busy marker exists; "
                    f"busy_file={paths['busy']}; "
                    f"job_id={existing_busy.get('job_id')}; "
                    f"reason={existing_busy.get('reason') or existing_busy.get('hold_reason')}; "
                    f"release_command=python3 tools/infra/aiclaw_chat.py queue-release --platform {platform}"
                )

            busy = {
                "enabled": True,
                "held": True,
                "job_id": job_id,
                "platform": platform,
                "queue_root": str(paths["root"]),
                "source": source,
                "reason": reason,
                "pid": os.getpid(),
                "started_at": utc_now(),
                "prompt_chars": prompt_chars,
                "release_command": f"python3 tools/infra/aiclaw_chat.py queue-release --platform {platform}",
            }
            write_json_file(paths["busy"], busy)
            try:
                yield busy
            except BaseException as exc:
                write_json_file(paths["busy"], {
                    **busy,
                    "finished_at": utc_now(),
                    "reason": "exception_during_browser_harness",
                    "error": str(exc),
                })
                raise
            else:
                released = {
                    **busy,
                    "held": False,
                    "released_at": utc_now(),
                    "release_reason": "browser_harness_final_response_recorded",
                }
                write_json_file(paths["released"] / f"{job_id}.json", released)
                if paths["busy"].exists():
                    paths["busy"].unlink()
        finally:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)
