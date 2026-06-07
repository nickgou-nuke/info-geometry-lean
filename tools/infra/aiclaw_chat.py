#!/usr/bin/env python3
"""CLI bridge for the local aiClaw AI-chat REST API.

This uses the repo-local clawBot client and talks to the aiClaw localBridge
server, not the public OpenAI API. It is intended for controlled proof-review
calls where we must poll tab/login state before sending a prompt.
"""

from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import hashlib
import json
import os
import re
import sys
import time
import uuid
from dataclasses import asdict, is_dataclass
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
CLAWBOT_ROOT = REPO_ROOT / "aihub" / "localBridge" / "clawBotCli"
DEFAULT_BASE_URL = "http://127.0.0.1:10088"
DEFAULT_PLATFORM = "chatgpt"
DEFAULT_QUEUE_ROOT = REPO_ROOT / "tmp" / "aiclaw_queue"
DEFAULT_QUEUE_STALE_SECONDS = 900.0
SENSITIVE_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("private_key", re.compile(r"-----BEGIN [A-Z ]*PRIVATE KEY-----")),
    ("openai_key", re.compile(r"\bsk-[A-Za-z0-9_-]{20,}\b")),
    ("github_token", re.compile(r"\bgh[pousr]_[A-Za-z0-9_]{20,}\b")),
    ("aws_access_key", re.compile(r"\bAKIA[0-9A-Z]{16}\b")),
    ("password_assignment", re.compile(r"(?i)\b(password|passwd|secret|token|api[_-]?key)\s*[:=]\s*\S+")),
)

if str(CLAWBOT_ROOT) not in sys.path:
    sys.path.insert(0, str(CLAWBOT_ROOT))

try:
    from clawbot import ClawBotClient
    from clawbot.errors import ClawBotError
except Exception as exc:  # pragma: no cover - import failure is environment setup.
    raise SystemExit(f"failed to import repo-local clawbot client: {exc}") from exc

try:
    from tools.infra.agent_message_ledger import record_message
except Exception:  # pragma: no cover - observation must never block sends.
    record_message = None


def jsonable(value: Any) -> Any:
    if is_dataclass(value):
        return jsonable(asdict(value))
    if isinstance(value, dict):
        return {str(k): jsonable(v) for k, v in value.items()}
    if isinstance(value, list):
        return [jsonable(v) for v in value]
    return value


def emit_json(value: Any) -> None:
    print(json.dumps(jsonable(value), indent=2, sort_keys=True))


def utc_now() -> str:
    return dt.datetime.now(dt.UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_utc_timestamp(value: Any) -> dt.datetime | None:
    if not isinstance(value, str) or not value:
        return None
    try:
        parsed = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return None
    if parsed.tzinfo is None:
        return parsed.replace(tzinfo=dt.UTC)
    return parsed.astimezone(dt.UTC)


def seconds_since(value: Any, *, now: dt.datetime | None = None) -> float | None:
    timestamp = parse_utc_timestamp(value)
    if timestamp is None:
        return None
    current = now or dt.datetime.now(dt.UTC)
    return max(0.0, (current - timestamp).total_seconds())


def pid_alive(pid: Any) -> bool | None:
    try:
        pid_int = int(pid)
    except (TypeError, ValueError):
        return None
    if pid_int <= 0:
        return False
    try:
        os.kill(pid_int, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def safe_platform_name(platform: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", platform).strip("_") or "platform"


def write_json_file(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(jsonable(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def read_json_file(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {}
    return value if isinstance(value, dict) else {}


def platform_queue_dir(queue_root: Path, platform: str) -> Path:
    return queue_root / safe_platform_name(platform)


def queue_paths(queue_root: Path, platform: str) -> dict[str, Path]:
    root = platform_queue_dir(queue_root, platform)
    return {
        "root": root,
        "lock": root / "lane.lock",
        "busy": root / "busy.json",
        "queued": root / "queued",
        "active": root / "active",
        "done": root / "done",
        "failed": root / "failed",
        "released": root / "released",
    }


def ensure_queue_dirs(paths: dict[str, Path]) -> None:
    for key in ("queued", "active", "done", "failed", "released"):
        paths[key].mkdir(parents=True, exist_ok=True)


def queue_recovery_guidance(queue_root: Path, platform: str) -> dict[str, Any]:
    release_command = f"python3 tools/infra/aiclaw_chat.py queue-release --platform {platform}"
    prune_active_command = f"python3 tools/infra/aiclaw_chat.py queue-prune-active --platform {platform}"
    return {
        "status_command": f"python3 tools/infra/aiclaw_chat.py queue-status --platform {platform}",
        "release_command": release_command,
        "prune_active_command": prune_active_command,
        "readback_rule": (
            "Recover the final visible answer through a read-only browser view, "
            "record the prompt hash and final answer in the work log, then run "
            f"`{release_command} --reason final_visible_answer_recorded`."
        ),
        "send_rule": "Do not send another prompt on this platform until lane_available=true.",
    }


def summarize_queue_doc(
    path: Path,
    payload: dict[str, Any],
    *,
    now: dt.datetime,
    stale_after: float,
) -> dict[str, Any]:
    started_at = payload.get("started_at") or payload.get("queued_at") or payload.get("finished_at")
    age = seconds_since(started_at, now=now)
    stale = bool(age is not None and stale_after > 0 and age >= stale_after)
    meta = payload.get("meta") if isinstance(payload.get("meta"), dict) else {}
    pid_state = pid_alive(payload.get("pid"))
    return {
        "path": str(path),
        "file": path.name,
        "job_id": payload.get("job_id"),
        "status": payload.get("status"),
        "pid": payload.get("pid"),
        "pid_alive": pid_state,
        "orphaned": pid_state is False,
        "reason": payload.get("reason") or payload.get("hold_reason") or payload.get("failure_reason"),
        "started_at": payload.get("started_at"),
        "queued_at": payload.get("queued_at"),
        "finished_at": payload.get("finished_at"),
        "age_seconds": round(age, 3) if age is not None else None,
        "stale_after_seconds": stale_after,
        "stale": stale,
        "prompt_chars": meta.get("prompt_chars"),
        "prompt_sha256": meta.get("prompt_sha256"),
    }


def queue_summary(queue_root: Path, platform: str, *, stale_after: float = DEFAULT_QUEUE_STALE_SECONDS) -> dict[str, Any]:
    paths = queue_paths(queue_root, platform)
    ensure_queue_dirs(paths)
    now = dt.datetime.now(dt.UTC)
    busy_raw = read_json_file(paths["busy"]) if paths["busy"].exists() else None
    busy = (
        summarize_queue_doc(paths["busy"], busy_raw, now=now, stale_after=stale_after)
        if busy_raw
        else None
    )
    queued_paths = sorted(paths["queued"].glob("*.json"))
    active_paths = sorted(paths["active"].glob("*.json"))
    active = [
        summarize_queue_doc(path, read_json_file(path), now=now, stale_after=stale_after)
        for path in active_paths
    ]
    queued = [
        summarize_queue_doc(path, read_json_file(path), now=now, stale_after=stale_after)
        for path in queued_paths
    ]
    guidance = queue_recovery_guidance(queue_root, platform)
    if busy:
        queue_state = "needs_readback"
        agent_action = "recover_final_visible_answer_then_release"
        lane_available = False
        readback_required = True
        hard_block = False
        state_reason = "A previous prompt may have reached the browser but no trustworthy final answer was captured."
    elif active:
        live_active = [item for item in active if item.get("pid_alive") is not False and not item.get("stale")]
        all_orphaned = all(item.get("pid_alive") is False for item in active)
        queue_state = "active" if live_active else "stale_active"
        if live_active:
            agent_action = "wait_for_active_job"
            lane_available = False
            state_reason = "A sender currently owns the lane."
        elif all_orphaned:
            agent_action = "run_queue_prune_active_or_send_one_prompt"
            lane_available = True
            state_reason = "Only dead active markers remain; no busy marker or queued job is present."
        else:
            agent_action = "inspect_or_archive_stale_active_job"
            lane_available = False
            state_reason = "Only stale active markers remain; inspect before sending."
        readback_required = False
        hard_block = False
    elif queued:
        queue_state = "queued"
        agent_action = "wait_fifo_or_increase_queue_timeout"
        lane_available = False
        readback_required = False
        hard_block = False
        state_reason = "Jobs are waiting in FIFO order."
    else:
        queue_state = "ready"
        agent_action = "send_one_prompt"
        lane_available = True
        readback_required = False
        hard_block = False
        state_reason = "No held, active, or queued job is present."
    return {
        "platform": platform,
        "queue_root": str(paths["root"]),
        "queue_state": queue_state,
        "agent_action": agent_action,
        "lane_available": lane_available,
        "readback_required": readback_required,
        "hard_block": hard_block,
        "state_reason": state_reason,
        "recovery": guidance,
        "busy": busy,
        "counts": {
            "queued": len(queued_paths),
            "active": len(active_paths),
            "done": len(list(paths["done"].glob("*.json"))),
            "failed": len(list(paths["failed"].glob("*.json"))),
            "released": len(list(paths["released"].glob("*.json"))),
        },
        "queued": queued[:20],
        "active": active[:20],
    }


TRANSPORT_PRE_SEND_ERROR_PATTERNS = (
    "failed to send message to tab",
    "receiving end does not exist",
    "message channel is closed",
    "could not establish connection",
    "extension context invalidated",
    "back/forward cache",
)


def result_error_text(result: dict[str, Any]) -> str:
    raw = result.get("raw")
    parts = [
        result.get("error"),
        raw.get("error") if isinstance(raw, dict) else None,
    ]
    return " ".join(str(part) for part in parts if part).strip()


def is_pre_send_transport_failure(result: dict[str, Any]) -> bool:
    if bool(result.get("success", False)):
        return False
    error = result_error_text(result).lower()
    return any(pattern in error for pattern in TRANSPORT_PRE_SEND_ERROR_PATTERNS)


def result_needs_lane_hold(result: dict[str, Any]) -> tuple[bool, str]:
    if is_pre_send_transport_failure(result):
        return False, ""
    content = str(result.get("content") or "").strip().lower()
    if result.get("suspect_intermediate") or content in {"thinking", "thinking..."}:
        return True, "suspect_intermediate_response"
    if not bool(result.get("success", False)):
        return True, "send_result_not_successful"
    return False, ""


def run_in_platform_queue(
    *,
    platform: str,
    queue_root: Path,
    queue_timeout: float,
    quiet: bool,
    meta: dict[str, Any],
    send_started: Any,
    hold_on_suspect: bool,
    callback: Any,
) -> dict[str, Any]:
    """Serialize browser-lane access across processes.

    The file lock handles concurrent live callers. A persistent busy marker is
    left behind when aiClaw returns an intermediate/failed result after a prompt
    may have entered the browser, forcing manual DOM readback before reuse.
    """
    paths = queue_paths(queue_root, platform)
    ensure_queue_dirs(paths)
    job_id = f"{dt.datetime.now(dt.UTC).strftime('%Y%m%dT%H%M%SZ')}_{os.getpid()}_{uuid.uuid4().hex[:8]}"
    queued_path = paths["queued"] / f"{job_id}.json"
    active_path = paths["active"] / f"{job_id}.json"
    job = {
        "job_id": job_id,
        "platform": platform,
        "status": "queued",
        "queued_at": utc_now(),
        "pid": os.getpid(),
        "meta": meta,
    }
    write_json_file(queued_path, job)

    def mark_failed(reason: str, error: str) -> None:
        failed = {
            **job,
            "status": "failed",
            "finished_at": utc_now(),
            "failure_reason": reason,
            "error": error,
        }
        write_json_file(paths["failed"] / f"{job_id}.json", failed)
        if queued_path.exists():
            queued_path.unlink()
        if active_path.exists():
            active_path.unlink()

    deadline = time.monotonic() + queue_timeout if queue_timeout > 0 else None
    paths["root"].mkdir(parents=True, exist_ok=True)
    with paths["lock"].open("a+", encoding="utf-8") as lock_file:
        while True:
            busy = read_json_file(paths["busy"]) if paths["busy"].exists() else None
            if busy:
                if deadline is not None and time.monotonic() >= deadline:
                    guidance = queue_recovery_guidance(queue_root, platform)
                    message = (
                        f"aiClaw lane {platform!r} is in needs_readback state after an unresolved prompt; "
                        f"busy_file={paths['busy']}; release with "
                        f"`{guidance['release_command']}` after read-only final-answer recovery. "
                        "This is a recovery-required queue state, not evidence that the provider is blocked."
                    )
                    mark_failed("queue_timeout_busy", message)
                    raise TimeoutError(message)
                if not quiet:
                    print(
                        f"queue waiting platform={platform} busy_job={busy.get('job_id')} "
                        f"reason={busy.get('reason')}",
                        file=sys.stderr,
                    )
                time.sleep(1)
                continue
            try:
                fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                queued_files = sorted(paths["queued"].glob("*.json"))
                if queued_files and queued_files[0] != queued_path:
                    fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)
                    if deadline is not None and time.monotonic() >= deadline:
                        message = (
                            f"timed out waiting for aiClaw lane queue platform={platform!r}; "
                            f"oldest_queued={queued_files[0].name}"
                        )
                        mark_failed("queue_timeout_ahead", message)
                        raise TimeoutError(message)
                    if not quiet:
                        print(
                            f"queue waiting platform={platform} "
                            f"ahead={queued_files[0].name}",
                            file=sys.stderr,
                        )
                    time.sleep(1)
                    continue
                break
            except BlockingIOError:
                if deadline is not None and time.monotonic() >= deadline:
                    message = f"timed out waiting for aiClaw lane queue platform={platform!r}"
                    mark_failed("queue_timeout_lock", message)
                    raise TimeoutError(message)
                if not quiet:
                    print(f"queue waiting platform={platform} lock=held", file=sys.stderr)
                time.sleep(1)

        try:
            if paths["busy"].exists():
                raise TimeoutError(f"aiClaw lane {platform!r} became busy before send; busy_file={paths['busy']}")
            job["status"] = "active"
            job["started_at"] = utc_now()
            write_json_file(active_path, job)
            if queued_path.exists():
                queued_path.unlink()

            result = callback()
            hold, reason = result_needs_lane_hold(result) if hold_on_suspect else (False, "")
            queue_meta = {
                "enabled": True,
                "job_id": job_id,
                "platform": platform,
                "queue_root": str(paths["root"]),
                "started_at": job["started_at"],
                "finished_at": utc_now(),
                "held": hold,
                "hold_reason": reason,
            }
            result["queue"] = queue_meta
            if hold:
                guidance = queue_recovery_guidance(queue_root, platform)
                write_json_file(paths["busy"], {
                    **queue_meta,
                    "queue_state": "needs_readback",
                    "readback_required": True,
                    "hard_block": False,
                    "reason": reason,
                    "meta": meta,
                    "release_command": guidance["release_command"],
                    "readback_rule": guidance["readback_rule"],
                })
            job["status"] = "done"
            job["finished_at"] = queue_meta["finished_at"]
            job["held"] = hold
            job["hold_reason"] = reason
            job["result"] = {
                "success": bool(result.get("success", False)),
                "suspect_intermediate": bool(result.get("suspect_intermediate", False)),
                "pre_send_transport_failure": is_pre_send_transport_failure(result),
                "needs_readback": hold,
                "error": result_error_text(result),
                "content_chars": len(str(result.get("content") or "")),
            }
            write_json_file(paths["done"] / f"{job_id}.json", job)
            if active_path.exists():
                active_path.unlink()
            return result
        except BaseException as exc:
            reason = "exception_after_send_started" if send_started() else "exception_before_send"
            if hold_on_suspect and send_started():
                guidance = queue_recovery_guidance(queue_root, platform)
                write_json_file(paths["busy"], {
                    "enabled": True,
                    "job_id": job_id,
                    "platform": platform,
                    "queue_root": str(paths["root"]),
                    "queue_state": "needs_readback",
                    "started_at": job.get("started_at"),
                    "finished_at": utc_now(),
                    "held": True,
                    "readback_required": True,
                    "hard_block": False,
                    "reason": reason,
                    "error": str(exc),
                    "meta": meta,
                    "release_command": guidance["release_command"],
                    "readback_rule": guidance["readback_rule"],
                })
            job["status"] = "failed"
            job["finished_at"] = utc_now()
            job["failure_reason"] = reason
            job["error"] = str(exc)
            write_json_file(paths["failed"] / f"{job_id}.json", job)
            if queued_path.exists():
                queued_path.unlink()
            if active_path.exists():
                active_path.unlink()
            raise
        finally:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)


def build_client(args: argparse.Namespace) -> ClawBotClient:
    return ClawBotClient(base_url=args.base_url, timeout=args.timeout)


def platform_info(status: dict[str, Any], platform: str) -> dict[str, Any]:
    platforms = status.get("platforms", {})
    if isinstance(platforms, dict):
        info = platforms.get(platform, {})
        return info if isinstance(info, dict) else {}
    return {}


def is_ready(status: dict[str, Any], platform: str, require_login: bool) -> bool:
    info = platform_info(status, platform)
    has_tab = bool(info.get("hasTab"))
    logged_in = bool(info.get("isLoggedIn"))
    return has_tab and (logged_in or not require_login)


def summarize_status(status: dict[str, Any]) -> dict[str, Any]:
    platforms = status.get("platforms", {})
    if not isinstance(platforms, dict):
        platforms = {}
    summary = {
        "platforms": {
            name: {
                "hasTab": bool(info.get("hasTab")) if isinstance(info, dict) else False,
                "isLoggedIn": bool(info.get("isLoggedIn")) if isinstance(info, dict) else False,
            }
            for name, info in platforms.items()
        },
        "tabs": status.get("tabs", []),
    }
    return summary


def wait_for_platform(
    client: ClawBotClient,
    platform: str,
    *,
    timeout_seconds: float,
    interval_seconds: float,
    require_login: bool,
    quiet: bool,
) -> dict[str, Any]:
    deadline = time.monotonic() + timeout_seconds
    last_status: dict[str, Any] | None = None
    while True:
        status = client.ai.status.get_status()
        last_status = status
        if is_ready(status, platform, require_login=require_login):
            return status
        if time.monotonic() >= deadline:
            summary = summarize_status(status)
            raise TimeoutError(
                "timed out waiting for "
                f"{platform!r} hasTab=true"
                + (" and isLoggedIn=true" if require_login else "")
                + f"; last_status={json.dumps(summary, sort_keys=True)}"
            )
        if not quiet:
            info = platform_info(status, platform)
            print(
                "waiting "
                f"platform={platform} "
                f"hasTab={bool(info.get('hasTab'))} "
                f"isLoggedIn={bool(info.get('isLoggedIn'))}",
                file=sys.stderr,
            )
        time.sleep(interval_seconds)


def cmd_status(args: argparse.Namespace) -> int:
    status = build_client(args).ai.status.get_status()
    emit_json(status if args.raw else summarize_status(status))
    return 0


def cmd_wait(args: argparse.Namespace) -> int:
    status = wait_for_platform(
        build_client(args),
        args.platform,
        timeout_seconds=args.wait_timeout,
        interval_seconds=args.interval,
        require_login=not args.no_login_required,
        quiet=args.quiet,
    )
    emit_json(status if args.raw else summarize_status(status))
    return 0


def cmd_navigate(args: argparse.Namespace) -> int:
    result = build_client(args).ai.navigation.navigate(args.platform)
    emit_json(result)
    return 0


def cmd_new(args: argparse.Namespace) -> int:
    def new_once() -> dict[str, Any]:
        result = jsonable(build_client(args).ai.chat.new_conversation(args.platform))
        if isinstance(result, dict):
            result.setdefault("success", True)
            result.setdefault("content", "")
            result.setdefault("meta", {"action": "new_conversation", "platform": args.platform})
            return result
        return {
            "success": True,
            "content": str(result),
            "meta": {"action": "new_conversation", "platform": args.platform},
        }

    if args.queue:
        result = run_in_platform_queue(
            platform=args.platform,
            queue_root=Path(args.queue_root),
            queue_timeout=args.queue_timeout,
            quiet=args.quiet,
            meta={"action": "new_conversation", "platform": args.platform},
            send_started=lambda: True,
            hold_on_suspect=True,
            callback=new_once,
        )
    else:
        result = new_once()
    emit_json(result)
    return 0 if result.get("success", True) else 2


def read_prompt(args: argparse.Namespace) -> str:
    if args.prompt is not None:
        return args.prompt
    prompt = sys.stdin.read()
    if not prompt.strip():
        raise ValueError("empty prompt; pass --prompt or pipe prompt text on stdin")
    return prompt


def sensitive_matches(prompt: str) -> list[str]:
    return [name for name, pattern in SENSITIVE_PATTERNS if pattern.search(prompt)]


def prompt_metadata(prompt: str, matches: list[str]) -> dict[str, Any]:
    return {
        "prompt_chars": len(prompt),
        "prompt_sha256": hashlib.sha256(prompt.encode("utf-8")).hexdigest(),
        "sensitive_matches": matches,
    }


def guard_prompt(prompt: str, *, allow_sensitive: bool) -> list[str]:
    matches = sensitive_matches(prompt)
    if matches and not allow_sensitive:
        raise ValueError(
            "prompt contains sensitive-looking material "
            f"({', '.join(matches)}); rerun with --allow-sensitive only if intentional"
        )
    return matches


def ask_ai(
    *,
    base_url: str = DEFAULT_BASE_URL,
    platform: str = DEFAULT_PLATFORM,
    prompt: str,
    timeout: int = 30,
    wait: bool = False,
    wait_timeout: float = 120,
    interval: float = 2,
    require_login: bool = True,
    quiet: bool = False,
    navigate: bool = False,
    new: bool = False,
    conversation_id: str | None = None,
    dry_run: bool = False,
    allow_sensitive: bool = False,
    queue: bool = True,
    queue_root: str | Path = DEFAULT_QUEUE_ROOT,
    queue_timeout: float = 900,
    hold_on_suspect: bool = True,
) -> dict[str, Any]:
    """Safely send one prompt through aiClaw, or return send metadata in dry-run mode."""
    matches = guard_prompt(prompt, allow_sensitive=allow_sensitive)
    meta = {
        "base_url": base_url,
        "platform": platform,
        "wait": bool(wait),
        "navigate": bool(navigate),
        "new": bool(new),
        "conversation_id": conversation_id,
        "queue": bool(queue),
        "queue_root": str(queue_root),
        **prompt_metadata(prompt, matches),
    }
    if dry_run:
        return {"dry_run": True, **meta}

    send_started = False
    started = time.monotonic()
    result: dict[str, Any] | None = None
    error_text = ""

    def send_once() -> dict[str, Any]:
        nonlocal conversation_id, send_started
        client = ClawBotClient(base_url=base_url, timeout=timeout)
        if wait:
            wait_for_platform(
                client,
                platform,
                timeout_seconds=wait_timeout,
                interval_seconds=interval,
                require_login=require_login,
                quiet=quiet,
            )
        if navigate:
            client.ai.navigation.navigate(platform)
            time.sleep(max(2.0, min(interval, 2.0)))
        if new:
            client.ai.chat.new_conversation(platform)
            conversation_id = None

        send_started = True
        result = client.ai.chat.send_message(
            platform=platform,
            prompt=prompt,
            conversation_id=conversation_id,
        )
        data = jsonable(result)
        if isinstance(data, dict) and navigate and is_pre_send_transport_failure(data):
            time.sleep(max(2.0, min(interval, 2.0)))
            result = client.ai.chat.send_message(
                platform=platform,
                prompt=prompt,
                conversation_id=conversation_id,
            )
            data = jsonable(result)
        if isinstance(data, dict):
            content = str(data.get("content") or "").strip()
            data.setdefault("meta", meta)
            data["suspect_intermediate"] = content.lower() in {"thinking", "thinking..."}
            data.setdefault("queue", {"enabled": False})
            return data
        return {
            "success": False,
            "content": str(data),
            "meta": meta,
            "suspect_intermediate": False,
            "queue": {"enabled": False},
        }

    try:
        if queue:
            result = run_in_platform_queue(
                platform=platform,
                queue_root=Path(queue_root),
                queue_timeout=queue_timeout,
                quiet=quiet,
                meta=meta,
                send_started=lambda: send_started,
                hold_on_suspect=hold_on_suspect,
                callback=send_once,
            )
        else:
            result = send_once()
        return result
    except BaseException as exc:
        error_text = str(exc)
        raise
    finally:
        if record_message is not None:
            try:
                response = ""
                success: bool | None = False
                metadata = dict(meta)
                if result is not None:
                    response = str(result.get("content") or "")
                    success = bool(result.get("success", False))
                    queue_meta = result.get("queue")
                    if isinstance(queue_meta, dict):
                        metadata["queue"] = queue_meta
                    if result.get("suspect_intermediate"):
                        metadata["failure_pattern"] = "suspect_intermediate_response"
                else:
                    response = error_text
                    metadata["failure_pattern"] = (
                        "exception_after_send_started" if send_started else "exception_before_send"
                    )
                    metadata["error"] = error_text
                record_message(
                    source_tool="aiclaw_chat.py",
                    source_file="tools/infra/aiclaw_chat.py",
                    channel="aiclaw_browser_oracle",
                    direction="agent_to_model",
                    provider="aiclaw",
                    model="browser-session",
                    platform=platform,
                    prompt_text=prompt,
                    response_text=response,
                    success=success,
                    latency_ms=(time.monotonic() - started) * 1000.0,
                    correlation_id=str(metadata.get("prompt_sha256", ""))[:16],
                    metadata=metadata,
                )
            except Exception:
                pass


def cmd_ask(args: argparse.Namespace) -> int:
    result = ask_ai(
        base_url=args.base_url,
        platform=args.platform,
        prompt=read_prompt(args),
        timeout=args.timeout,
        wait=args.wait,
        wait_timeout=args.wait_timeout,
        interval=args.interval,
        require_login=not args.no_login_required,
        quiet=args.quiet,
        navigate=args.navigate,
        new=args.new,
        conversation_id=args.conversation_id,
        dry_run=args.dry_run,
        allow_sensitive=args.allow_sensitive,
        queue=not args.no_queue,
        queue_root=args.queue_root,
        queue_timeout=args.queue_timeout,
        hold_on_suspect=not args.no_hold_on_suspect,
    )
    if args.json:
        emit_json(result)
    else:
        conversation_id = result.get("conversation_id") or result.get("conversationId")
        if conversation_id:
            print(f"[conversationId={conversation_id}]", file=sys.stderr)
        print(result.get("content") or json.dumps(result, indent=2, sort_keys=True))
    return 0 if result.get("success", bool(args.dry_run)) else 2


def cmd_queue_status(args: argparse.Namespace) -> int:
    emit_json(queue_summary(Path(args.queue_root), args.platform, stale_after=args.stale_after))
    return 0


def cmd_queue_release(args: argparse.Namespace) -> int:
    paths = queue_paths(Path(args.queue_root), args.platform)
    ensure_queue_dirs(paths)
    paths["root"].mkdir(parents=True, exist_ok=True)
    with paths["lock"].open("a+", encoding="utf-8") as lock_file:
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
        try:
            if not paths["busy"].exists():
                emit_json({
                    "released": False,
                    "reason": "no_busy_marker",
                    "platform": args.platform,
                    "queue_root": str(paths["root"]),
                })
                return 0
            busy = read_json_file(paths["busy"])
            released = {
                **busy,
                "released_at": utc_now(),
                "release_reason": args.reason,
                "released_by_pid": os.getpid(),
            }
            job_id = str(busy.get("job_id") or dt.datetime.now(dt.UTC).strftime("%Y%m%dT%H%M%SZ"))
            release_path = paths["released"] / f"{job_id}.json"
            write_json_file(release_path, released)
            paths["busy"].unlink()
            emit_json({
                "released": True,
                "platform": args.platform,
                "queue_root": str(paths["root"]),
                "archived_busy": str(release_path),
                "release_reason": args.reason,
            })
            return 0
        finally:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)


def cmd_queue_prune_active(args: argparse.Namespace) -> int:
    paths = queue_paths(Path(args.queue_root), args.platform)
    ensure_queue_dirs(paths)
    paths["root"].mkdir(parents=True, exist_ok=True)
    now = dt.datetime.now(dt.UTC)
    pruned: list[dict[str, Any]] = []
    kept: list[dict[str, Any]] = []
    with paths["lock"].open("a+", encoding="utf-8") as lock_file:
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
        try:
            for path in sorted(paths["active"].glob("*.json")):
                payload = read_json_file(path)
                summary = summarize_queue_doc(path, payload, now=now, stale_after=args.stale_after)
                should_prune = bool(summary["orphaned"] or summary["stale"])
                if not should_prune:
                    kept.append(summary)
                    continue
                archived = {
                    **payload,
                    "status": "active_pruned",
                    "pruned_at": utc_now(),
                    "prune_reason": args.reason,
                    "original_active_path": str(path),
                    "active_summary": summary,
                }
                job_id = str(payload.get("job_id") or path.stem)
                archive_path = paths["released"] / f"{job_id}.active_pruned.json"
                write_json_file(archive_path, archived)
                path.unlink()
                pruned.append({**summary, "archive_path": str(archive_path)})
            emit_json({
                "platform": args.platform,
                "queue_root": str(paths["root"]),
                "pruned_count": len(pruned),
                "kept_count": len(kept),
                "pruned": pruned,
                "kept": kept,
            })
            return 0
        finally:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)


def add_common_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--base-url",
        default=os.environ.get("AICLAW_BASE_URL", DEFAULT_BASE_URL),
        help=f"aiClaw localBridge base URL (default: {DEFAULT_BASE_URL})",
    )
    parser.add_argument(
        "--platform",
        default=os.environ.get("AICLAW_PLATFORM", DEFAULT_PLATFORM),
        help=f"AI platform name from aiClaw status (default: {DEFAULT_PLATFORM})",
    )
    parser.add_argument("--timeout", type=int, default=int(os.environ.get("AICLAW_TIMEOUT", "30")))


def add_queue_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--queue-root",
        default=os.environ.get("AICLAW_QUEUE_ROOT", str(DEFAULT_QUEUE_ROOT)),
        help=f"local single-flight queue root (default: {DEFAULT_QUEUE_ROOT})",
    )
    parser.add_argument(
        "--queue-timeout",
        type=float,
        default=float(os.environ.get("AICLAW_QUEUE_TIMEOUT", "900")),
        help="seconds to wait for the platform queue before failing",
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    status = subparsers.add_parser("status", help="Print aiClaw AI tab/login status.")
    add_common_args(status)
    status.add_argument("--raw", action="store_true", help="Print raw localBridge status.")
    status.set_defaults(func=cmd_status)

    wait = subparsers.add_parser("wait", help="Poll until a platform tab is ready.")
    add_common_args(wait)
    wait.add_argument("--wait-timeout", type=float, default=float(os.environ.get("AICLAW_WAIT_TIMEOUT", "120")))
    wait.add_argument("--interval", type=float, default=float(os.environ.get("AICLAW_WAIT_INTERVAL", "2")))
    wait.add_argument("--no-login-required", action="store_true")
    wait.add_argument("--quiet", action="store_true")
    wait.add_argument("--raw", action="store_true", help="Print raw localBridge status.")
    wait.set_defaults(func=cmd_wait)

    navigate = subparsers.add_parser("navigate", help="Ask aiClaw to focus/navigate an AI platform tab.")
    add_common_args(navigate)
    navigate.set_defaults(func=cmd_navigate)

    new = subparsers.add_parser("new", help="Start a new AI conversation for the platform.")
    add_common_args(new)
    add_queue_args(new)
    new.add_argument("--quiet", action="store_true")
    new.add_argument("--no-queue", dest="queue", action="store_false", help="Bypass the local single-flight platform queue.")
    new.set_defaults(queue=True)
    new.set_defaults(func=cmd_new)

    ask = subparsers.add_parser("ask", help="Send a prompt to an AI platform through aiClaw.")
    add_common_args(ask)
    ask.add_argument("--prompt", help="Prompt text. If omitted, stdin is used.")
    ask.add_argument("--conversation-id")
    ask.add_argument("--new", action="store_true", help="Start a new conversation before sending.")
    ask.add_argument("--navigate", action="store_true", help="Navigate/focus the platform before sending.")
    ask.add_argument("--wait", action="store_true", help="Poll status before sending.")
    ask.add_argument("--wait-timeout", type=float, default=float(os.environ.get("AICLAW_WAIT_TIMEOUT", "120")))
    ask.add_argument("--interval", type=float, default=float(os.environ.get("AICLAW_WAIT_INTERVAL", "2")))
    ask.add_argument("--no-login-required", action="store_true")
    ask.add_argument("--quiet", action="store_true")
    ask.add_argument("--json", action="store_true", help="Print the full parsed result.")
    ask.add_argument("--dry-run", action="store_true", help="Show send metadata without contacting aiClaw.")
    ask.add_argument("--allow-sensitive", action="store_true", help="Allow prompts matching secret-like patterns.")
    add_queue_args(ask)
    ask.add_argument("--no-queue", action="store_true", help="Bypass the local single-flight platform queue.")
    ask.add_argument(
        "--no-hold-on-suspect",
        action="store_true",
        help="Do not leave the lane busy after suspect/failed post-send results.",
    )
    ask.set_defaults(func=cmd_ask)

    queue_status = subparsers.add_parser("queue-status", help="Print local aiClaw lane queue state.")
    queue_status.add_argument("--platform", default=os.environ.get("AICLAW_PLATFORM", DEFAULT_PLATFORM))
    queue_status.add_argument("--queue-root", default=os.environ.get("AICLAW_QUEUE_ROOT", str(DEFAULT_QUEUE_ROOT)))
    queue_status.add_argument(
        "--stale-after",
        type=float,
        default=float(os.environ.get("AICLAW_QUEUE_STALE_SECONDS", str(DEFAULT_QUEUE_STALE_SECONDS))),
        help="seconds after which queued/active markers are reported as stale; <=0 disables stale marking",
    )
    queue_status.set_defaults(func=cmd_queue_status)

    queue_release = subparsers.add_parser(
        "queue-release",
        help="Release a held lane after final visible answer readback has been recorded.",
    )
    queue_release.add_argument("--platform", default=os.environ.get("AICLAW_PLATFORM", DEFAULT_PLATFORM))
    queue_release.add_argument("--queue-root", default=os.environ.get("AICLAW_QUEUE_ROOT", str(DEFAULT_QUEUE_ROOT)))
    queue_release.add_argument(
        "--reason",
        default="manual_final_readback_complete",
        help="auditable reason for releasing the held lane",
    )
    queue_release.set_defaults(func=cmd_queue_release)

    queue_prune_active = subparsers.add_parser(
        "queue-prune-active",
        help="Archive orphaned or stale active aiClaw queue markers without touching busy held lanes.",
    )
    queue_prune_active.add_argument("--platform", default=os.environ.get("AICLAW_PLATFORM", DEFAULT_PLATFORM))
    queue_prune_active.add_argument("--queue-root", default=os.environ.get("AICLAW_QUEUE_ROOT", str(DEFAULT_QUEUE_ROOT)))
    queue_prune_active.add_argument(
        "--stale-after",
        type=float,
        default=float(os.environ.get("AICLAW_QUEUE_STALE_SECONDS", str(DEFAULT_QUEUE_STALE_SECONDS))),
        help="seconds after which active markers are pruned; orphaned PIDs are always pruned",
    )
    queue_prune_active.add_argument(
        "--reason",
        default="orphaned_or_stale_active_marker",
        help="auditable reason for pruning active markers",
    )
    queue_prune_active.set_defaults(func=cmd_queue_prune_active)

    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        return int(args.func(args))
    except (ClawBotError, TimeoutError, ValueError) as exc:
        print(f"aiclaw_chat: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
