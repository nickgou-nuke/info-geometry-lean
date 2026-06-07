#!/usr/bin/env python3
"""Append-only ledger for agent-to-model communication.

The ledger records what agents submit to collaborator/oracle/model lanes and
what comes back. It is for empirical analysis and GEPA scoring only; it is not
proof authority and does not promote SOP changes.

Secrets are redacted before writing. Large payloads are clipped but hashed in
full so repeated prompt shapes can still be grouped.
"""

from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import hashlib
import json
import os
import re
import uuid
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_LEDGER_DIR = REPO_ROOT / "artifacts" / "agent_messages"
DEFAULT_MAX_TEXT_CHARS = int(os.environ.get("AGENT_MESSAGE_LEDGER_MAX_TEXT_CHARS", "20000"))

SENSITIVE_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("private_key", re.compile(r"-----BEGIN [A-Z ]*PRIVATE KEY-----[\s\S]*?-----END [A-Z ]*PRIVATE KEY-----")),
    ("openai_key", re.compile(r"\bsk-[A-Za-z0-9_-]{20,}\b")),
    ("github_token", re.compile(r"\bgh[pousr]_[A-Za-z0-9_]{20,}\b")),
    ("aws_access_key", re.compile(r"\bAKIA[0-9A-Z]{16}\b")),
    ("bearer_token", re.compile(r"(?i)\bBearer\s+[A-Za-z0-9._~+/=-]{20,}\b")),
    ("secret_assignment", re.compile(r"(?i)\b(password|passwd|secret|token|api[_-]?key)\s*[:=]\s*['\"]?[^'\"\s]+")),
)


def utc_now() -> str:
    return dt.datetime.now(dt.UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def today_path(ledger_dir: Path = DEFAULT_LEDGER_DIR) -> Path:
    day = dt.datetime.now(dt.UTC).strftime("%Y%m%d")
    return ledger_dir / f"{day}_agent_messages.jsonl"


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8", errors="replace")).hexdigest()


def redact_text(text: str) -> tuple[str, list[str]]:
    redacted = text
    hits: list[str] = []
    for name, pattern in SENSITIVE_PATTERNS:
        if pattern.search(redacted):
            hits.append(name)
            redacted = pattern.sub(f"[REDACTED:{name}]", redacted)
    return redacted, sorted(set(hits))


def clip_text(text: str, max_chars: int = DEFAULT_MAX_TEXT_CHARS) -> tuple[str, bool]:
    if max_chars <= 0:
        return "", bool(text)
    if len(text) <= max_chars:
        return text, False
    half = max_chars // 2
    return (
        text[:half]
        + f"\n\n[... clipped {len(text) - max_chars} chars ...]\n\n"
        + text[-(max_chars - half):],
        True,
    )


def _jsonable(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): _jsonable(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [_jsonable(v) for v in value]
    if isinstance(value, (str, int, float, bool)) or value is None:
        return value
    return str(value)


def record_message(
    *,
    source_tool: str,
    source_file: str,
    channel: str,
    direction: str = "agent_to_model",
    provider: str = "",
    model: str = "",
    platform: str = "",
    prompt_text: str = "",
    response_text: str = "",
    success: bool | None = None,
    latency_ms: float | None = None,
    correlation_id: str = "",
    metadata: dict[str, Any] | None = None,
    ledger_dir: Path | str = DEFAULT_LEDGER_DIR,
    max_text_chars: int = DEFAULT_MAX_TEXT_CHARS,
) -> dict[str, Any]:
    """Append a redacted communication event and return the written payload."""
    prompt_redacted, prompt_sensitive = redact_text(prompt_text or "")
    response_redacted, response_sensitive = redact_text(response_text or "")
    prompt_clip, prompt_truncated = clip_text(prompt_redacted, max_text_chars)
    response_clip, response_truncated = clip_text(response_redacted, max_text_chars)
    event_id = uuid.uuid4().hex

    event = {
        "schema": "agent-message-ledger/v1",
        "event_id": event_id,
        "ts": utc_now(),
        "source_tool": source_tool,
        "source_file": source_file,
        "channel": channel,
        "direction": direction,
        "provider": provider,
        "model": model,
        "platform": platform,
        "correlation_id": correlation_id,
        "prompt_sha256": sha256_text(prompt_text or ""),
        "prompt_chars": len(prompt_text or ""),
        "prompt_text": prompt_clip,
        "prompt_truncated": prompt_truncated,
        "prompt_sensitive_matches": prompt_sensitive,
        "response_sha256": sha256_text(response_text or ""),
        "response_chars": len(response_text or ""),
        "response_text": response_clip,
        "response_truncated": response_truncated,
        "response_sensitive_matches": response_sensitive,
        "success": success,
        "latency_ms": latency_ms,
        "metadata": _jsonable(metadata or {}),
        "authority": "observation_only_not_proof",
    }

    path = today_path(Path(ledger_dir))
    path.parent.mkdir(parents=True, exist_ok=True)
    line = json.dumps(event, sort_keys=True, ensure_ascii=False) + "\n"
    with path.open("a", encoding="utf-8") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            handle.write(line)
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
    return event


def main() -> int:
    parser = argparse.ArgumentParser(description="Append one agent-message ledger event.")
    parser.add_argument("--source-tool", required=True)
    parser.add_argument("--source-file", default="")
    parser.add_argument("--channel", required=True)
    parser.add_argument("--direction", default="agent_to_model")
    parser.add_argument("--provider", default="")
    parser.add_argument("--model", default="")
    parser.add_argument("--platform", default="")
    parser.add_argument("--prompt-file", type=Path)
    parser.add_argument("--response-file", type=Path)
    parser.add_argument("--success", choices=["true", "false", "unknown"], default="unknown")
    parser.add_argument("--ledger-dir", type=Path, default=DEFAULT_LEDGER_DIR)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    prompt_text = args.prompt_file.read_text(encoding="utf-8") if args.prompt_file else ""
    response_text = args.response_file.read_text(encoding="utf-8") if args.response_file else ""
    success = None if args.success == "unknown" else args.success == "true"
    event = record_message(
        source_tool=args.source_tool,
        source_file=args.source_file,
        channel=args.channel,
        direction=args.direction,
        provider=args.provider,
        model=args.model,
        platform=args.platform,
        prompt_text=prompt_text,
        response_text=response_text,
        success=success,
        ledger_dir=args.ledger_dir,
    )
    if args.json:
        print(json.dumps(event, indent=2, sort_keys=True))
    else:
        print(f"recorded {event['event_id']} prompt={event['prompt_chars']} response={event['response_chars']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
