#!/usr/bin/env python3
"""Account-auth Gemini CLI adapter for single-segment ideation.

Input: one JSON object on stdin.
Output: one JSON object on stdout with creative_notes + agent status fields.

No API-key logic is used here; this assumes local Gemini CLI is already signed in.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from typing import Any


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def sanitize_gemini_args(raw_args: list[str]) -> tuple[list[str], list[str]]:
    """Drop legacy cache-retention args unsupported by current backends."""
    sanitized: list[str] = []
    dropped: list[str] = []
    skip_next = False
    for idx, arg in enumerate(raw_args):
        if skip_next:
            skip_next = False
            continue
        if "prompt_cache_retention" not in arg:
            sanitized.append(arg)
            continue

        dropped.append(arg)
        if arg.strip() == "--prompt_cache_retention" and idx + 1 < len(raw_args):
            dropped.append(raw_args[idx + 1])
            skip_next = True
    return sanitized, dropped


def build_prompt(segment: dict[str, Any], prefix: str) -> str:
    content = str(segment.get("content", "")).strip()
    if not content:
        content = str(segment.get("seed_text", "")).strip()
    if not content:
        content = str(segment.get("text", "")).strip()

    seg_id = str(segment.get("segment_id", "")).strip()
    title = str(segment.get("title", "")).strip()

    return (
        f"{prefix.strip()}\n\n"
        f"Segment: {seg_id} {f'({title})' if title else ''}\n\n"
        "Task:\n"
        "1) Produce concise creative_notes for this segment.\n"
        "2) Separate observed statements and inferred hypotheses.\n"
        "3) Keep output plain text.\n\n"
        "Input Segment:\n"
        f"{content}\n"
    ).strip()


def run_gemini(gemini_bin: str, gemini_args: list[str], prompt: str, *, input_mode: str, prompt_flag: str, timeout_sec: int) -> tuple[int, str, str]:
    cmd = [gemini_bin] + gemini_args
    if input_mode == "arg":
        cmd = cmd + [prompt_flag, prompt]
        proc = subprocess.run(cmd, text=True, capture_output=True, timeout=timeout_sec, check=False)
    else:
        proc = subprocess.run(cmd, input=prompt, text=True, capture_output=True, timeout=timeout_sec, check=False)
    return proc.returncode, proc.stdout.strip(), proc.stderr.strip()


def main() -> int:
    parser = argparse.ArgumentParser(description="Gemini account-auth adapter for one segment")
    parser.add_argument("--gemini-bin", default="gemini")
    parser.add_argument("--gemini-arg", action="append", default=[])
    parser.add_argument("--input-mode", choices=["stdin", "arg"], default="stdin")
    parser.add_argument("--prompt-flag", default="-p")
    parser.add_argument("--timeout-sec", type=int, default=240)
    parser.add_argument(
        "--prompt-prefix",
        default=(
            "You are the Gemini Agent in a structured research pipeline. "
            "Generate precise creative ideation notes."
        ),
    )
    args = parser.parse_args()
    gemini_args, dropped_args = sanitize_gemini_args(args.gemini_arg)
    if dropped_args:
        print(
            "warning: dropped unsupported gemini arg(s) containing "
            "'prompt_cache_retention': "
            + ", ".join(dropped_args),
            file=sys.stderr,
        )

    raw = sys.stdin.read().strip()
    if not raw:
        return 0

    try:
        segment = json.loads(raw)
    except json.JSONDecodeError as exc:
        out = {
            "agent_status": "FATAL",
            "errors": [f"invalid_json_input: {exc}"],
            "enriched_at_utc": utc_now(),
        }
        print(json.dumps(out, ensure_ascii=True))
        return 1

    if not isinstance(segment, dict):
        out = {
            "agent_status": "FATAL",
            "errors": ["input must be JSON object"],
            "enriched_at_utc": utc_now(),
        }
        print(json.dumps(out, ensure_ascii=True))
        return 1

    prompt = build_prompt(segment, args.prompt_prefix)

    try:
        code, stdout, stderr = run_gemini(
            args.gemini_bin,
            gemini_args,
            prompt,
            input_mode=args.input_mode,
            prompt_flag=args.prompt_flag,
            timeout_sec=args.timeout_sec,
        )
    except Exception as exc:
        enriched = dict(segment)
        enriched["agent_status"] = "FATAL"
        enriched["error_log"] = str(exc)
        enriched["errors"] = [str(exc)]
        enriched["enriched_at_utc"] = utc_now()
        print(json.dumps(enriched, ensure_ascii=True))
        return 1

    enriched = dict(segment)
    enriched["enriched_at_utc"] = utc_now()

    if code == 0 and stdout:
        enriched["creative_notes"] = stdout
        enriched["agent_status"] = "SUCCESS"
        enriched["errors"] = []
        print(json.dumps(enriched, ensure_ascii=True))
        return 0

    enriched["agent_status"] = "ERROR"
    enriched["error_log"] = stderr or "empty_output"
    enriched["errors"] = [enriched["error_log"]]
    print(json.dumps(enriched, ensure_ascii=True))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
