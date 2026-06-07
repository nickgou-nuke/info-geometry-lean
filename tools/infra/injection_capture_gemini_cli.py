#!/usr/bin/env python3
"""Capture Gemini CLI creative ideation into packet segment cards.

This adapter is intentionally account-auth oriented (no API key assumptions):
it shells out to a local `gemini` CLI command that is already authenticated via
interactive Google account login on the machine.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[2]))

from tools.infra.injection_common import (
    acquire_packet_lock,
    append_history_event,
    injections_root,
    repo_root,
    resolve_packet,
    validate_packet_schema,
    write_json_atomic,
    write_run_manifest,
)

try:
    from tools.infra.agent_message_ledger import record_message
except Exception:  # pragma: no cover - observation must never block capture.
    record_message = None


def sanitize_gemini_args(raw_args: list[str]) -> tuple[list[str], list[str]]:
    """Drop unsupported passthrough args before invoking Gemini CLI.

    Some legacy wrappers still inject prompt-level cache knobs that newer
    backends reject (`prompt_cache_retention`). We strip those args early to
    keep the capture stage backend-agnostic.
    """
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


def ensure_research(packet: dict[str, Any]) -> dict[str, Any]:
    research = packet.setdefault("research", {})
    if not isinstance(research, dict):
        raise ValueError("packet.research must be an object")

    workflow = research.setdefault(
        "workflow",
        {
            "mode": "gemini-hermes-codex",
            "creative_provider": "gemini_cli",
            "verification_provider": "hermes",
            "coding_provider": "codex",
            "creative_complete": False,
            "verification_complete": False,
        },
    )
    if not isinstance(workflow, dict):
        raise ValueError("packet.research.workflow must be an object")

    segments = research.setdefault("segments", [])
    if not isinstance(segments, list):
        raise ValueError("packet.research.segments must be a list")
    return research


def select_segments(
    research: dict[str, Any],
    explicit_ids: list[str],
    *,
    overwrite_notes: bool,
    max_segments: int,
) -> list[dict[str, Any]]:
    segments = research.get("segments", [])
    if not isinstance(segments, list):
        raise ValueError("packet.research.segments must be a list")

    by_id: dict[str, dict[str, Any]] = {}
    for seg in segments:
        if not isinstance(seg, dict):
            continue
        sid = str(seg.get("segment_id", "")).strip()
        if sid:
            by_id[sid] = seg

    chosen: list[dict[str, Any]] = []
    if explicit_ids:
        for sid in explicit_ids:
            if sid not in by_id:
                raise ValueError(f"segment not found: {sid}")
            chosen.append(by_id[sid])
    else:
        for seg in segments:
            if not isinstance(seg, dict):
                continue
            if overwrite_notes:
                chosen.append(seg)
                continue
            notes = str(seg.get("creative_notes", "")).strip()
            if not notes:
                chosen.append(seg)

    if max_segments > 0:
        chosen = chosen[:max_segments]
    return chosen


def build_prompt(packet: dict[str, Any], segment: dict[str, Any], prefix: str) -> str:
    packet_id = str(packet.get("packet_id", ""))
    title = str(packet.get("title", ""))
    raw_text = str(packet.get("raw_text", "")).strip()

    research = packet.get("research", {}) if isinstance(packet.get("research"), dict) else {}
    topic = str(research.get("topic", "")).strip()
    questions = research.get("questions", []) if isinstance(research.get("questions", []), list) else []

    sid = str(segment.get("segment_id", ""))
    seg_title = str(segment.get("title", "")).strip()
    seed = str(segment.get("seed_text", "")).strip()

    q_lines = "\n".join(f"- {str(q)}" for q in questions if str(q).strip())
    if not q_lines:
        q_lines = "- (none)"

    out = (
        f"{prefix.strip()}\n\n"
        f"Packet: {packet_id}\n"
        f"Title: {title}\n"
        f"Topic: {topic if topic else '(none)'}\n"
        f"Segment: {sid} {f'({seg_title})' if seg_title else ''}\n\n"
        "Research Questions:\n"
        f"{q_lines}\n\n"
        "Chunk Seed Text:\n"
        f"{seed}\n\n"
        "Optional broader context (raw intake excerpt):\n"
        f"{raw_text[:2200]}\n\n"
        "Task:\n"
        "1) Produce concise creative ideation notes for this chunk.\n"
        "2) Separate direct observations and inferred hypotheses.\n"
        "3) Return plain text only; no markdown tables.\n"
    )
    return out.strip()


def run_gemini_cli(
    gemini_bin: str,
    gemini_args: list[str],
    prompt: str,
    *,
    input_mode: str,
    prompt_flag: str,
    timeout_sec: int,
) -> tuple[int, str, str]:
    cmd = [gemini_bin] + gemini_args
    started = time.monotonic()
    code = 1
    stdout = ""
    stderr = ""
    try:
        if input_mode == "arg":
            cmd = cmd + [prompt_flag, prompt]
            proc = subprocess.run(
                cmd,
                text=True,
                capture_output=True,
                timeout=timeout_sec,
                check=False,
            )
        elif input_mode == "stdin":
            proc = subprocess.run(
                cmd,
                input=prompt,
                text=True,
                capture_output=True,
                timeout=timeout_sec,
                check=False,
            )
        else:
            raise ValueError(f"unsupported input mode: {input_mode}")
        code = int(proc.returncode)
        stdout = proc.stdout.strip()
        stderr = proc.stderr.strip()
    except subprocess.TimeoutExpired:
        code = 124
        stderr = f"timeout after {timeout_sec}s"
    except Exception as exc:
        code = 1
        stderr = str(exc)
    finally:
        if record_message is not None:
            try:
                record_message(
                    source_tool="injection_capture_gemini_cli.py",
                    source_file="tools/infra/injection_capture_gemini_cli.py",
                    channel="injection_gemini_capture",
                    provider="gemini-cli",
                    model=gemini_bin,
                    platform="gemini_cli",
                    prompt_text=prompt,
                    response_text=stdout or stderr,
                    success=(code == 0),
                    latency_ms=(time.monotonic() - started) * 1000.0,
                    metadata={
                        "input_mode": input_mode,
                        "prompt_flag": prompt_flag,
                        "timeout_sec": timeout_sec,
                        "returncode": code,
                        "failure_pattern": "" if code == 0 else stderr[:160],
                    },
                )
            except Exception:
                pass
    return code, stdout, stderr


def main() -> int:
    parser = argparse.ArgumentParser(description="Capture Gemini CLI ideation into packet segments")
    parser.add_argument("packet", help="Packet id or packet path")
    parser.add_argument("--segment-id", action="append", default=[], help="Segment id (repeat); default auto-select")
    parser.add_argument("--max-segments", type=int, default=0, help="Cap number of processed segments; 0=all")
    parser.add_argument("--overwrite-notes", action="store_true", help="Overwrite existing creative_notes")

    parser.add_argument("--gemini-bin", default="gemini", help="Gemini CLI binary name/path")
    parser.add_argument("--gemini-arg", action="append", default=[], help="Extra arg passed to Gemini CLI (repeat)")
    parser.add_argument("--input-mode", choices=["stdin", "arg"], default="stdin")
    parser.add_argument("--prompt-flag", default="-p", help="Prompt flag when --input-mode arg")
    parser.add_argument("--timeout-sec", type=int, default=240)
    parser.add_argument("--sleep-sec", type=float, default=0.0, help="Pacing delay between segment calls")

    parser.add_argument(
        "--prompt-prefix",
        default=(
            "You are the creative ideation stage in a research pipeline. Keep outputs concise,\n"
            "source-groundable, and semantically rich."
        ),
    )
    parser.add_argument("--dry-run", action="store_true", help="Do not call Gemini; only print selected segments")
    parser.add_argument("--mark-creative-complete", action="store_true")
    parser.add_argument("--note", default="")
    args = parser.parse_args()
    gemini_args, dropped_args = sanitize_gemini_args(args.gemini_arg)
    if dropped_args:
        print(
            "warning: dropped unsupported gemini arg(s) containing "
            "'prompt_cache_retention': "
            + ", ".join(dropped_args),
            file=sys.stderr,
        )

    root = repo_root()
    injections = injections_root(root)
    packet_path = resolve_packet(injections, args.packet)
    packet_id = packet_path.stem

    lock_owner = f"injection_capture_gemini_cli:{os.getpid()}:{packet_id}"
    with acquire_packet_lock(packet_id, lock_owner, block=True) as lock:
        packet = json.loads(packet_path.read_text(encoding="utf-8"))
        validate_packet_schema(packet)

        research = ensure_research(packet)
        workflow = research["workflow"]
        workflow["mode"] = "gemini-hermes-codex"
        workflow["creative_provider"] = "gemini_cli"

        segment_ids = [s.strip() for s in args.segment_id if s.strip()]
        targets = select_segments(
            research,
            segment_ids,
            overwrite_notes=args.overwrite_notes,
            max_segments=args.max_segments,
        )

        if not targets:
            raise ValueError("no segments selected")

        if args.dry_run:
            for seg in targets:
                print(str(seg.get("segment_id", "")))
            write_run_manifest(
                root,
                packet=packet,
                stage="segments:gemini_capture:dry_run",
                command_argv=list(sys.argv),
                result={"ok": True, "selected": len(targets)},
                extra={"lock_wait_sec": lock.wait_seconds},
            )
            return 0

        processed = 0
        failures: list[dict[str, Any]] = []

        for seg in targets:
            sid = str(seg.get("segment_id", "")).strip()
            if not sid:
                continue

            prompt = build_prompt(packet, seg, args.prompt_prefix)
            code, stdout, stderr = run_gemini_cli(
                args.gemini_bin,
                gemini_args,
                prompt,
                input_mode=args.input_mode,
                prompt_flag=args.prompt_flag,
                timeout_sec=args.timeout_sec,
            )
            if code != 0:
                failures.append(
                    {
                        "segment_id": sid,
                        "exit": code,
                        "stderr": stderr[-800:],
                    }
                )
                continue

            if not stdout.strip():
                failures.append(
                    {
                        "segment_id": sid,
                        "exit": code,
                        "stderr": "empty stdout",
                    }
                )
                continue

            seg["creative_notes"] = stdout.strip()
            processed += 1

            append_history_event(
                packet,
                event="segment:creative:capture",
                note=f"segment={sid};provider=gemini_cli",
                idempotent=False,
            )

            if args.sleep_sec > 0:
                time.sleep(args.sleep_sec)

        if args.mark_creative_complete and processed == len(targets) and not failures:
            workflow["creative_complete"] = True

        if args.note.strip():
            append_history_event(packet, event="segments:note", note=args.note.strip(), idempotent=False)

        validate_packet_schema(packet)
        write_json_atomic(packet_path, packet)

        write_run_manifest(
            root,
            packet=packet,
            stage="segments:gemini_capture",
            command_argv=list(sys.argv),
            result={
                "ok": len(failures) == 0,
                "processed": processed,
                "selected": len(targets),
                "failures": failures,
            },
            extra={
                "lock_wait_sec": lock.wait_seconds,
                "input_mode": args.input_mode,
                "gemini_bin": args.gemini_bin,
                "gemini_args": gemini_args,
                "dropped_unsupported_gemini_args": dropped_args,
                "sleep_sec": args.sleep_sec,
            },
        )

    if failures:
        print(json.dumps({"packet": str(packet_path), "failures": failures}, ensure_ascii=True))
        return 1

    print(packet_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
