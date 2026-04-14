#!/usr/bin/env python3
"""Syntactically chunk packet intake text and seed per-segment ideation surfaces.

This script is the earliest stage of the gemini-hermes-codex research pipeline:
1) split intake text into syntactic chunks,
2) create/append research segment cards,
3) optionally attach creative ideation notes,
4) optionally emit per-segment ideation prompt files.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
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


def normalize_text(s: str) -> str:
    s = s.replace("\r\n", "\n").replace("\r", "\n")
    # keep paragraph boundaries, trim outer whitespace
    return s.strip()


def split_sentences(paragraph: str) -> list[str]:
    text = paragraph.strip()
    if not text:
        return []
    # Basic multilingual sentence boundary splitter.
    parts = re.split(r"(?<=[.!?\u2026])\s+", text)
    out = [p.strip() for p in parts if p.strip()]
    return out if out else [text]


def split_oversized(sentence: str, max_chars: int) -> list[str]:
    s = sentence.strip()
    if len(s) <= max_chars:
        return [s]

    # First pass: split by soft punctuation while preserving readability.
    soft = re.split(r"(?<=[,;:])\s+", s)
    if len(soft) > 1 and max(len(x) for x in soft) < len(s):
        out: list[str] = []
        buf = ""
        for part in soft:
            cand = part if not buf else f"{buf} {part}".strip()
            if len(cand) <= max_chars:
                buf = cand
            else:
                if buf:
                    out.append(buf)
                if len(part) <= max_chars:
                    buf = part
                else:
                    # hard fallback by whitespace tokens
                    tokens = part.split()
                    hard = ""
                    for t in tokens:
                        hc = t if not hard else f"{hard} {t}".strip()
                        if len(hc) <= max_chars:
                            hard = hc
                        else:
                            if hard:
                                out.append(hard)
                            hard = t
                    if hard:
                        buf = hard
                    else:
                        buf = ""
        if buf:
            out.append(buf)
        return [x for x in out if x.strip()]

    # Hard fallback by words.
    out2: list[str] = []
    buf2 = ""
    for token in s.split():
        cand = token if not buf2 else f"{buf2} {token}".strip()
        if len(cand) <= max_chars:
            buf2 = cand
        else:
            if buf2:
                out2.append(buf2)
            buf2 = token
    if buf2:
        out2.append(buf2)
    return [x for x in out2 if x.strip()]


def syntactic_chunks(text: str, max_chars: int, max_segments: int | None = None) -> list[str]:
    paragraphs = [p.strip() for p in re.split(r"\n\s*\n+", normalize_text(text)) if p.strip()]
    units: list[str] = []
    for p in paragraphs:
        for s in split_sentences(p):
            units.extend(split_oversized(s, max_chars=max_chars))

    chunks: list[str] = []
    buf = ""
    for u in units:
        cand = u if not buf else f"{buf} {u}".strip()
        if len(cand) <= max_chars:
            buf = cand
            continue
        if buf:
            chunks.append(buf)
        buf = u
        if max_segments is not None and len(chunks) >= max_segments:
            break

    if (max_segments is None or len(chunks) < max_segments) and buf:
        chunks.append(buf)

    if max_segments is not None:
        chunks = chunks[:max_segments]
    return [c for c in chunks if c.strip()]


def next_segment_index(existing: list[dict[str, Any]]) -> int:
    max_idx = 0
    for seg in existing:
        if not isinstance(seg, dict):
            continue
        sid = str(seg.get("segment_id", "")).strip()
        m = re.fullmatch(r"S(\d+)", sid)
        if not m:
            continue
        max_idx = max(max_idx, int(m.group(1)))
    return max_idx + 1


def parse_ideation_notes_file(path: Path) -> list[str]:
    raw = path.read_text(encoding="utf-8")
    # Delimiter for multi-note payloads.
    blocks = [b.strip() for b in re.split(r"\n\s*---\s*\n", raw) if b.strip()]
    return blocks


def write_prompt_files(out_dir: Path, packet_id: str, title: str, segments: list[dict[str, Any]]) -> list[str]:
    out_dir.mkdir(parents=True, exist_ok=True)
    written: list[str] = []
    for seg in segments:
        sid = str(seg["segment_id"])
        seed = str(seg.get("seed_text", "")).strip()
        prompt = (
            f"# Ideation Prompt {sid}\n\n"
            f"Packet: {packet_id}\n"
            f"Title: {title}\n\n"
            "Task:\n"
            "1. Expand this chunk into precise conceptual notes.\n"
            "2. Separate direct observations vs inferred claims.\n"
            "3. Add 3-6 candidate claims for verification.\n"
            "4. Keep language compact and source-groundable.\n\n"
            "Chunk:\n"
            f"{seed}\n"
        )
        p = out_dir / f"{sid}.md"
        p.write_text(prompt, encoding="utf-8")
        written.append(str(p))
    return written


def main() -> int:
    parser = argparse.ArgumentParser(description="Chunk intake text and seed ideation segments")
    parser.add_argument("packet", help="Packet id or packet path")
    parser.add_argument("--text", default="", help="Override chunk source text; defaults to packet.raw_text")
    parser.add_argument("--max-chars", type=int, default=650, help="Max characters per chunk")
    parser.add_argument("--max-segments", type=int, default=0, help="Optional cap; 0 means unlimited")
    parser.add_argument("--replace-segments", action="store_true", help="Replace existing research.segments")
    parser.add_argument("--segment-title-prefix", default="Chunk", help="Segment title prefix")
    parser.add_argument("--set-workflow-mode", choices=["standard", "gemini-hermes-codex"], default="gemini-hermes-codex")
    parser.add_argument("--creative-provider", default="gemini_cli")
    parser.add_argument("--verification-provider", default="hermes")
    parser.add_argument("--coding-provider", default="codex")
    parser.add_argument("--creative-notes", action="append", default=[], help="Repeat to attach ideation notes to chunks")
    parser.add_argument("--creative-notes-file", default="", help="File with ideation notes; blocks separated by '\n---\n'")
    parser.add_argument("--prompt-dir", default="", help="If set, write per-segment ideation prompts to this directory")
    parser.add_argument("--mark-creative-complete", action="store_true")
    parser.add_argument("--note", default="")
    args = parser.parse_args()

    if args.max_chars < 80:
        raise ValueError("--max-chars too small; use >= 80")

    root = repo_root()
    injections = injections_root(root)
    packet_path = resolve_packet(injections, args.packet)
    packet_id = packet_path.stem

    lock_owner = f"injection_chunk_ideate:{os.getpid()}:{packet_id}"
    with acquire_packet_lock(packet_id, lock_owner, block=True) as lock:
        packet = json.loads(packet_path.read_text(encoding="utf-8"))
        validate_packet_schema(packet)

        research = ensure_research(packet)
        workflow = research["workflow"]
        workflow["mode"] = args.set_workflow_mode
        workflow["creative_provider"] = args.creative_provider.strip() or "gemini_cli"
        workflow["verification_provider"] = args.verification_provider.strip() or "hermes"
        workflow["coding_provider"] = args.coding_provider.strip() or "codex"
        workflow["creative_complete"] = False if not args.mark_creative_complete else workflow.get("creative_complete", False)

        text = args.text.strip() or str(packet.get("raw_text", "")).strip()
        if not text:
            raise ValueError("no source text: provide --text or packet.raw_text")

        max_segments = args.max_segments if args.max_segments > 0 else None
        chunks = syntactic_chunks(text, max_chars=args.max_chars, max_segments=max_segments)
        if not chunks:
            raise ValueError("syntactic chunking produced zero segments")

        existing_segments = research.get("segments", [])
        if not isinstance(existing_segments, list):
            raise ValueError("packet.research.segments must be a list")

        if args.replace_segments:
            existing_segments = []

        start_idx = next_segment_index(existing_segments)
        new_segments: list[dict[str, Any]] = []
        for k, chunk in enumerate(chunks, start=start_idx):
            sid = f"S{k}"
            new_segments.append(
                {
                    "segment_id": sid,
                    "title": f"{args.segment_title_prefix} {k}",
                    "source_span": "",
                    "seed_text": chunk,
                    "creative_notes": "",
                    "enriched_context": "",
                    "claims": [],
                    "inference_flags": [],
                    "confidence": 0.0,
                    "literature_evidence": [],
                }
            )

        merged_segments = existing_segments + new_segments

        file_notes: list[str] = []
        if args.creative_notes_file.strip():
            file_notes = parse_ideation_notes_file(Path(args.creative_notes_file))
        inline_notes = [n.strip() for n in args.creative_notes if n.strip()]
        note_pool = inline_notes + file_notes

        if note_pool:
            for i, seg in enumerate(new_segments):
                if i >= len(note_pool):
                    break
                seg["creative_notes"] = note_pool[i]

        # If every new segment has non-empty creative notes and user asked, mark complete.
        if args.mark_creative_complete:
            if all(str(seg.get("creative_notes", "")).strip() for seg in new_segments):
                workflow["creative_complete"] = True
            else:
                raise ValueError("--mark-creative-complete requires creative notes for every new segment")

        research["segments"] = merged_segments

        append_history_event(
            packet,
            event="segments:chunked",
            note=f"count={len(new_segments)};max_chars={args.max_chars};replace={str(args.replace_segments).lower()}",
            idempotent=False,
        )

        if note_pool:
            append_history_event(
                packet,
                event="segments:ideation-seeded",
                note=f"notes={len(note_pool)}",
                idempotent=False,
            )

        if args.note.strip():
            append_history_event(packet, event="segments:note", note=args.note.strip(), idempotent=False)

        prompt_files: list[str] = []
        if args.prompt_dir.strip():
            prompt_files = write_prompt_files(
                Path(args.prompt_dir),
                packet_id=str(packet.get("packet_id", packet_id)),
                title=str(packet.get("title", "")),
                segments=new_segments,
            )

        validate_packet_schema(packet)
        write_json_atomic(packet_path, packet)
        write_run_manifest(
            root,
            packet=packet,
            stage="segments:chunk_ideate",
            command_argv=list(sys.argv),
            result={
                "ok": True,
                "new_segments": len(new_segments),
                "prompt_files": len(prompt_files),
                "creative_notes_seeded": min(len(note_pool), len(new_segments)),
            },
            extra={
                "lock_wait_sec": lock.wait_seconds,
                "replace_segments": args.replace_segments,
                "max_chars": args.max_chars,
                "max_segments": args.max_segments,
            },
        )

    print(packet_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
