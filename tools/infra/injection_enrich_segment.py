#!/usr/bin/env python3
"""Update research workflow segments with creative notes and evidence."""

from __future__ import annotations

import argparse
import json
import os
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


def as_nonempty_list(values: list[str]) -> list[str]:
    return [v.strip() for v in values if v.strip()]


def ensure_research(packet: dict[str, Any]) -> dict[str, Any]:
    research = packet.setdefault("research", {})
    if not isinstance(research, dict):
        raise ValueError("packet.research must be an object")
    workflow = research.setdefault(
        "workflow",
        {
            "mode": "standard",
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


def find_or_create_segment(research: dict[str, Any], segment_id: str, seed_text: str) -> dict[str, Any]:
    segments = research["segments"]
    for seg in segments:
        if isinstance(seg, dict) and str(seg.get("segment_id", "")).strip() == segment_id:
            return seg
    segment = {
        "segment_id": segment_id,
        "title": segment_id,
        "source_span": "",
        "seed_text": seed_text,
        "creative_notes": "",
        "enriched_context": "",
        "claims": [],
        "inference_flags": [],
        "confidence": 0.0,
        "literature_evidence": [],
    }
    segments.append(segment)
    return segment


def parse_evidence_rows(args: argparse.Namespace) -> list[dict[str, str]]:
    urls = as_nonempty_list(args.evidence_url)
    summaries = as_nonempty_list(args.evidence_summary)
    titles = args.evidence_title
    dates = args.evidence_date
    relevances = args.evidence_relevance
    if not urls and not summaries:
        return []
    if len(urls) != len(summaries):
        raise ValueError("--evidence-url and --evidence-summary must have the same count")
    if titles and len(titles) not in (0, len(urls)):
        raise ValueError("--evidence-title count must be 0 or match evidence count")
    if dates and len(dates) not in (0, len(urls)):
        raise ValueError("--evidence-date count must be 0 or match evidence count")
    if relevances and len(relevances) not in (0, len(urls)):
        raise ValueError("--evidence-relevance count must be 0 or match evidence count")
    rows: list[dict[str, str]] = []
    for i, (url, summary) in enumerate(zip(urls, summaries)):
        row = {"url": url, "summary": summary}
        if i < len(titles) and titles[i].strip():
            row["title"] = titles[i].strip()
        if i < len(dates) and dates[i].strip():
            row["date"] = dates[i].strip()
        if i < len(relevances) and relevances[i].strip():
            row["relevance"] = relevances[i].strip()
        rows.append(row)
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description="Attach Gemini/Hermes enrichment to a packet segment")
    parser.add_argument("packet", help="Packet id or packet path")
    parser.add_argument("--segment-id", required=True, help="Segment id (for example S1)")
    parser.add_argument("--seed-text", default="", help="Seed text if segment is auto-created")
    parser.add_argument("--title", default="", help="Optional segment title")
    parser.add_argument("--source-span", default="", help="Optional source span marker")
    parser.add_argument("--creative-notes", default="", help="Gemini creative notes for this segment")
    parser.add_argument("--enriched-context", default="", help="Hermes enrichment notes/context")
    parser.add_argument("--claim", action="append", default=[], help="Claim line (repeat)")
    parser.add_argument("--inference-flag", action="append", default=[], help="Inference flag (repeat)")
    parser.add_argument("--confidence", type=float, default=None, help="Confidence score [0,1] for segment")
    parser.add_argument("--evidence-url", action="append", default=[], help="Evidence URL (repeat)")
    parser.add_argument("--evidence-summary", action="append", default=[], help="Evidence summary (repeat)")
    parser.add_argument("--evidence-title", action="append", default=[], help="Evidence title (repeat)")
    parser.add_argument("--evidence-date", action="append", default=[], help="Evidence date (repeat)")
    parser.add_argument("--evidence-relevance", action="append", default=[], help="Evidence relevance (repeat)")
    parser.add_argument(
        "--set-workflow-mode",
        choices=["standard", "gemini-hermes-codex"],
        default=None,
        help="Override research.workflow.mode",
    )
    parser.add_argument("--mark-creative-complete", action="store_true")
    parser.add_argument("--mark-verification-complete", action="store_true")
    parser.add_argument("--note", default="", help="History note suffix")
    args = parser.parse_args()

    root = repo_root()
    injections = injections_root(root)
    packet_path = resolve_packet(injections, args.packet)
    packet_id = packet_path.stem

    lock_owner = f"injection_enrich:{os.getpid()}:{packet_id}:{args.segment_id}"
    with acquire_packet_lock(packet_id, lock_owner, block=True) as lock:
        packet = json.loads(packet_path.read_text(encoding="utf-8"))
        validate_packet_schema(packet)

        research = ensure_research(packet)
        if args.set_workflow_mode:
            research["workflow"]["mode"] = args.set_workflow_mode

        segment = find_or_create_segment(research, args.segment_id.strip(), args.seed_text)

        if args.title.strip():
            segment["title"] = args.title.strip()
        if args.source_span.strip():
            segment["source_span"] = args.source_span.strip()
        if args.creative_notes.strip():
            segment["creative_notes"] = args.creative_notes.strip()
        if args.enriched_context.strip():
            segment["enriched_context"] = args.enriched_context.strip()

        claims = as_nonempty_list(args.claim)
        if claims:
            segment["claims"] = claims
        flags = as_nonempty_list(args.inference_flag)
        if flags:
            segment["inference_flags"] = flags
        if args.confidence is not None:
            if args.confidence < 0.0 or args.confidence > 1.0:
                raise ValueError("--confidence must be in [0,1]")
            segment["confidence"] = float(args.confidence)

        evidence_rows = parse_evidence_rows(args)
        if evidence_rows:
            segment["literature_evidence"] = evidence_rows

        workflow = research["workflow"]
        if args.mark_creative_complete:
            workflow["creative_complete"] = True
        if args.mark_verification_complete:
            workflow["verification_complete"] = True

        note_parts = [f"segment={args.segment_id}"]
        if args.note.strip():
            note_parts.append(args.note.strip())
        append_history_event(
            packet,
            event="segment:enriched",
            note="; ".join(note_parts),
            idempotent=False,
        )

        validate_packet_schema(packet)
        write_json_atomic(packet_path, packet)
        write_run_manifest(
            root,
            packet=packet,
            stage="segment:enrich",
            command_argv=list(sys.argv),
            result={"ok": True, "segment_id": args.segment_id},
            extra={
                "lock_wait_sec": lock.wait_seconds,
                "mark_creative_complete": args.mark_creative_complete,
                "mark_verification_complete": args.mark_verification_complete,
                "evidence_count": len(evidence_rows),
            },
        )

    print(packet_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
