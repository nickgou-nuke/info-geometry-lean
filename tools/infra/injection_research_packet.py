#!/usr/bin/env python3
"""Seed a topic-focused deep-research packet in handover/injections."""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[2]))

from tools.infra.injection_common import (
    LANES,
    acquire_packet_lock,
    default_packet_id,
    injections_root,
    repo_root,
    status_for_lane,
    utc_now,
    validate_packet_schema,
    write_json_atomic,
    write_run_manifest,
)


def main() -> int:
    parser = argparse.ArgumentParser(description="Create a deep-research injection packet")
    parser.add_argument("--id", dest="packet_id", default=None, help="Explicit packet id")
    parser.add_argument("--topic", required=True, help="Research topic")
    parser.add_argument("--title", default=None, help="Optional packet title")
    parser.add_argument("--question", action="append", default=[], help="Research question (repeat)")
    parser.add_argument("--source-url", action="append", default=[], help="Source URL (repeat)")
    parser.add_argument("--source-paper", action="append", default=[], help="Paper ref (DOI/arXiv/etc), repeat")
    parser.add_argument("--source-note", action="append", default=[], help="Free-form source note, repeat")
    parser.add_argument(
        "--workflow-mode",
        default="gemini-hermes-codex",
        choices=["standard", "gemini-hermes-codex"],
        help="Research workflow mode",
    )
    parser.add_argument(
        "--creative-provider",
        default="gemini_cli",
        help="Creative stage provider label",
    )
    parser.add_argument(
        "--verification-provider",
        default="hermes",
        help="Verification stage provider label",
    )
    parser.add_argument(
        "--coding-provider",
        default="codex",
        help="Coding stage provider label",
    )
    parser.add_argument(
        "--segment",
        action="append",
        default=[],
        help="Seed segment text; repeat for multiple segments",
    )
    parser.add_argument("--lane", default="raw", choices=LANES)
    parser.add_argument("--source-type", default="web", choices=["web", "chat", "manual", "llm", "paper", "other"])
    parser.add_argument("--source-ref", default="deep-research", help="Primary source ref label")
    parser.add_argument(
        "--authority-tier",
        default="external_analogy",
        choices=["repo_native", "external_analogy"],
        help="Authority tier for downstream promotion rules",
    )
    parser.add_argument("--raw-text", default="", help="Raw intake text")
    parser.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()

    root = repo_root()
    injections = injections_root(root)
    lane_dir = injections / args.lane
    lane_dir.mkdir(parents=True, exist_ok=True)

    packet_id = args.packet_id or default_packet_id()
    out_path = lane_dir / f"{packet_id}.json"

    lock_owner = f"injection_research_create:{os.getpid()}:{packet_id}"
    with acquire_packet_lock(packet_id, lock_owner, block=True) as lock:
        if out_path.exists() and not args.overwrite:
            raise SystemExit(f"error: packet exists: {out_path} (use --overwrite)")

        title = args.title or f"Deep research: {args.topic}"
        sources = []
        for url in args.source_url:
            sources.append({"kind": "url", "ref": url})
        for p in args.source_paper:
            sources.append({"kind": "paper", "ref": p})
        for n in args.source_note:
            sources.append({"kind": "note", "ref": n})

        raw_text = args.raw_text.strip()
        if not raw_text:
            raw_text = args.topic

        segments = []
        for idx, seg in enumerate(args.segment, start=1):
            text = seg.strip()
            if not text:
                continue
            segments.append(
                {
                    "segment_id": f"S{idx}",
                    "title": f"Segment {idx}",
                    "source_span": "",
                    "seed_text": text,
                    "creative_notes": "",
                    "enriched_context": "",
                    "claims": [],
                    "inference_flags": [],
                    "confidence": 0.0,
                    "literature_evidence": [],
                }
            )

        packet = {
            "packet_id": packet_id,
            "title": title,
            "authority_tier": args.authority_tier,
            "source": {
                "type": args.source_type,
                "ref": args.source_ref,
                "date": utc_now(),
            },
            "raw_text": raw_text,
            "distilled_claim": "",
            "research": {
                "topic": args.topic,
                "questions": args.question,
                "sources": sources,
                "coverage": "draft",
                "workflow": {
                    "mode": args.workflow_mode,
                    "creative_provider": args.creative_provider.strip() or "gemini_cli",
                    "verification_provider": args.verification_provider.strip() or "hermes",
                    "coding_provider": args.coding_provider.strip() or "codex",
                    "creative_complete": False,
                    "verification_complete": False,
                },
                "segments": segments,
            },
            "repo_mapping": {
                "owner_files": [],
                "symbols": [],
                "target_theorems": [],
            },
            "verification_plan": {
                "build_targets": [],
                "audit_targets": [],
            },
            "status": status_for_lane(args.lane),
            "history": [
                {
                    "at": utc_now(),
                    "event": "created:research",
                    "note": f"created in lane={args.lane}",
                }
            ],
        }

        validate_packet_schema(packet)
        write_json_atomic(out_path, packet)
        write_run_manifest(
            root,
            packet=packet,
            stage=f"create:research:{args.lane}",
            command_argv=list(os.sys.argv),
            result={"ok": True},
            extra={"lock_wait_sec": lock.wait_seconds, "lane": args.lane},
        )
    print(out_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
