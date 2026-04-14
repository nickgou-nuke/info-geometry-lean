#!/usr/bin/env python3
"""Seed a topic-focused deep-research packet in handover/injections."""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path

LANES = ("raw", "distilled", "translated", "gated", "accepted", "rejected", "archive")


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def default_packet_id() -> str:
    return "EXT-" + datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")


def main() -> int:
    parser = argparse.ArgumentParser(description="Create a deep-research injection packet")
    parser.add_argument("--id", dest="packet_id", default=None, help="Explicit packet id")
    parser.add_argument("--topic", required=True, help="Research topic")
    parser.add_argument("--title", default=None, help="Optional packet title")
    parser.add_argument("--question", action="append", default=[], help="Research question (repeat)")
    parser.add_argument("--source-url", action="append", default=[], help="Source URL (repeat)")
    parser.add_argument("--source-paper", action="append", default=[], help="Paper ref (DOI/arXiv/etc), repeat")
    parser.add_argument("--source-note", action="append", default=[], help="Free-form source note, repeat")
    parser.add_argument("--lane", default="raw", choices=LANES)
    parser.add_argument("--source-type", default="web", choices=["web", "chat", "manual", "llm", "paper", "other"])
    parser.add_argument("--source-ref", default="deep-research", help="Primary source ref label")
    parser.add_argument("--raw-text", default="", help="Raw intake text")
    parser.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    injections = repo_root / "handover" / "injections"
    lane_dir = injections / args.lane
    lane_dir.mkdir(parents=True, exist_ok=True)

    packet_id = args.packet_id or default_packet_id()
    out_path = lane_dir / f"{packet_id}.json"

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

    packet = {
        "packet_id": packet_id,
        "title": title,
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
        "status": "archived" if args.lane == "archive" else args.lane,
        "history": [
            {
                "at": utc_now(),
                "event": "created:research",
                "note": f"created in lane={args.lane}",
            }
        ],
    }

    out_path.write_text(json.dumps(packet, ensure_ascii=True, indent=2) + "\n", encoding="utf-8")
    print(out_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
