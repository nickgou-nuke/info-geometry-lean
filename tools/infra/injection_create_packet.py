#!/usr/bin/env python3
"""Create a new knowledge injection packet."""

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
    parser = argparse.ArgumentParser(description="Create an injection claim packet")
    parser.add_argument("--id", dest="packet_id", default=None, help="Explicit packet id")
    parser.add_argument("--title", required=True, help="Packet title")
    parser.add_argument("--source-type", default="manual", choices=["web", "chat", "manual", "llm", "paper", "other"])
    parser.add_argument("--source-ref", required=True, help="Source reference (url/chat id/note)")
    parser.add_argument("--raw-text", default="", help="Raw intake text")
    parser.add_argument("--lane", default="raw", choices=LANES)
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

    packet = {
        "packet_id": packet_id,
        "title": args.title,
        "source": {
            "type": args.source_type,
            "ref": args.source_ref,
            "date": utc_now(),
        },
        "raw_text": args.raw_text,
        "distilled_claim": "",
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
                "event": "created",
                "note": f"created in lane={args.lane}",
            }
        ],
    }

    out_path.write_text(json.dumps(packet, ensure_ascii=True, indent=2) + "\n", encoding="utf-8")
    print(out_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
