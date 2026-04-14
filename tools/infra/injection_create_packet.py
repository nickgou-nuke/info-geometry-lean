#!/usr/bin/env python3
"""Create a new knowledge injection packet."""

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
    parser = argparse.ArgumentParser(description="Create an injection claim packet")
    parser.add_argument("--id", dest="packet_id", default=None, help="Explicit packet id")
    parser.add_argument("--title", required=True, help="Packet title")
    parser.add_argument("--source-type", default="manual", choices=["web", "chat", "manual", "llm", "paper", "other"])
    parser.add_argument("--source-ref", required=True, help="Source reference (url/chat id/note)")
    parser.add_argument(
        "--authority-tier",
        default="repo_native",
        choices=["repo_native", "external_analogy"],
        help="Authority tier for downstream promotion rules",
    )
    parser.add_argument("--raw-text", default="", help="Raw intake text")
    parser.add_argument("--lane", default="raw", choices=LANES)
    parser.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()

    root = repo_root()
    injections = injections_root(root)
    lane_dir = injections / args.lane
    lane_dir.mkdir(parents=True, exist_ok=True)

    packet_id = args.packet_id or default_packet_id()
    out_path = lane_dir / f"{packet_id}.json"

    lock_owner = f"injection_create:{os.getpid()}:{packet_id}"
    with acquire_packet_lock(packet_id, lock_owner, block=True) as lock:
        if out_path.exists() and not args.overwrite:
            raise SystemExit(f"error: packet exists: {out_path} (use --overwrite)")

        packet = {
            "packet_id": packet_id,
            "title": args.title,
            "authority_tier": args.authority_tier,
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
            "status": status_for_lane(args.lane),
            "history": [
                {
                    "at": utc_now(),
                    "event": "created",
                    "note": f"created in lane={args.lane}",
                }
            ],
        }

        validate_packet_schema(packet)
        write_json_atomic(out_path, packet)
        write_run_manifest(
            root,
            packet=packet,
            stage=f"create:{args.lane}",
            command_argv=list(os.sys.argv),
            result={"ok": True},
            extra={"lock_wait_sec": lock.wait_seconds, "lane": args.lane},
        )
    print(out_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
