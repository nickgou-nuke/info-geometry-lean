#!/usr/bin/env python3
"""Show lane counts for the knowledge injection subsystem."""

from __future__ import annotations

import argparse
from pathlib import Path

LANES = ("raw", "distilled", "translated", "gated", "accepted", "rejected", "archive")


def main() -> int:
    parser = argparse.ArgumentParser(description="Show injection lane status")
    parser.add_argument("--list", dest="list_lane", choices=LANES, help="List packets in a lane")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    injections = repo_root / "handover" / "injections"

    total = 0
    for lane in LANES:
        lane_dir = injections / lane
        lane_dir.mkdir(parents=True, exist_ok=True)
        files = sorted(p.name for p in lane_dir.glob("*.json"))
        total += len(files)
        print(f"{lane:10s} {len(files):4d}")

    print(f"{'total':10s} {total:4d}")

    if args.list_lane:
        lane_dir = injections / args.list_lane
        names = sorted(p.name for p in lane_dir.glob("*.json"))
        if not names:
            print(f"\n{args.list_lane}: (empty)")
        else:
            print(f"\n{args.list_lane}:")
            for n in names:
                print(f"  - {n}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
