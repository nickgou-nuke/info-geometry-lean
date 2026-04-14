#!/usr/bin/env python3
"""Promote injection claim packets between lifecycle lanes."""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path

LANES = ("raw", "distilled", "translated", "gated", "accepted", "rejected", "archive")
STATUS_MAP = {"archive": "archived"}


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def status_for_lane(lane: str) -> str:
    return STATUS_MAP.get(lane, lane)


def resolve_packet(injections: Path, ref: str) -> Path:
    p = Path(ref)
    if p.exists():
        return p
    for lane in LANES:
        cand = injections / lane / f"{ref}.json"
        if cand.exists():
            return cand
    raise FileNotFoundError(f"packet not found for ref={ref}")


def main() -> int:
    parser = argparse.ArgumentParser(description="Promote an injection packet to another lane")
    parser.add_argument("packet", help="Packet id or path")
    parser.add_argument("--to", required=True, choices=LANES, help="Destination lane")
    parser.add_argument("--note", default="", help="History note")
    parser.add_argument("--allow-skip", action="store_true", help="Allow skipping forward multiple lanes")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    injections = repo_root / "handover" / "injections"
    src = resolve_packet(injections, args.packet)
    dst_dir = injections / args.to
    dst_dir.mkdir(parents=True, exist_ok=True)

    src_lane = src.parent.name
    if src_lane not in LANES:
        raise SystemExit(f"error: source packet not in lane directory: {src}")

    if not args.allow_skip:
        if abs(LANES.index(args.to) - LANES.index(src_lane)) > 1:
            raise SystemExit("error: lane skip blocked (use --allow-skip)")

    packet = json.loads(src.read_text(encoding="utf-8"))
    packet["status"] = status_for_lane(args.to)
    hist = packet.setdefault("history", [])
    hist.append(
        {
            "at": utc_now(),
            "event": f"promoted:{src_lane}->{args.to}",
            "note": args.note,
        }
    )

    dst = dst_dir / src.name
    dst.write_text(json.dumps(packet, ensure_ascii=True, indent=2) + "\n", encoding="utf-8")
    if dst.resolve() != src.resolve():
        src.unlink()

    print(dst)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
