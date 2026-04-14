#!/usr/bin/env python3
"""Promote injection claim packets between lifecycle lanes."""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[2]))

from tools.infra.injection_common import (
    LANES,
    acquire_packet_lock,
    append_history_event,
    check_transition_allowed,
    enforce_authority_tier_transition_gate,
    enforce_external_analogy_translation_gate,
    enforce_gated_gate,
    enforce_translation_gate,
    injections_root,
    repo_root,
    resolve_packet,
    run_and_record_build_targets,
    status_for_lane,
    utc_now,
    validate_packet_schema,
    write_json_atomic,
    write_run_manifest,
)


def main() -> int:
    parser = argparse.ArgumentParser(description="Promote an injection packet to another lane")
    parser.add_argument("packet", help="Packet id or path")
    parser.add_argument("--to", required=True, choices=LANES, help="Destination lane")
    parser.add_argument("--note", default="", help="History note")
    args = parser.parse_args()

    root = repo_root()
    injections = injections_root(root)
    src = resolve_packet(injections, args.packet)
    dst_dir = injections / args.to
    dst_dir.mkdir(parents=True, exist_ok=True)

    src_lane = src.parent.name
    if src_lane not in LANES:
        raise SystemExit(f"error: source packet not in lane directory: {src}")
    if src.name.endswith(".json"):
        packet_id = src.stem
    else:
        raise SystemExit(f"error: source packet must be .json: {src}")

    lock_owner = f"injection_promote:{os.getpid()}:{packet_id}:{src_lane}->{args.to}"
    with acquire_packet_lock(packet_id, lock_owner, block=True) as lock:
        check_transition_allowed(src_lane, args.to)

        packet = json.loads(src.read_text(encoding="utf-8"))
        validate_packet_schema(packet)
        enforce_authority_tier_transition_gate(packet, args.to)

        if args.to == "translated":
            if str(packet.get("authority_tier", "repo_native")) == "external_analogy":
                enforce_external_analogy_translation_gate(packet)
            else:
                enforce_translation_gate(packet)
        elif args.to == "gated":
            enforce_gated_gate(packet)
        elif args.to == "accepted":
            enforce_gated_gate(packet)
            run_and_record_build_targets(root, packet)

        packet["status"] = status_for_lane(args.to)
        append_history_event(
            packet,
            event=f"promoted:{src_lane}->{args.to}",
            note=args.note,
            at=utc_now(),
            idempotent=True,
        )
        validate_packet_schema(packet)

        dst = dst_dir / src.name
        write_json_atomic(dst, packet)
        if dst.resolve() != src.resolve():
            src.unlink()

        manifest_result = {"ok": True, "src_lane": src_lane, "dst_lane": args.to}
        if args.to == "accepted":
            verification_results = packet.get("verification_results", {})
            if isinstance(verification_results, dict):
                manifest_result["verification_results"] = verification_results
        write_run_manifest(
            root,
            packet=packet,
            stage=f"promote:{src_lane}->{args.to}",
            command_argv=list(os.sys.argv),
            result=manifest_result,
            extra={"lock_wait_sec": lock.wait_seconds, "note": args.note},
        )

    print(dst)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
