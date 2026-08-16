#!/usr/bin/env python3
"""Candidate-bridge packet builder + validator.

This is the typed contract for classifying symbolic correspondences into one of:
- equivalence
- obstruction
- discard
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def slug(text: str) -> str:
    out = re.sub(r"[^a-zA-Z0-9]+", "-", text.strip().lower()).strip("-")
    return out[:64] or "bridge"


def _uniq(items: list[str]) -> list[str]:
    seen = set()
    out = []
    for x in items:
        s = str(x).strip()
        if not s or s in seen:
            continue
        seen.add(s)
        out.append(s)
    return out


# [lossless-compact] load_json folded into igf.common.json_io.load_json
from igf.common.json_io import load_json


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def default_forbidden_moves() -> list[str]:
    return [
        "treat symbolic analogy as theorem without an explicit map",
        "collapse metric and spectral support by definition",
        "drop mismatch objects when preservation fails",
        "change owner meaning to force bridge closure",
    ]


def build_packet(args: argparse.Namespace) -> dict[str, Any]:
    packet_id = args.packet_id.strip()
    if not packet_id:
        packet_id = f"cbp-{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')}-{slug(args.claimed_invariant)}"

    packet: dict[str, Any] = {
        "packet_id": packet_id,
        "created_at": utc_now(),
        "source_owner_surfaces": _uniq(args.source_owner or []),
        "target_owner_surfaces": _uniq(args.target_owner or []),
        "claimed_invariant": args.claimed_invariant.strip(),
        "proposed_map": {
            "map_kind": args.map_kind.strip(),
            "map_expression": args.map_expression.strip(),
        },
        "outcome_class": args.outcome_class.strip(),
        "evidence_refs": _uniq(args.evidence_ref or []),
        "unresolved_assumptions": _uniq(args.unresolved_assumption or []),
        "forbidden_moves": default_forbidden_moves(),
        "status": args.status.strip(),
    }

    if args.source_packet:
        packet["provenance"] = {"source_packet": args.source_packet.strip()}
    if args.provenance_note:
        packet.setdefault("provenance", {})
        packet["provenance"]["note"] = args.provenance_note.strip()

    if args.outcome_class in {"equivalence", "obstruction"}:
        packet["theorem_target"] = {
            "kind": args.theorem_kind.strip(),
            "name": args.theorem_name.strip(),
        }
        if args.theorem_note:
            packet["theorem_target"]["note"] = args.theorem_note.strip()

    if args.outcome_class == "obstruction":
        packet["mismatch_object"] = {
            "name": args.mismatch_name.strip(),
            "preservation_gap": args.mismatch_gap.strip(),
        }
        if args.mismatch_note:
            packet["mismatch_object"]["note"] = args.mismatch_note.strip()

    if args.outcome_class == "discard":
        packet["discard_reason"] = args.discard_reason.strip()

    return packet


def validate_packet(packet: Any) -> list[str]:
    errs: list[str] = []
    if not isinstance(packet, dict):
        return ["packet must be a JSON object"]

    req_top = [
        "packet_id",
        "created_at",
        "source_owner_surfaces",
        "target_owner_surfaces",
        "claimed_invariant",
        "proposed_map",
        "outcome_class",
        "unresolved_assumptions",
        "status",
    ]
    for k in req_top:
        if k not in packet:
            errs.append(f"missing required field: {k}")

    for lane in ("source_owner_surfaces", "target_owner_surfaces"):
        val = packet.get(lane)
        if not isinstance(val, list) or not any(str(x).strip() for x in val):
            errs.append(f"{lane} must be a non-empty array")

    inv = str(packet.get("claimed_invariant", "")).strip()
    if not inv:
        errs.append("claimed_invariant missing")

    pm = packet.get("proposed_map")
    if not isinstance(pm, dict):
        errs.append("proposed_map must be object")
    else:
        kind = str(pm.get("map_kind", "")).strip()
        if kind not in {"equivalence", "intertwiner", "functor", "natural_transformation", "translator", "coherence"}:
            errs.append(f"invalid proposed_map.map_kind: {kind}")
        expr = str(pm.get("map_expression", "")).strip()
        if not expr:
            errs.append("proposed_map.map_expression missing")

    outcome = str(packet.get("outcome_class", "")).strip()
    if outcome not in {"equivalence", "obstruction", "discard"}:
        errs.append(f"invalid outcome_class: {outcome}")

    status = str(packet.get("status", "")).strip()
    if status not in {"draft", "stabilization", "admitted", "rejected"}:
        errs.append(f"invalid status: {status}")

    unresolved = packet.get("unresolved_assumptions", [])
    if not isinstance(unresolved, list):
        errs.append("unresolved_assumptions must be array")

    theorem_target = packet.get("theorem_target")
    if outcome in {"equivalence", "obstruction"}:
        if not isinstance(theorem_target, dict):
            errs.append("theorem_target required for equivalence/obstruction")
        else:
            t_kind = str(theorem_target.get("kind", "")).strip()
            if t_kind not in {"theorem", "lemma", "coherence", "definition"}:
                errs.append(f"invalid theorem_target.kind: {t_kind}")
            t_name = str(theorem_target.get("name", "")).strip()
            if not t_name:
                errs.append("theorem_target.name missing")

    mismatch = packet.get("mismatch_object")
    if outcome == "equivalence" and mismatch is not None:
        errs.append("mismatch_object must be absent for equivalence")
    if outcome == "obstruction":
        if not isinstance(mismatch, dict):
            errs.append("mismatch_object required for obstruction")
        else:
            m_name = str(mismatch.get("name", "")).strip()
            m_gap = str(mismatch.get("preservation_gap", "")).strip()
            if not m_name:
                errs.append("mismatch_object.name missing")
            if not m_gap:
                errs.append("mismatch_object.preservation_gap missing")

    discard_reason = str(packet.get("discard_reason", "")).strip()
    if outcome == "discard" and not discard_reason:
        errs.append("discard_reason required for discard")

    return errs


def cmd_build(args: argparse.Namespace) -> int:
    out = Path(args.out)
    packet = build_packet(args)
    errs = validate_packet(packet)
    if errs:
        print("ERROR: built candidate bridge packet failed validation:", file=sys.stderr)
        for e in errs:
            print(f"  - {e}", file=sys.stderr)
        return 3
    write_json(out, packet)
    print(f"candidate bridge packet written: {out}")
    return 0


def cmd_validate(args: argparse.Namespace) -> int:
    pkt_path = Path(args.packet)
    if not pkt_path.exists():
        print(f"ERROR: packet not found: {pkt_path}", file=sys.stderr)
        return 2
    packet = load_json(pkt_path)
    errs = validate_packet(packet)
    if errs:
        print("INVALID candidate bridge packet")
        for e in errs:
            print(f"- {e}")
        return 1
    print("VALID candidate bridge packet")
    return 0


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    sp = p.add_subparsers(dest="cmd", required=True)

    p_build = sp.add_parser("build", help="Build typed candidate-bridge packet.")
    p_build.add_argument("--out", required=True, help="Output packet JSON path.")
    p_build.add_argument("--packet-id", default="", help="Optional explicit packet id.")
    p_build.add_argument("--source-owner", action="append", default=[], help="Source owner file/surface (repeatable).")
    p_build.add_argument("--target-owner", action="append", default=[], help="Target owner file/surface (repeatable).")
    p_build.add_argument("--claimed-invariant", required=True, help="Invariant proposed to be preserved by the map.")
    p_build.add_argument(
        "--map-kind",
        default="translator",
        choices=["equivalence", "intertwiner", "functor", "natural_transformation", "translator", "coherence"],
        help="Declared map kind.",
    )
    p_build.add_argument("--map-expression", required=True, help="Explicit proposed map expression or symbolic surface.")
    p_build.add_argument(
        "--outcome-class",
        required=True,
        choices=["equivalence", "obstruction", "discard"],
        help="Current classification outcome.",
    )
    p_build.add_argument(
        "--theorem-kind",
        default="theorem",
        choices=["theorem", "lemma", "coherence", "definition"],
        help="Theorem target kind for equivalence/obstruction.",
    )
    p_build.add_argument("--theorem-name", default="", help="Theorem target name for equivalence/obstruction.")
    p_build.add_argument("--theorem-note", default="", help="Optional theorem note.")
    p_build.add_argument("--mismatch-name", default="", help="Mismatch object name for obstruction.")
    p_build.add_argument("--mismatch-gap", default="", help="Invariant-preservation gap for obstruction.")
    p_build.add_argument("--mismatch-note", default="", help="Optional mismatch note.")
    p_build.add_argument("--discard-reason", default="", help="Discard reason when outcome_class=discard.")
    p_build.add_argument("--evidence-ref", action="append", default=[], help="Evidence reference path/url (repeatable).")
    p_build.add_argument("--unresolved-assumption", action="append", default=[], help="Unresolved assumption (repeatable).")
    p_build.add_argument("--source-packet", default="", help="Optional source packet identifier/path.")
    p_build.add_argument("--provenance-note", default="", help="Optional provenance note.")
    p_build.add_argument(
        "--status",
        default="draft",
        choices=["draft", "stabilization", "admitted", "rejected"],
        help="Packet status.",
    )

    p_val = sp.add_parser("validate", help="Validate candidate-bridge packet JSON.")
    p_val.add_argument("--packet", required=True, help="Path to packet JSON.")
    return p.parse_args()


def main() -> None:
    args = parse_args()
    if args.cmd == "build":
        rc = cmd_build(args)
    elif args.cmd == "validate":
        rc = cmd_validate(args)
    else:
        rc = 2
    raise SystemExit(rc)


if __name__ == "__main__":
    main()
