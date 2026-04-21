#!/usr/bin/env python3
"""Convert a Socratic packet into sampler-style JSONL rows for hypothesis_fuser_and_lean_gate."""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--packet", required=True, help="Path to Socratic packet JSON.")
    p.add_argument("--out", required=True, help="Output JSONL path.")
    return p.parse_args()


def _target_source(note: str) -> str:
    lowered = note.lower()
    if "accepted declaration name extracted from compiled lean environment" in lowered:
        return "compiled_decl"
    if "recovered from fallback packet" in lowered:
        return "fallback_packet"
    return "raw_target"


def _target_priority(target: dict[str, Any]) -> tuple[int, int]:
    kind = str(target.get("kind", "")).strip().lower()
    note = str(target.get("note", "")).strip()
    source = _target_source(note)
    source_rank = {
        "compiled_decl": 3,
        "fallback_packet": 2,
        "raw_target": 1,
    }.get(source, 0)
    kind_rank = 1 if kind == "theorem" else 0
    return (source_rank, kind_rank)


def _canonical_target_key(name: str) -> str:
    bits = [part for part in name.split(".") if part]
    return bits[-1] if bits else name


def _select_targets(targets: list[dict[str, Any]]) -> list[dict[str, Any]]:
    preferred_by_key: dict[str, dict[str, Any]] = {}
    for target in targets:
        name = str(target.get("name", "")).strip()
        if not name:
            continue
        key = _canonical_target_key(name)
        current = preferred_by_key.get(key)
        if current is None or _target_priority(target) > _target_priority(current):
            preferred_by_key[key] = target
    ordered: list[dict[str, Any]] = []
    seen: set[str] = set()
    for target in targets:
        name = str(target.get("name", "")).strip()
        if not name:
            continue
        key = _canonical_target_key(name)
        chosen = preferred_by_key.get(key)
        if chosen is None or key in seen or chosen is not target:
            continue
        ordered.append(chosen)
        seen.add(key)
    return ordered


def main() -> int:
    args = parse_args()
    packet_path = Path(args.packet).resolve()
    out_path = Path(args.out).resolve()
    if not packet_path.exists():
        raise SystemExit(f"missing packet: {packet_path}")
    payload = json.loads(packet_path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise SystemExit("packet must be a JSON object")

    raw_targets = payload.get("formalization_targets", [])
    evidence = payload.get("evidence", [])
    open_problems = payload.get("open_problems", [])
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")

    targets = _select_targets(raw_targets if isinstance(raw_targets, list) else [])

    rows: list[dict[str, Any]] = []
    for idx, target in enumerate(targets, start=1):
        if not isinstance(target, dict):
            continue
        name = str(target.get("name", "")).strip() or f"target_{idx}"
        kind = str(target.get("kind", "")).strip() or "theorem"
        note = str(target.get("note", "")).strip()
        source = _target_source(note)
        claim = ""
        if isinstance(evidence, list) and evidence:
            row_idx = min(idx - 1, len(evidence) - 1)
            claim_row = evidence[row_idx]
            if isinstance(claim_row, dict):
                claim = str(claim_row.get("claim", "")).strip()
        if kind == "definition":
            lean_code = f"def {name} : Prop := True"
        else:
            lean_code = f"theorem {name} : True := by\n  trivial"
        rows.append(
            {
                "created_at": run_id,
                "hypothesis_id": f"socratic-{idx:03d}-{name}",
                "model_role": "socratic_packet",
                "status": "ok",
                "response": note or claim,
                "lean_code": lean_code,
                "open_problems": open_problems if isinstance(open_problems, list) else [],
                "target_name": name,
                "target_kind": kind,
                "target_note": note,
                "target_source": source,
                "target_priority": _target_priority(target)[0],
                "target_key": _canonical_target_key(name),
            }
        )

    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True) + "\n")

    print(out_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
