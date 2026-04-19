#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra import research_packet

DEFAULT_INPUT = ROOT / "artifacts" / "leandojo" / "lean_progress_sample.jsonl"
DEFAULT_OUT_DIR = ROOT / "quarantine" / "hermes_memory" / "research_packets"

FORBIDDEN_MOVES = [
    "treat LeanProgress sample rows as theorem closure",
    "promote tactic text without Lean compilation",
    "convert sorry-bearing candidates directly into canonical statements",
    "treat local sample data as external evidence",
]


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def slug(text: str) -> str:
    out = re.sub(r"[^a-zA-Z0-9]+", "-", text.strip().lower()).strip("-")
    return out[:64] or "leanprogress"


def load_jsonl(path: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            rows.append(json.loads(line))
    return rows


def build_packet(row: dict[str, object], *, idx: int, source_path: Path) -> dict[str, object]:
    goal = str(row.get("goal", "")).strip()
    prefix = str(row.get("prefix", "")).strip()
    tactic = str(row.get("tactic", "")).strip()
    steps_remaining = int(row.get("steps_remaining", 0) or 0)

    packet_id = f"ldj-progress-{idx:03d}-{slug(goal)}"
    candidate_name = f"leanprogress_{idx:03d}_{slug(goal).replace('-', '_')}"

    evidence_summary = (
        f"LeanProgress local row with steps_remaining={steps_remaining}; "
        f"prefix_present={'yes' if prefix else 'no'}; tactic_present={'yes' if tactic else 'no'}."
    )

    facts = []
    interpretations = [
        f"Local LeanProgress sample row for goal: {goal}",
        f"Candidate tactic: {tactic}" if tactic else "No tactic recorded",
        f"Estimated steps remaining: {steps_remaining}",
    ]
    formalization_candidates = []
    if tactic and tactic != "sorry":
        formalization_candidates.append(
            f"Try tactic `{tactic}` against goal `{goal}` with {steps_remaining} steps remaining."
        )
    if tactic == "sorry":
        interpretations.append("This row contains `sorry` and must remain quarantine-only.")

    packet = {
        "packet_id": packet_id,
        "created_at": utc_now(),
        "research_goal": f"Investigate LeanProgress-guided proof attempt for goal: {goal}",
        "allowed_sources": ["files"],
        "trusted_domains": [],
        "provenance": {
            "source": "LeanDojoTokenFree.LeanProgress",
            "state_path": str(source_path),
            "models": {
                "planner": "hermes",
                "research": "deepseek-prover-v2-7b-q8_0.gguf",
                "verifier": "lean",
                "writer": "codex-cli",
            },
        },
        "evidence": [
            {
                "claim": f"Lean goal observed: {goal}",
                "sources": [str(source_path)],
                "confidence": "medium",
                "evidence_summary": evidence_summary,
                "subquestion_id": f"goal-{idx:03d}",
            },
            {
                "claim": f"Candidate tactic is `{tactic}`." if tactic else "No tactic proposed.",
                "sources": [str(source_path)],
                "confidence": "medium",
                "evidence_summary": evidence_summary,
                "subquestion_id": f"tactic-{idx:03d}",
            },
        ],
        "contradictions": [],
        "candidate_invariants": [],
        "forbidden_moves": FORBIDDEN_MOVES,
        "formalization_targets": [
            {
                "kind": "theorem",
                "name": candidate_name,
                "note": f"LeanProgress-derived candidate for goal `{goal}`.",
            }
        ],
        "classification": {
            "facts": facts,
            "interpretations": interpretations,
            "metaphors": [],
            "formalization_candidates": formalization_candidates,
        },
        "handoff": {
            "prompt_a_ready": True,
            "requires_nemoclaw_note": True,
            "requires_clawcode_gate": True,
        },
        "status": "draft",
    }
    return packet


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Convert LeanProgress-style JSONL rows into Hermes research packets."
    )
    parser.add_argument(
        "--input",
        type=Path,
        default=DEFAULT_INPUT,
        help="Input LeanProgress JSONL (default: artifacts/leandojo/lean_progress_sample.jsonl)",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=DEFAULT_OUT_DIR,
        help="Output packet directory (default: quarantine/hermes_memory/research_packets)",
    )
    args = parser.parse_args()

    rows = load_jsonl(args.input)
    args.out_dir.mkdir(parents=True, exist_ok=True)

    manifest: list[dict[str, object]] = []
    for idx, row in enumerate(rows, start=1):
        packet = build_packet(row, idx=idx, source_path=args.input)
        errors = research_packet.validate_packet(packet)
        if errors:
            raise SystemExit(
                f"generated packet {packet['packet_id']} failed validation: {'; '.join(errors)}"
            )
        out_path = args.out_dir / f"{packet['packet_id']}.json"
        research_packet.write_json(out_path, packet)
        manifest.append(
            {
                "packet_id": packet["packet_id"],
                "path": str(out_path),
                "research_goal": packet["research_goal"],
            }
        )

    manifest_path = args.out_dir / "leanprogress_manifest.json"
    research_packet.write_json(
        manifest_path,
        {
            "schema": "leanprogress_to_hermes_manifest.v1",
            "generated_at": utc_now(),
            "input": str(args.input),
            "count": len(manifest),
            "packets": manifest,
        },
    )
    print(f"wrote {len(manifest)} packet(s) to {args.out_dir}")
    print(f"wrote manifest {manifest_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
