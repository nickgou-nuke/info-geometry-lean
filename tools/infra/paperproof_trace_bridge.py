#!/usr/bin/env python3
"""Render proof-state telemetry as Paperproof-style proof-history packets.

This is a lightweight bridge inspired by Paperproof's proof visualization
model: hypotheses, goals, tactics, and scope-like context are made explicit for
human review and LLM prompt packets.

It is not Paperproof itself, does not require the VS Code extension, and does
not prove anything.  Lean/Jixia/InfoTree telemetry remains the source of truth.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "info_geometry.paperproof_trace.v1"


def iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    if not path.exists():
        return
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except Exception:
                continue
            if isinstance(row, dict):
                yield row


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
            count += 1
    return count


def goal_pp(goal: Any) -> str:
    if isinstance(goal, dict):
        return str(goal.get("pp") or goal.get("type") or "")
    return str(goal or "")


def hypothesis_from_context(item: Any, idx: int) -> dict[str, Any]:
    if isinstance(item, dict):
        name = item.get("userName") or item.get("name") or item.get("fvarId") or f"h{idx}"
        return {
            "name": str(name),
            "type": str(item.get("type") or item.get("pp") or ""),
            "raw": item,
        }
    return {"name": f"h{idx}", "type": str(item), "raw": item}


def hypotheses_from_goals(goals: list[Any]) -> list[dict[str, Any]]:
    seen: set[tuple[str, str]] = set()
    out: list[dict[str, Any]] = []
    for goal in goals:
        if not isinstance(goal, dict):
            continue
        context = goal.get("context")
        if not isinstance(context, list):
            continue
        for idx, item in enumerate(context):
            hyp = hypothesis_from_context(item, idx)
            key = (hyp["name"], hyp["type"])
            if key not in seen:
                seen.add(key)
                out.append(hyp)
    return out


def step_from_jixia(row: dict[str, Any], idx: int) -> dict[str, Any] | None:
    tactic = str(row.get("tactic_syntax") or "").strip()
    before = row.get("before") if isinstance(row.get("before"), list) else []
    after = row.get("after") if isinstance(row.get("after"), list) else []
    if not tactic and not before and not after:
        return None
    return {
        "index": idx,
        "source": "jixia",
        "tactic": tactic,
        "range": row.get("range"),
        "references": row.get("references") if isinstance(row.get("references"), list) else [],
        "hypotheses_before": hypotheses_from_goals(before),
        "goals_before": [{"pp": goal_pp(goal), "raw": goal} for goal in before],
        "hypotheses_after": hypotheses_from_goals(after),
        "goals_after": [{"pp": goal_pp(goal), "raw": goal} for goal in after],
        "solved": len(after) == 0,
    }


def step_from_sft(row: dict[str, Any], idx: int) -> dict[str, Any] | None:
    tactic = str(row.get("tactic") or "").strip()
    goal_before = str(row.get("goal_before") or "").strip()
    goal_after = str(row.get("goal_after") or "").strip()
    if not tactic and not goal_before and not goal_after:
        return None
    return {
        "index": idx,
        "source": str(row.get("source") or "tactic_sft"),
        "tactic": tactic,
        "range": None,
        "references": (row.get("context") or {}).get("dependencies", []) if isinstance(row.get("context"), dict) else [],
        "hypotheses_before": [],
        "goals_before": [{"pp": goal_before, "raw": goal_before}] if goal_before else [],
        "hypotheses_after": [],
        "goals_after": [] if goal_after == "no goals" else ([{"pp": goal_after, "raw": goal_after}] if goal_after else []),
        "solved": goal_after == "no goals" or goal_after == "",
    }


def group_key(row: dict[str, Any]) -> str:
    theorem = row.get("theorem") or row.get("theoremFullName") or row.get("declaration")
    if theorem:
        return str(theorem)
    source_file = row.get("source_file") or row.get("lean_file") or row.get("leanFile")
    if source_file:
        return str(source_file)
    return "unknown"


def packet_for_group(key: str, rows: list[dict[str, Any]], *, source: str) -> dict[str, Any]:
    steps: list[dict[str, Any]] = []
    for idx, row in enumerate(rows):
        step = step_from_jixia(row, idx) if source == "jixia" else step_from_sft(row, idx)
        if step is not None:
            steps.append(step)
    first = rows[0] if rows else {}
    return {
        "schema": SCHEMA,
        "id": key,
        "source": source,
        "theorem": first.get("theorem") or first.get("theoremFullName") or first.get("declaration") or "",
        "source_file": first.get("source_file") or first.get("lean_file") or first.get("leanFile") or "",
        "step_count": len(steps),
        "steps": steps,
        "authority": {
            "paperproof_style_visualization": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }


def build_packets(*, jixia_tactics: list[Path], sft: list[Path]) -> list[dict[str, Any]]:
    packets: list[dict[str, Any]] = []
    for path in jixia_tactics:
        groups: dict[str, list[dict[str, Any]]] = defaultdict(list)
        for row in iter_jsonl(path):
            groups[group_key(row)].append(row)
        packets.extend(packet_for_group(key, rows, source="jixia") for key, rows in sorted(groups.items()))
    for path in sft:
        groups: dict[str, list[dict[str, Any]]] = defaultdict(list)
        for row in iter_jsonl(path):
            groups[group_key(row)].append(row)
        packets.extend(packet_for_group(key, rows, source="tactic_sft") for key, rows in sorted(groups.items()))
    return packets


def render_markdown(packets: list[dict[str, Any]]) -> str:
    lines: list[str] = ["# Paperproof-Style Proof History", ""]
    lines.append("These packets are visualization/prompt context only; Lean remains proof authority.")
    lines.append("")
    for packet in packets:
        title = packet.get("theorem") or packet.get("source_file") or packet.get("id")
        lines.append(f"## `{title}`")
        lines.append("")
        lines.append(f"- Source: `{packet.get('source')}`")
        lines.append(f"- Steps: `{packet.get('step_count')}`")
        lines.append("")
        for step in packet.get("steps") or []:
            lines.append(f"### Step {step.get('index')}: `{step.get('tactic')}`")
            lines.append("")
            if step.get("hypotheses_before"):
                lines.append("Hypotheses before:")
                for hyp in step["hypotheses_before"]:
                    lines.append(f"- `{hyp.get('name')}` : `{hyp.get('type')}`")
            if step.get("goals_before"):
                lines.append("Goals before:")
                for goal in step["goals_before"]:
                    lines.append(f"- `{goal.get('pp')}`")
            if step.get("goals_after"):
                lines.append("Goals after:")
                for goal in step["goals_after"]:
                    lines.append(f"- `{goal.get('pp')}`")
            else:
                lines.append("Goals after: `no goals`")
            lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jixia-tactics", type=Path, action="append", default=[])
    parser.add_argument("--sft", type=Path, action="append", default=[])
    parser.add_argument("--out-jsonl", type=Path, required=True)
    parser.add_argument("--out-md", type=Path)
    args = parser.parse_args()

    packets = build_packets(jixia_tactics=args.jixia_tactics, sft=args.sft)
    count = write_jsonl(args.out_jsonl, packets)
    if args.out_md:
        args.out_md.parent.mkdir(parents=True, exist_ok=True)
        args.out_md.write_text(render_markdown(packets), encoding="utf-8")
    print(json.dumps({"schema": SCHEMA + ".summary", "packets": count}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
