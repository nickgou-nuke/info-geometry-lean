#!/usr/bin/env python3
"""Compare Paperproof-style proof packets with Jixia tactic transitions.

This is an audit tool for proof-state extraction quality.  It treats both
Paperproof-style packets and Jixia rows as telemetry, not proof authority.

The intended loop is:

  Jixia tactic transitions
    -> paperproof_trace_bridge.py
    -> paperproof_jixia_compare.py

If later we add direct Paperproof RPC exports, this script can compare those
packets against the same Jixia transition rows without changing the report
shape.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "info_geometry.paperproof_jixia_compare.v1"


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


def normalize_text(value: Any) -> str:
    return re.sub(r"\s+", " ", str(value or "")).strip()


def stable_hash(value: Any) -> str:
    text = json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
    return hashlib.sha1(text.encode("utf-8")).hexdigest()


def range_key(value: Any) -> str:
    if value is None:
        return ""
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))


def goal_pps_from_jixia(goals: Any) -> list[str]:
    if not isinstance(goals, list):
        return []
    out: list[str] = []
    for goal in goals:
        if isinstance(goal, dict):
            out.append(normalize_text(goal.get("pp") or goal.get("type") or ""))
        else:
            out.append(normalize_text(goal))
    return out


def goal_pps_from_paperproof(goals: Any) -> list[str]:
    if not isinstance(goals, list):
        return []
    out: list[str] = []
    for goal in goals:
        if isinstance(goal, dict):
            out.append(normalize_text(goal.get("pp") or goal.get("raw") or ""))
        else:
            out.append(normalize_text(goal))
    return out


def source_key(row: dict[str, Any]) -> str:
    return str(row.get("source_file") or row.get("lean_file") or row.get("leanFile") or row.get("theorem") or row.get("id") or "unknown")


def step_signature(*, tactic: str, rng: Any, before: list[str], after: list[str]) -> tuple[str, str, str, str]:
    return (
        normalize_text(tactic),
        range_key(rng),
        stable_hash(before),
        stable_hash(after),
    )


def load_jixia_steps(path: Path) -> dict[str, list[dict[str, Any]]]:
    groups: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in iter_jsonl(path):
        before = goal_pps_from_jixia(row.get("before"))
        after = goal_pps_from_jixia(row.get("after"))
        step = {
            "tactic": normalize_text(row.get("tactic_syntax")),
            "range": row.get("range"),
            "before": before,
            "after": after,
            "signature": step_signature(tactic=row.get("tactic_syntax"), rng=row.get("range"), before=before, after=after),
        }
        groups[source_key(row)].append(step)
    return groups


def load_paperproof_steps(path: Path) -> dict[str, list[dict[str, Any]]]:
    groups: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for packet in iter_jsonl(path):
        key = source_key(packet)
        for row in packet.get("steps") or []:
            if not isinstance(row, dict):
                continue
            before = goal_pps_from_paperproof(row.get("goals_before"))
            after = goal_pps_from_paperproof(row.get("goals_after"))
            step = {
                "tactic": normalize_text(row.get("tactic")),
                "range": row.get("range"),
                "before": before,
                "after": after,
                "signature": step_signature(tactic=row.get("tactic"), rng=row.get("range"), before=before, after=after),
            }
            groups[key].append(step)
    return groups


def multiset_overlap(left: Iterable[Any], right: Iterable[Any]) -> int:
    a = Counter(left)
    b = Counter(right)
    return sum((a & b).values())


def compare_groups(
    paperproof: dict[str, list[dict[str, Any]]],
    jixia: dict[str, list[dict[str, Any]]],
) -> list[dict[str, Any]]:
    keys = sorted(set(paperproof) | set(jixia))
    rows: list[dict[str, Any]] = []
    for key in keys:
        psteps = paperproof.get(key, [])
        jsteps = jixia.get(key, [])
        rows.append(
            {
                "source_key": key,
                "paperproof_steps": len(psteps),
                "jixia_steps": len(jsteps),
                "step_count_delta": len(psteps) - len(jsteps),
                "exact_signature_matches": multiset_overlap(
                    (step["signature"] for step in psteps),
                    (step["signature"] for step in jsteps),
                ),
                "tactic_text_matches": multiset_overlap(
                    (step["tactic"] for step in psteps),
                    (step["tactic"] for step in jsteps),
                ),
                "range_matches": multiset_overlap(
                    (range_key(step["range"]) for step in psteps if step.get("range") is not None),
                    (range_key(step["range"]) for step in jsteps if step.get("range") is not None),
                ),
                "before_goal_matches": multiset_overlap(
                    (stable_hash(step["before"]) for step in psteps),
                    (stable_hash(step["before"]) for step in jsteps),
                ),
                "after_goal_matches": multiset_overlap(
                    (stable_hash(step["after"]) for step in psteps),
                    (stable_hash(step["after"]) for step in jsteps),
                ),
            }
        )
    return rows


def build_report(*, paperproof_trace: Path, jixia_tactics: Path) -> dict[str, Any]:
    paperproof = load_paperproof_steps(paperproof_trace)
    jixia = load_jixia_steps(jixia_tactics)
    comparisons = compare_groups(paperproof, jixia)
    return {
        "schema": SCHEMA,
        "paperproof_trace": str(paperproof_trace),
        "jixia_tactics": str(jixia_tactics),
        "groups": len(comparisons),
        "totals": {
            "paperproof_steps": sum(row["paperproof_steps"] for row in comparisons),
            "jixia_steps": sum(row["jixia_steps"] for row in comparisons),
            "exact_signature_matches": sum(row["exact_signature_matches"] for row in comparisons),
            "tactic_text_matches": sum(row["tactic_text_matches"] for row in comparisons),
            "range_matches": sum(row["range_matches"] for row in comparisons),
            "before_goal_matches": sum(row["before_goal_matches"] for row in comparisons),
            "after_goal_matches": sum(row["after_goal_matches"] for row in comparisons),
        },
        "comparisons": comparisons,
        "authority": {
            "telemetry_audit_only": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }


def render_markdown(report: dict[str, Any]) -> str:
    totals = report["totals"]
    lines = [
        "# Paperproof/Jixia Proof-State Extraction Audit",
        "",
        "This report compares telemetry shape only. Lean remains proof authority.",
        "",
        "## Totals",
        "",
        f"- Paperproof-style steps: `{totals['paperproof_steps']}`",
        f"- Jixia steps: `{totals['jixia_steps']}`",
        f"- Exact signature matches: `{totals['exact_signature_matches']}`",
        f"- Tactic text matches: `{totals['tactic_text_matches']}`",
        f"- Range matches: `{totals['range_matches']}`",
        f"- Before-goal matches: `{totals['before_goal_matches']}`",
        f"- After-goal matches: `{totals['after_goal_matches']}`",
        "",
        "## Groups",
        "",
    ]
    for row in report["comparisons"]:
        lines.append(f"### `{row['source_key']}`")
        lines.append("")
        lines.append(f"- Paperproof-style steps: `{row['paperproof_steps']}`")
        lines.append(f"- Jixia steps: `{row['jixia_steps']}`")
        lines.append(f"- Step count delta: `{row['step_count_delta']}`")
        lines.append(f"- Exact signature matches: `{row['exact_signature_matches']}`")
        lines.append(f"- Tactic text matches: `{row['tactic_text_matches']}`")
        lines.append(f"- Range matches: `{row['range_matches']}`")
        lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paperproof-trace", type=Path, required=True)
    parser.add_argument("--jixia-tactics", type=Path, required=True)
    parser.add_argument("--out-json", type=Path, required=True)
    parser.add_argument("--out-md", type=Path)
    args = parser.parse_args()

    report = build_report(paperproof_trace=args.paperproof_trace, jixia_tactics=args.jixia_tactics)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(report, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    if args.out_md:
        args.out_md.parent.mkdir(parents=True, exist_ok=True)
        args.out_md.write_text(render_markdown(report), encoding="utf-8")
    print(json.dumps({"schema": SCHEMA + ".summary", "groups": report["groups"], **report["totals"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
