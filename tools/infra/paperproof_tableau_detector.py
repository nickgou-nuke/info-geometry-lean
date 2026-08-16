#!/usr/bin/env python3
"""Detect semantic-tableau-like proof strategy in Paperproof traces.

Paperproof's semantic-tableaux analogy is operationally useful:

  by_contra / contradiction entry
    -> negated goal becomes a hypothesis
    -> later goals often become `False`
    -> branches are closed by contradiction-like tactics

This detector labels that strategy shape for prompt routing and tactic-training
features.  It is heuristic metadata, not proof authority.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "info_geometry.paperproof_tableau_profile.v1"

ENTRY_TACTICS = {"by_contra", "by_contra!", "contrapose", "contrapose!", "by_cases"}
CLOSING_TACTICS = {"contradiction", "exfalso", "omega", "linarith", "nlinarith", "aesop", "tauto", "simp", "exact"}
BRANCHING_TACTICS = {"constructor", "apply", "cases", "cases'", "rcases", "induction", "induction'", "by_cases"}


# [lossless-compact] iter_jsonl folded into igf.common.json_io.iter_jsonl
from igf.common.json_io import iter_jsonl


def normalize(text: Any) -> str:
    return re.sub(r"\s+", " ", str(text or "")).strip()


def family(tactic: str) -> str:
    parts = tactic.strip().split()
    return parts[0] if parts else ""


def goal_text(goal: Any) -> str:
    if isinstance(goal, dict):
        return normalize(goal.get("pp") or goal.get("text") or goal.get("type") or goal.get("raw") or "")
    return normalize(goal)


def false_goal(goal: Any) -> bool:
    text = goal_text(goal)
    stripped = text.replace("⊢", "").strip()
    return stripped == "False" or stripped.endswith(": False") or "⊢ False" in text


def contradiction_like_tactic(tactic: str) -> bool:
    fam = family(tactic)
    if fam in {"contradiction", "exfalso"}:
        return True
    lowered = tactic.lower()
    return any(token in lowered for token in ("false.elim", "not.elim", "absurd", "contradiction"))


def step_profile(step: dict[str, Any]) -> dict[str, Any]:
    tactic = normalize(step.get("tactic"))
    fam = family(tactic)
    before = step.get("goals_before") if isinstance(step.get("goals_before"), list) else []
    after = step.get("goals_after") if isinstance(step.get("goals_after"), list) else []
    labels: list[str] = []
    if fam in ENTRY_TACTICS:
        labels.append("contradiction_entry")
    if any(false_goal(goal) for goal in before + after):
        labels.append("false_goal")
    if len(after) > len(before):
        labels.append("branching")
    if not after:
        labels.append("branch_closing")
    if contradiction_like_tactic(tactic) or fam in CLOSING_TACTICS and any(false_goal(goal) for goal in before):
        labels.append("contradiction_closure")
    return {
        "step_index": step.get("index"),
        "tactic": tactic,
        "tactic_family": fam,
        "goal_count_before": len(before),
        "goal_count_after": len(after),
        "labels": sorted(set(labels)),
    }


def profile_trace(packet: dict[str, Any]) -> dict[str, Any]:
    steps = [step for step in packet.get("steps") or [] if isinstance(step, dict)]
    step_profiles = [step_profile(step) for step in steps]
    entry_steps = [row for row in step_profiles if "contradiction_entry" in row["labels"]]
    false_goal_steps = [row for row in step_profiles if "false_goal" in row["labels"]]
    branch_steps = [row for row in step_profiles if "branching" in row["labels"]]
    closing_steps = [row for row in step_profiles if "branch_closing" in row["labels"]]
    contradiction_closures = [row for row in step_profiles if "contradiction_closure" in row["labels"]]

    strategy_labels: list[str] = []
    if entry_steps:
        strategy_labels.append("contradiction_entry")
    if false_goal_steps:
        strategy_labels.append("top_down_false_goal")
    if branch_steps:
        strategy_labels.append("branching_tableau")
    if contradiction_closures or closing_steps:
        strategy_labels.append("branch_closing")

    tableau_like = bool(entry_steps and (false_goal_steps or contradiction_closures or closing_steps))
    return {
        "schema": SCHEMA,
        "id": packet.get("id") or packet.get("theorem") or packet.get("source_file"),
        "source": packet.get("source"),
        "theorem": packet.get("theorem"),
        "source_file": packet.get("source_file"),
        "tableau_like": tableau_like,
        "entry_tactic": entry_steps[0]["tactic"] if entry_steps else None,
        "false_goal_steps": len(false_goal_steps),
        "branching_steps": len(branch_steps),
        "closing_steps": len(closing_steps),
        "contradiction_closure_steps": len(contradiction_closures),
        "strategy_labels": sorted(set(strategy_labels)),
        "steps": step_profiles,
        "authority": {
            "heuristic_strategy_label": True,
            "not_a_proof": True,
            "lean_remains_proof_authority": True,
        },
    }


# [lossless-compact] write_jsonl folded into igf.common.json_io.write_jsonl
from igf.common.json_io import write_jsonl


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paperproof-trace", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    profiles = [profile_trace(packet) for packet in iter_jsonl(args.paperproof_trace)]
    count = write_jsonl(args.out, profiles)
    print(
        json.dumps(
            {
                "schema": SCHEMA + ".summary",
                "out": str(args.out),
                "profiles": count,
                "tableau_like": sum(1 for row in profiles if row["tableau_like"]),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
