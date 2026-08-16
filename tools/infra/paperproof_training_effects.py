#!/usr/bin/env python3
"""Label tactic effects from Paperproof-style proof-history packets.

The labels are intentionally conservative and heuristic.  They are training
features for local LLM/reranker work, not proof authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Iterable


SCHEMA = "info_geometry.paperproof_tactic_effect.v1"


# [lossless-compact] iter_jsonl folded into igf.common.json_io.iter_jsonl
from igf.common.json_io import iter_jsonl


# [lossless-compact] stable_hash folded into igf.common.hashing.stable_hash
from igf.common.hashing import stable_hash


def family(tactic: str) -> str:
    words = tactic.strip().split()
    return words[0] if words else ""


def normalize_goal_count(value: Any) -> int:
    return len(value) if isinstance(value, list) else 0


def effect_labels(tactic: str, before_count: int, after_count: int, hyp_before: int, hyp_after: int) -> list[str]:
    fam = family(tactic)
    labels: list[str] = []
    lowered = tactic.lower()
    if after_count == 0:
        labels.append("closes_goal")
    if after_count > before_count:
        labels.append("splits_goal")
    if hyp_after > hyp_before:
        labels.append("adds_hypothesis")
    if fam in {"by_contra", "by_contra!", "contrapose", "contrapose!"}:
        labels.append("starts_tableau_mode")
        labels.append("contradiction_entry")
    elif fam in {"intro", "rintro", "intros"}:
        labels.append("introduces_binder")
    elif fam in {"constructor", "constructor'"}:
        labels.append("constructs_goal")
    elif fam in {"rw", "rewrite", "simp", "simpa", "simp_all"}:
        labels.append("rewrites_or_simplifies")
    elif fam in {"apply", "exact", "refine"}:
        labels.append("uses_term_or_lemma")
    elif fam in {"cases", "cases'", "rcases", "induction", "induction'"}:
        labels.append("branches_context")
    elif fam in {"have", "suffices"}:
        labels.append("creates_intermediate_claim")
    if fam in {"contradiction", "exfalso"} or any(token in lowered for token in ("false.elim", "not.elim", "absurd")):
        labels.append("contradiction_closure")
        labels.append("closes_tableau_branch")
    if not labels:
        labels.append("unknown_effect")
    return sorted(set(labels))


def rows_from_packet(packet: dict[str, Any]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    theorem = str(packet.get("theorem") or packet.get("id") or "")
    source_file = str(packet.get("source_file") or "")
    for step in packet.get("steps") or []:
        if not isinstance(step, dict):
            continue
        tactic = str(step.get("tactic") or "").strip()
        before = normalize_goal_count(step.get("goals_before"))
        after = normalize_goal_count(step.get("goals_after"))
        hyp_before = normalize_goal_count(step.get("hypotheses_before"))
        hyp_after = normalize_goal_count(step.get("hypotheses_after"))
        payload = {
            "schema": SCHEMA,
            "id": stable_hash(theorem, source_file, step.get("index"), tactic, step.get("range")),
            "source": packet.get("source"),
            "theorem": theorem,
            "source_file": source_file,
            "step_index": step.get("index"),
            "tactic": tactic,
            "tactic_family": family(tactic),
            "goal_count_before": before,
            "goal_count_after": after,
            "hypothesis_count_before": hyp_before,
            "hypothesis_count_after": hyp_after,
            "effect_labels": effect_labels(tactic, before, after, hyp_before, hyp_after),
            "references": step.get("references") if isinstance(step.get("references"), list) else [],
            "range": step.get("range"),
            "authority": {
                "heuristic_training_label": True,
                "not_a_proof": True,
                "lean_remains_proof_authority": True,
            },
        }
        out.append(payload)
    return out


# [lossless-compact] write_jsonl folded into igf.common.json_io.write_jsonl
from igf.common.json_io import write_jsonl


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paperproof-trace", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    rows: list[dict[str, Any]] = []
    for packet in iter_jsonl(args.paperproof_trace):
        rows.extend(rows_from_packet(packet))
    count = write_jsonl(args.out, rows)
    print(json.dumps({"schema": SCHEMA + ".summary", "rows": count, "out": str(args.out)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
