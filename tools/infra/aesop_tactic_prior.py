#!/usr/bin/env python3
"""Aesop-inspired static tactic prior classification.

Aesop separates proof search into normalisation, safe rules, and unsafe
backtracking rules.  This module borrows that control vocabulary for training
telemetry.  It is deliberately heuristic and dependency-free: it does not call
Lean or Aesop, and its output is only a search/training prior.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


SCHEMA = "info_geometry.aesop_tactic_prior.v1"

NORMALIZATION_TACTICS = {
    "simp",
    "simp_all",
    "simpa",
    "dsimp",
    "unfold",
    "change",
    "norm_num",
    "ring",
    "ring_nf",
}

SAFE_TACTICS = {
    "intro",
    "intros",
    "constructor",
    "rfl",
    "assumption",
    "trivial",
    "exact",
    "subst",
    "contradiction",
}

UNSAFE_TACTICS = {
    "apply",
    "refine",
    "cases",
    "rcases",
    "induction",
    "have",
    "suffices",
    "obtain",
    "use",
    "exists",
}

SEARCH_TACTICS = {
    "aesop",
    "grind",
    "exact?",
    "apply?",
    "solve_by_elim",
}


def tactic_head(tactic: Any) -> str:
    text = str(tactic or "").strip()
    if not text:
        return ""
    # Handle common tactic combinators without trying to parse Lean syntax.
    text = re.sub(r"^(first|try|all_goals|any_goals)\s*\|\s*", "", text)
    return text.split()[0].strip(";,")


def classify_tactic(tactic: Any) -> dict[str, Any]:
    head = tactic_head(tactic)
    if not head:
        phase = "unknown"
        backtracking = "unknown"
        probability = 0.1
    elif head in NORMALIZATION_TACTICS:
        phase = "normalization"
        backtracking = "eager"
        probability = 0.85
    elif head in SAFE_TACTICS:
        phase = "safe"
        backtracking = "none"
        probability = 0.9
    elif head in SEARCH_TACTICS:
        phase = "search"
        backtracking = "bounded_backtracking"
        probability = 0.55
    elif head in UNSAFE_TACTICS:
        phase = "unsafe"
        backtracking = "backtracking"
        probability = 0.45
    else:
        phase = "unsafe"
        backtracking = "backtracking"
        probability = 0.35

    return {
        "schema": SCHEMA,
        "tactic_head": head,
        "phase": phase,
        "backtracking": backtracking,
        "success_probability_prior": probability,
        "source": "aesop_inspired_static_heuristic",
        "authority": {
            "prior_is_not_proof": True,
            "lean_remains_proof_authority": True,
        },
    }


def annotate_jsonl(input_path: Path, output_path: Path, tactic_key: str) -> int:
    output_path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with input_path.open("r", encoding="utf-8") as src, output_path.open("w", encoding="utf-8") as out:
        for line in src:
            line = line.strip()
            if not line:
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                continue
            row["aesop_tactic_prior"] = classify_tactic(row.get(tactic_key))
            out.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
            count += 1
    return count


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tactic", nargs="?", help="Classify a single tactic string")
    parser.add_argument("--input-jsonl", type=Path)
    parser.add_argument("--output-jsonl", type=Path)
    parser.add_argument("--tactic-key", default="tactic")
    args = parser.parse_args()

    if args.input_jsonl:
        if not args.output_jsonl:
            parser.error("--output-jsonl is required with --input-jsonl")
        count = annotate_jsonl(args.input_jsonl, args.output_jsonl, args.tactic_key)
        print(json.dumps({"output": str(args.output_jsonl), "rows": count}, indent=2, sort_keys=True))
        return 0

    print(json.dumps(classify_tactic(args.tactic or ""), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
