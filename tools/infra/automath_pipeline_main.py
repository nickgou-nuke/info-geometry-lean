#!/usr/bin/env python3
"""
Automath Pipeline — Main entry point

Usage:
  python -m tools.infra.automath_pipeline --apex "InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.matrixToCuntz" --hypotheses /tmp/hypotheses.json
  python -m tools.infra.automath_pipeline --apex "..." --dry-run
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import List, Optional

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from tools.infra.automath_pipeline import (
    AutomathPipeline,
    Hypothesis,
    LeanGate,
    CASFilter,
    SocraticVerifier,
    OracleReferee,
    HiveSync,
)


def load_hypotheses(file: Path) -> List[Hypothesis]:
    """Load hypotheses from JSON file."""
    data = json.loads(file.read_text())
    if isinstance(data, dict):
        items = data.get("hypotheses", [data])
    else:
        items = data
    hypotheses = []
    for item in items:
        h = Hypothesis(
            id=item.get("id", item.get("concept_id", "hyp_0")),
            statement=item.get("statement", str(item.get("acceptance_theorems", []))),
            rationale=item.get("rationale", "Omega extraction"),
            mathematical_objects=item.get("mathematical_objects", item.get("formal_objects", [])),
            source_apex=item.get("source_apex", "Apex"),
            metadata=item.get("metadata", {}),
        )
        hypotheses.append(h)
    return hypotheses


def load_oracle_response(result_file: Path) -> list:
    """Parse Oracle response from browser-harness result file."""
    # The result file contains the Oracle's raw response
    # Parse it into structured hypotheses
    content = result_file.read_text()
    # Simple parsing: split by "HYPOTHESIS" markers
    hypotheses = []
    parts = content.split("HYPOTHESIS")
    for i, part in enumerate(parts[1:], 1):
        lines = part.strip().split('\n')
        if not lines:
            continue
        # Parse the hypothesis
        stmt = lines[0].strip()
        rationale = ""
        objects = []
        for line in lines[1:]:
            if line.startswith("RATIONALE"):
                rationale = line.split("—", 1)[-1].strip()
            elif line.startswith("RATIONALE:"):
                rationale = line.split(":", 1)[-1].strip()
            elif "falsification" in line.lower() or "falsification" in line.lower():
                # end of hypothesis
                pass
        # Extract mathematical objects from rationale
        import re
        obj_matches = re.findall(r'\b(spectrum|C\*|Cuntz|functional calculus|fibonacci|operator|root|projection|K-theory|K_0)\b', rationale, re.I)
        objects = list(set(obj_matches))
        hypotheses.append({
            "id": f"auto_hyp_{i}",
            "statement": stmt,
            "rationale": rationale,
            "mathematical_objects": objects,
            "source_apex": "InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.matrixToCuntz",
        })
    return hypotheses


def main():
    parser = argparse.ArgumentParser(description="Automath Pipeline — Hybrid Omega + Hive")
    parser.add_argument("--apex", required=True, help="Source apex declaration")
    parser.add_argument("--hypotheses", type=Path, help="JSON file with hypotheses")
    parser.add_argument("--oracle-result", type=Path, help="Oracle result file to parse")
    parser.add_argument("--dry-run", action="store_true", help="Run without committing to Hive")
    parser.add_argument("--max-repairs", type=int, default=3, help="Max Socratic repair attempts")
    parser.add_argument("--output", type=Path, help="Output Gold theorems JSON")
    args = parser.parse_args()

    # Load hypotheses
    hypotheses = []
    if args.hypotheses:
        hypotheses = load_hypotheses(args.hypotheses)
    elif args.oracle_result:
        raw = load_oracle_response(args.oracle_result)
        # Convert to Hypothesis objects
        from tools.infra.automath_pipeline import Hypothesis
        for item in raw:
            h = Hypothesis(
                id=item["id"],
                statement=item["statement"],
                rationale=item["rationale"],
                mathematical_objects=item["mathematical_objects"],
                source_apex=args.apex,
            )
            hypotheses.append(h)
    else:
        # Use the oracle response we just got
        result_file = Path("/tmp/chatgpt_browser_result.json")
        if result_file.exists():
            raw = load_oracle_response(result_file)
            for item in raw:
                h = Hypothesis(
                    id=item["id"],
                    statement=item["statement"],
                    rationale=item["rationale"],
                    mathematical_objects=item["mathematical_objects"],
                    source_apex=args.apex,
                )
                hypotheses.append(h)
        else:
            print("No hypotheses source provided")
            return 1

    if not hypotheses:
        print("No hypotheses to process")
        return 1

    print(f"Processing {len(hypotheses)} hypotheses from apex: {args.apex}")

    # Run pipeline
    pipeline = AutomathPipeline(apex=args.apex, max_repairs=args.max_repairs)
    gold = pipeline.run(hypotheses)

    # Output results
    if args.output:
        output = [{
            "id": h.id,
            "statement": h.statement,
            "apex": h.source_apex,
            "cas_passed": h.cas_passed,
            "lean_file": str(h.lean_file) if h.lean_file else None,
            "oracle_verdict": h.oracle_verdict,
            "committed": h.committed,
        } for h in gold]
        args.output.write_text(json.dumps(output, indent=2))
        print(f"Output written to {args.output}")

    if not args.dry_run and gold:
        # Commit to Hive
        hive = HiveSync()
        for h in gold:
            hive.commit_gold(h)

    return 0 if gold else 1


if __name__ == "__main__":
    sys.exit(main())