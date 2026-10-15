#!/usr/bin/env python3
"""
AutoMath candidate pipeline — main entry point

Usage:
  python -m tools.infra.automath_pipeline_main --apex "InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.matrixToCuntz" --hypotheses /tmp/hypotheses.json
  python -m tools.infra.automath_pipeline_main --apex "..." --dry-run
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import List

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from tools.infra.automath_pipeline import (
    AutomathPipeline,
    Hypothesis,
)
from tools.infra.hive_epistemic_bridge import validate_candidate_archive_record


def load_hypotheses(file: Path, default_apex: str) -> List[Hypothesis]:
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
            source_apex=item.get("source_apex") or default_apex,
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
    parser = argparse.ArgumentParser(description="AutoMath Lean candidate pipeline")
    parser.add_argument("--apex", required=True, help="Source apex declaration")
    parser.add_argument("--hypotheses", type=Path, help="JSON file with hypotheses")
    parser.add_argument("--oracle-result", type=Path, help="Oracle result file to parse")
    parser.add_argument("--dry-run", action="store_true", help="List inputs without oracle, compiler, or Arango side effects")
    parser.add_argument("--max-repairs", type=int, default=3, help="Max Socratic repair attempts")
    parser.add_argument("--output", type=Path, help="Write candidate provenance summary JSON")
    args = parser.parse_args()

    # Load hypotheses
    hypotheses = []
    if args.hypotheses:
        hypotheses = load_hypotheses(args.hypotheses, args.apex)
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

    if args.dry_run:
        print(f"Dry run: {len(hypotheses)} hypotheses for apex {args.apex}")
        for hypothesis in hypotheses:
            print(f"  {hypothesis.id}: {hypothesis.statement[:100]}")
        return 0

    print(f"Processing {len(hypotheses)} hypotheses from apex: {args.apex}")

    # Run pipeline
    pipeline = AutomathPipeline(apex=args.apex, max_repairs=args.max_repairs)
    candidates = pipeline.run(hypotheses)

    # Output results
    if args.output:
        output = []
        for h in candidates:
            candidate_record = {
                "record_type": "automath_lean_candidate",
                "authority": "candidate_record_not_proof_authority",
                "status": h.metadata.get("archive_status", "lean_checked_pending_review"),
                "candidate_sha256": h.metadata.get("candidate_sha256", ""),
                "lean_file": str(h.lean_file) if h.lean_file else "",
                "source_path": h.metadata.get("source_path", ""),
                "source_snapshot_sha256": h.metadata.get("source_snapshot_sha256", ""),
                "source_snapshot_current_sha256": h.metadata.get("source_snapshot_current_sha256", ""),
                "source_context_changed": h.metadata.get("source_context_changed", False),
                "toolchain": h.metadata.get("toolchain", ""),
                "lakefile_sha256": h.metadata.get("lakefile_sha256", ""),
                "lake_manifest_sha256": h.metadata.get("lake_manifest_sha256", ""),
                "git_head": h.metadata.get("git_head", ""),
                "lean_check_returncode": h.metadata.get("lean_check_returncode"),
                "lean_output_sha256": h.metadata.get("lean_output_sha256", ""),
                "semantic_vacuity_returncode": h.metadata.get("semantic_vacuity_returncode"),
                "semantic_vacuity_output_sha256": h.metadata.get("semantic_vacuity_output_sha256", ""),
                "axiom_audit_status": h.metadata.get("axiom_audit_status", "not_requested"),
                "axiom_audit_declarations": h.metadata.get("axiom_audit_declarations", []),
                "axiom_audit_returncode": h.metadata.get("axiom_audit_returncode"),
                "axiom_audit_output_sha256": h.metadata.get("axiom_audit_output_sha256", ""),
                "audit_receipt": h.metadata.get("audit_receipt"),
            }
            checked = validate_candidate_archive_record(candidate_record)
            if not checked["ok"]:
                raise RuntimeError(
                    f"candidate receipt failed export validation for {h.id}: {checked['reasons']}"
                )
            output.append({
                "id": h.id,
                "statement": h.statement,
                "apex": h.source_apex,
                "cas_passed": h.cas_passed,
                "lean_file": str(h.lean_file) if h.lean_file else None,
                "oracle_verdict": h.oracle_verdict,
                "archived": h.archived,
                "candidate_sha256": h.metadata.get("candidate_sha256", ""),
                "source_snapshot_sha256": h.metadata.get("source_snapshot_sha256", ""),
                "source_snapshot_current_sha256": h.metadata.get("source_snapshot_current_sha256", ""),
                "source_context_changed": h.metadata.get("source_context_changed", False),
                "cas_status": h.metadata.get("cas_status", "not_supplied"),
                "lean_check_returncode": h.metadata.get("lean_check_returncode"),
                "lean_output_sha256": h.metadata.get("lean_output_sha256", ""),
                "semantic_vacuity_status": h.metadata.get("semantic_vacuity_status", "not_run"),
                "semantic_vacuity_returncode": h.metadata.get("semantic_vacuity_returncode"),
                "semantic_vacuity_output_sha256": h.metadata.get("semantic_vacuity_output_sha256", ""),
                "run_id": h.metadata.get("run_id", ""),
                "oracle_exchanges": h.metadata.get("oracle_exchanges", []),
                "audit_receipt": checked["receipt"],
                "authority": "candidate_only_requires_owner_review",
            })
        args.output.write_text(json.dumps(output, indent=2))
        print(f"Output written to {args.output}")

    # The pipeline archives exactly once after Lean checking. This entrypoint
    # must not perform a second write or classify candidates as Gold.
    return 0 if candidates else 1


if __name__ == "__main__":
    sys.exit(main())
