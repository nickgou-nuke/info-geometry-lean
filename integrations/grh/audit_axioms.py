#!/usr/bin/env python3
"""Validate the exact GRH audit scope and reject any extra proof axiom.

This parser consumes output from a fresh, successful invocation of
`lake env lean InfoGeometryGRH/AxiomAudit.lean`. The integration runner owns
the shared build lock, dependency build, source fingerprint, and actual Lean
exit code. A printed `#print axioms` report alone is never accepted.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import sys
from typing import Any


NATIVE_OWNERS = (
    "InfoGeometry.Krein.Clifford",
    "InfoGeometry.Analysis.CenteredLogInterpolation",
    "InfoGeometry.Arithmetic.FiniteSmoothedMangoldt",
    "InfoGeometry.Arithmetic.SmoothedMangoldtReal",
    "InfoGeometry.Arithmetic.SmoothedMangoldtInterpolation",
    "InfoGeometry.Arithmetic.SmoothedMangoldtGrowth",
    "InfoGeometry.Arithmetic.SmoothedMangoldtMellin",
    "InfoGeometry.Arithmetic.RiemannHypothesisHalfPlaneReduction",
    "InfoGeometry.Arithmetic.WeightedMangoldtSmoothing",
    "InfoGeometry.Arithmetic.RealDoubledDirichletReadout",
    "InfoGeometry.Arithmetic.RealDoubledCenteredXiReadout",
)
OWNERS = NATIVE_OWNERS + (
    "InfoGeometryGRH.VerifiedGRH",
    "InfoGeometryGRH.PrimeRemainderBridge",
    "InfoGeometryGRH.RealDoubledGRH",
)
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
ALLOWED_KINDS = frozenset(
    {"theorem", "definition", "opaque", "inductive", "constructor", "recursor", "quotient"}
)


class AuditFailure(ValueError):
    """The supplied Lean evidence is failing, incomplete, or out of scope."""


def _string_list(value: Any, field: str) -> list[str]:
    if not isinstance(value, list) or any(not isinstance(x, str) for x in value):
        raise AuditFailure(f"Malformed {field}")
    if len(value) != len(set(value)):
        raise AuditFailure(f"Duplicate {field}")
    return value


def validate_output(output: str, *, lean_exit_code: int,
                    scope: str = "integration") -> dict[str, Any]:
    """Check a completed Lean run, its exact owners, and every declaration."""
    if lean_exit_code != 0:
        raise AuditFailure(f"Lean exited with code {lean_exit_code}")
    if scope not in {"native", "integration"}:
        raise AuditFailure(f"Unknown audit scope: {scope}")
    expected_owners = NATIVE_OWNERS if scope == "native" else OWNERS
    if "GRH_AXIOM_AUDIT_FAILURE:" in output:
        raise AuditFailure("Lean emitted an explicit axiom audit failure")
    records: list[dict[str, Any]] = []
    for line in output.splitlines():
        stripped = line.strip()
        if not stripped.startswith("{"):
            continue
        try:
            record = json.loads(stripped)
        except json.JSONDecodeError as exc:
            raise AuditFailure("Malformed audit JSON") from exc
        if not isinstance(record, dict):
            raise AuditFailure("Audit record is not an object")
        records.append(record)
    summaries = [r for r in records if r.get("record") == "grh_axiom_audit_summary"]
    if len(summaries) != 1 or not records or records[-1] is not summaries[0]:
        raise AuditFailure("Expected exactly one final GRH audit summary")
    summary = summaries[0]
    if summary.get("status") != "PASS":
        raise AuditFailure("Audit did not report PASS")
    if summary.get("scope") != scope:
        raise AuditFailure("Audit environment scope mismatch")
    if _string_list(summary.get("modules"), "owner scope") != list(expected_owners):
        raise AuditFailure("Audit owner scope differs from the integration contract")
    whitelist = _string_list(summary.get("axiom_whitelist"), "axiom whitelist")
    if set(whitelist) != ALLOWED_AXIOMS:
        raise AuditFailure("Audit axiom whitelist differs from the permitted foundations")
    declarations = [r for r in records if r.get("record") == "grh_axiom_audit_declaration"]
    if len(records) != len(declarations) + 1:
        raise AuditFailure("Unknown audit record")
    if type(summary.get("declarations")) is not int or summary["declarations"] != len(declarations):
        raise AuditFailure("Audited declaration count mismatch")
    seen_names: set[str] = set()
    counts: Counter[str] = Counter()
    theorem_count = 0
    used_axioms: set[str] = set()
    for record in declarations:
        name = record.get("name")
        module = record.get("module")
        if not isinstance(name, str) or not name or name in seen_names:
            raise AuditFailure("Missing or duplicate audited declaration name")
        if module not in expected_owners:
            raise AuditFailure(f"Unexpected owner for {name}: {module!r}")
        if record.get("kind") not in ALLOWED_KINDS:
            raise AuditFailure(f"Prohibited declaration kind for {name}")
        if record.get("unsafe") is not False or record.get("partial") is not False:
            raise AuditFailure(f"Unsafe, partial, or incomplete declaration record: {name}")
        axioms = _string_list(record.get("axioms"), f"axioms of {name}")
        rejected = set(axioms) - ALLOWED_AXIOMS
        if rejected:
            raise AuditFailure(f"Disallowed axioms for {name}: {', '.join(sorted(rejected))}")
        seen_names.add(name)
        counts[module] += 1
        theorem_count += record["kind"] == "theorem"
        used_axioms.update(axioms)
    if set(counts) != set(expected_owners):
        missing = sorted(set(expected_owners) - set(counts))
        raise AuditFailure(f"Empty or unaudited owners: {', '.join(missing)}")
    if type(summary.get("theorems")) is not int or summary["theorems"] != theorem_count:
        raise AuditFailure("Audited theorem count mismatch")
    if theorem_count == 0:
        raise AuditFailure("No theorem declarations were audited")
    return {
        "status": "PASS",
        "scope": "selected owner declarations and their transitive axiom dependencies",
        "environment_scope": scope,
        "lean_exit_code": lean_exit_code,
        "declarations": len(declarations),
        "theorems": theorem_count,
        "owner_counts": dict(sorted(counts.items())),
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "used_axioms": sorted(used_axioms),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path, help="Captured output from the fresh Lean audit")
    parser.add_argument("--lean-exit-code", required=True, type=int,
                        help="Actual exit code of the audited Lean invocation")
    parser.add_argument("--scope", choices=("native", "integration"), default="integration")
    parser.add_argument("--report", type=Path, help="Optional JSON validation report")
    args = parser.parse_args()
    try:
        result = validate_output(args.log.read_text(encoding="utf-8"),
                                 lean_exit_code=args.lean_exit_code, scope=args.scope)
    except (OSError, UnicodeError, AuditFailure) as exc:
        result = {"status": "FAIL", "reason": str(exc)}
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
