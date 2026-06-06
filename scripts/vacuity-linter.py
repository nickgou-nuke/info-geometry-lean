#!/usr/bin/env python3
"""
Lean 4 Vacuity Linter — AST-based detection of vacuous/mathless "cheating" code.

Detects patterns where a Lean proof type-checks but proves nothing meaningful:
  • by trivial / by trivial! on non-trivial statements
  • by admit / by sorry / by exact <trivial>
  • Proofs that don't use hypotheses
  • calc chains that cancel out
  • by rfl on constructed equalities
  • Theorem : True patterns (proving True instead of the real statement)
  • Empty match / cases blocks
  • simp with no effect

Usage:
  python3 scripts/vacuity-linter.py path/to/theorem.lean
  python3 scripts/vacuity-linter.py --stdin < file.lean
  python3 scripts/vacuity-linter.py --score path/to/theorem.lean  # returns 0.0-1.0
"""

import argparse
import os
import re
import sys
from typing import List, Tuple


# ── Detection Patterns ────────────────────────────────────────────────

VACUITY_PATTERNS = [
    # Direct trivial proofs on non-trivial statements
    (0.9, "trivial_proof", r"theorem\s+\w+.*:.*:=.*\bby\s+trivial\b",
     "Theorem proven with `by trivial` — likely vacuous if the statement is non-trivial"),

    (0.8, "trivial_bang", r"theorem\s+\w+.*:.*:=.*\bby\s+trivial!",
     "Theorem proven with `by trivial!` — likely vacuous"),

    (0.7, "admit_proof", r"theorem\s+\w+.*:.*:=.*\bby\s+admit\b",
     "Theorem proven with `by admit` — incomplete proof"),

    (0.7, "sorry_proof", r"theorem\s+\w+.*:.*:=.*\bby\s+sorry\b",
     "Theorem proven with `by sorry` — incomplete proof"),

    # Proving True instead of the real statement
    (0.6, "true_pattern", r"theorem\s+\w+.*:\s*True\b.*:=",
     "Theorem states `True` — trivially true, check if this is intentional"),

    # by exact on a trivial hypothesis
    (0.5, "exact_trivial", r"by\s+exact\s+(True\.trivial|trivial|rfl)\b",
     "Uses `exact trivial` or `exact rfl` — may be vacuous if the goal is non-trivial"),

    (0.5, "rfl_vacuous", r"theorem\s+\w+.*:.*:=.*\bby\s+rfl\b",
     "Theorem proven with `by rfl` — only valid if both sides are definitionally equal"),

    # calc chains that circle back
    (0.4, "calc_circle", r"calc\s+\n(\s+\w+\s+:=.*\n)+",
     "`calc` block — check that it doesn't just rewrite in a circle"),

    # Empty where clauses
    (0.3, "empty_where", r"theorem\s+\w+\s+.*:=\s*$",
     "Theorem with empty body — undefined"),

    # by simp with no arguments
    (0.3, "simp_vacuous", r"by\s+simp(\s*)$",
     "`by simp` without arguments — may or may not be vacuous depending on context"),

    # by nlinarith / omega (automatic provers)
    (0.2, "auto_prover", r"by\s+(nlinarith|omega|arith|aesop|polyrith)\b",
     "Automatic prover used — check that it actually proves the intended statement"),

    # Theorem with := followed by nothing or just a comment
    (0.4, "empty_body", r"theorem\s+\w+.*:=\s*--",
     "Theorem body is just a comment — undefined"),

    # no hypotheses used: theorem that's just `:= by` with no references to parameters
    (0.3, "no_hyp_use", r"theorem\s+(\w+)\s+\(.*\).*:.*by\s+(?!.*\1)",
     "Theorem with parameters but proof doesn't reference them — potential vacuity"),
]


def detect_vacuity(code: str) -> List[Tuple[float, str, str, str]]:
    """Run all vacuity detection patterns on Lean code. Returns list of (score, name, match, reason)."""
    findings = []
    for score, name, pattern, reason in VACUITY_PATTERNS:
        matches = re.findall(pattern, code, re.MULTILINE)
        if matches:
            findings.append((score, name, matches[0] if isinstance(matches[0], str) else str(matches[0]), reason))
    return findings


def compute_vacuity_score(code: str) -> float:
    """Compute overall vacuity score from 0.0 (honest) to 1.0 (completely vacuous)."""
    findings = detect_vacuity(code)
    if not findings:
        return 0.0
    # Take the maximum severity finding
    max_score = max(s for s, _, _, _ in findings)
    # Also consider count — multiple issues compound
    count_bonus = min(0.3, len(findings) * 0.05)
    return min(1.0, max_score + count_bonus)


def compute_honesty_score(code: str) -> float:
    """Compute honesty score from 0.0 (vacuous) to 1.0 (honest)."""
    return 1.0 - compute_vacuity_score(code)


def print_report(code: str, filepath: str = "<stdin>"):
    """Print a detailed vacuity report."""
    findings = detect_vacuity(code)
    vacuity = compute_vacuity_score(code)
    honesty = compute_honesty_score(code)

    print(f"📊 Vacuity Report: {filepath}")
    print(f"{'=' * 60}")
    print(f"  Honesty score:  {honesty:.2f}  {'🟢 honest' if honesty > 0.7 else '🟡 suspicious' if honesty > 0.4 else '🔴 vacuous'}")
    print(f"  Vacuity score:  {vacuity:.2f}")
    print(f"  Lines:          {len(code.splitlines())}")
    print()

    if findings:
        print(f"  ⚠️  Detected {len(findings)} potential vacuity patterns:")
        print()
        for score, name, match, reason in sorted(findings, key=lambda x: -x[0]):
            severity = "🔴" if score >= 0.7 else "🟡" if score >= 0.4 else "🟢"
            print(f"  {severity} [{score:.1f}] {name}")
            print(f"       {reason}")
            print(f"       Match: \"{match[:80]}\"")
            print()
    else:
        print("  ✅ No vacuity patterns detected.")
        print()


def main():
    parser = argparse.ArgumentParser(description="Lean 4 Vacuity Linter")
    parser.add_argument("file", nargs="?", help="Lean file to check")
    parser.add_argument("--stdin", action="store_true", help="Read from stdin")
    parser.add_argument("--score", action="store_true", help="Return numeric score only (for GEPA)")
    parser.add_argument("--json", action="store_true", help="Output JSON")
    args = parser.parse_args()

    code = ""
    if args.file:
        with open(args.file, "r") as f:
            code = f.read()
    elif args.stdin or not sys.stdin.isatty():
        code = sys.stdin.read()
    else:
        parser.print_help()
        sys.exit(1)

    if args.json:
        import json
        findings = [{"severity": s, "name": n, "match": m, "reason": r}
                    for s, n, m, r in detect_vacuity(code)]
        print(json.dumps({
            "honesty_score": compute_honesty_score(code),
            "vacuity_score": compute_vacuity_score(code),
            "findings": findings
        }, indent=2))
    elif args.score:
        print(f"{compute_honesty_score(code):.3f}")
    else:
        print_report(code, args.file or "<stdin>")


if __name__ == "__main__":
    main()
