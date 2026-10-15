#!/usr/bin/env python3
"""Vacuity Policy Gate — Layer C of the vacuity enforcement system.

Reads the JSON report produced by ``theorem_significance.py`` and enforces
the repository policy: any "error"-level violation causes a nonzero exit code.
It can also validate that reported levels are consistent with the shared
policy configuration used by Layer B.

Usage::

    python3 tools/check_vacuity_policy.py [reports/theorem-significance.json]

Exit codes:
    0   all violations are warnings only
    1   at least one error-level violation found
    2   report file missing or invalid report shape
    3   consistency mismatch between report levels and policy config

Typical CI integration::

    lake env lean lean/InfoGeometry/Lint/Vacuity.lean
    python3 tools/theorem_significance.py
    python3 tools/check_vacuity_policy.py reports/theorem-significance.json
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.pathing import repo_root
from tools.vacuity_policy_config import (
    BRIDGE_HINTS_DEFAULT,
    STRICT_PATHS_DEFAULT,
    expected_violation_level,
)


def check_policy(
    report_path: Path,
    *,
    strict_paths: list[str],
    bridge_hints: list[str],
    verbose: bool = True,
    validate_consistency: bool = True,
) -> int:
    """Return policy gate status code.

    Exit codes:
      0: pass
      1: error-level violations found
      2: invalid, incomplete, or advisory-only report
      3: report levels inconsistent with shared policy config
    """
    try:
        with open(report_path, encoding="utf-8") as f:
            entries = json.load(f)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        print(f"ERROR: unreadable or invalid report: {exc}", file=sys.stderr)
        return 2

    if not isinstance(entries, list) or not entries:
        print("ERROR: report must be a nonempty JSON array of declarations.", file=sys.stderr)
        return 2

    # Validate the entire producer contract before making any policy decision.
    # Missing violations is missing evidence, never evidence of zero violations.
    for index, entry in enumerate(entries):
        if (not isinstance(entry, dict)
                or not isinstance(entry.get("name"), str) or not entry["name"].strip()
                or not isinstance(entry.get("file"), str) or not entry["file"].strip()
                or not isinstance(entry.get("violations"), list)):
            print(f"ERROR: incomplete declaration report at index {index}.", file=sys.stderr)
            return 2
        for flag in ("hard_verdict_allowed", "semantic_audit_performed", "coverage_complete"):
            if flag in entry and not isinstance(entry[flag], bool):
                print(f"ERROR: invalid {flag} at declaration index {index}.", file=sys.stderr)
                return 2
        if (entry.get("hard_verdict_allowed") is False
                or entry.get("semantic_audit_performed") is False
                or entry.get("coverage_complete") is False
                or entry.get("classification_basis") == "graph-topology"):
            print(f"ERROR: advisory_report_not_clearance at declaration index {index}.",
                  file=sys.stderr)
            return 2
        for violation in entry["violations"]:
            if (not isinstance(violation, dict)
                    or violation.get("level") not in ("error", "warning")
                    or not isinstance(violation.get("code"), str)
                    or not violation["code"].strip()):
                print(f"ERROR: invalid violation at declaration index {index}.", file=sys.stderr)
                return 2

    errors: list[dict] = []
    warnings: list[dict] = []
    mismatches: list[dict] = []

    for entry in entries:
        if not isinstance(entry, dict):
            continue
        name = entry.get("name")
        file_path = entry.get("file")
        for v in entry.get("violations", []):
            if not isinstance(v, dict):
                continue
            level = v.get("level")
            code = v.get("code")
            if level == "error":
                errors.append({"name": name, "file": file_path, **v})
            elif level == "warning":
                warnings.append({"name": name, "file": file_path, **v})

            if validate_consistency and isinstance(code, str):
                expected = expected_violation_level(code, file_path, strict_paths, bridge_hints)
                if expected is not None and level != expected:
                    mismatches.append(
                        {
                            "name": name,
                            "file": file_path,
                            "code": code,
                            "level": level,
                            "expected": expected,
                        }
                    )

    if verbose:
        print(f"Vacuity policy gate: {len(entries)} declarations checked")
        print(f"  Warnings: {len(warnings)}")
        print(f"  Errors:   {len(errors)}")
        if errors:
            print()
            print("ERROR-level violations:")
            # Group by file
            by_file: dict[str, list[dict]] = {}
            for e in errors:
                f = e.get("file") or "(unknown)"
                by_file.setdefault(f, []).append(e)
            for fpath in sorted(by_file):
                print(f"\n  {fpath}:")
                for e in by_file[fpath]:
                    print(f"    [{e['code']}] {e['name']}")

        if validate_consistency and mismatches:
            print()
            print("Policy consistency mismatches:")
            for m in mismatches:
                fpath = m.get("file") or "(unknown)"
                print(
                    f"  {fpath}: [{m['code']}] {m['name']} "
                    f"reported={m['level']} expected={m['expected']}"
                )

    if errors:
        if verbose:
            print(f"\nFAILED: {len(errors)} error-level violations.")
        return 1
    if validate_consistency and mismatches:
        if verbose:
            print(f"\nFAILED: {len(mismatches)} policy consistency mismatches.")
        return 3
    else:
        if verbose:
            print("\nPASSED: no error-level violations.")
        return 0


def main() -> None:
    root = repo_root()
    default_path = root / "reports" / "theorem-significance.json"

    parser = argparse.ArgumentParser(description="Vacuity policy gate")
    parser.add_argument("report", nargs="?", default=str(default_path), help="Path to theorem-significance JSON report")
    parser.add_argument("--strict-prefix", action="append", default=[], help="Strict policy file prefix (repeatable)")
    parser.add_argument("--bridge-hint", action="append", default=[], help="Bridge file stem hint (repeatable)")
    parser.add_argument("--skip-consistency-check", action="store_true", help="Skip validation of reported levels vs shared policy")
    args = parser.parse_args()

    report_path = Path(args.report)
    strict_paths = args.strict_prefix if args.strict_prefix else list(STRICT_PATHS_DEFAULT)
    bridge_hints = args.bridge_hint if args.bridge_hint else list(BRIDGE_HINTS_DEFAULT)

    if not report_path.exists():
        print(f"ERROR: Report file not found: {report_path}", file=sys.stderr)
        print("Run `python3 tools/theorem_significance.py` first.", file=sys.stderr)
        sys.exit(2)

    rc = check_policy(
        report_path,
        strict_paths=strict_paths,
        bridge_hints=bridge_hints,
        validate_consistency=not args.skip_consistency_check,
    )
    sys.exit(rc)


if __name__ == "__main__":
    main()
