#!/usr/bin/env python3
"""Vacuity Policy Gate — Layer C of the vacuity enforcement system.

Reads the JSON report produced by ``theorem_significance.py`` and enforces
the repository policy: any "error"-level violation causes a nonzero exit code.

Usage::

    python3 tools/check_vacuity_policy.py [reports/theorem-significance.json]

Exit codes:
    0   all violations are warnings only
    1   at least one error-level violation found

Typical CI integration::

    lake env lean lean/InfoGeometry/Lint/Vacuity.lean
    python3 tools/theorem_significance.py
    python3 tools/check_vacuity_policy.py reports/theorem-significance.json
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))

from pathing import repo_root

# Files matching these prefixes are subject to strict enforcement.
# Violations at "error" level in these files cause a hard CI failure.
STRICT_PREFIXES = [
    "lean/InfoGeometry/Canonical/",
    "lean/InfoGeometry/Quantum/",
]

# Bridge files get the tightest treatment: V1, V2, V4 are errors.
BRIDGE_HINTS = ["Bridge", "Core"]


def check_policy(report_path: Path, *, verbose: bool = True) -> int:
    """Return 0 if policy passes, 1 if any error-level violations exist."""
    with open(report_path) as f:
        entries = json.load(f)

    errors: list[dict] = []
    warnings: list[dict] = []

    for entry in entries:
        for v in entry.get("violations", []):
            if v["level"] == "error":
                errors.append({"name": entry["name"], "file": entry.get("file"), **v})
            elif v["level"] == "warning":
                warnings.append({"name": entry["name"], "file": entry.get("file"), **v})

    if verbose:
        print(f"Vacuity policy gate: {len(entries)} theorems checked")
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

    if errors:
        print(f"\nFAILED: {len(errors)} error-level violations.")
        return 1
    else:
        if verbose:
            print("\nPASSED: no error-level violations.")
        return 0


def main() -> None:
    root = repo_root()
    default_path = root / "reports" / "theorem-significance.json"

    if len(sys.argv) > 1:
        report_path = Path(sys.argv[1])
    else:
        report_path = default_path

    if not report_path.exists():
        print(f"ERROR: Report file not found: {report_path}", file=sys.stderr)
        print("Run `python3 tools/theorem_significance.py` first.", file=sys.stderr)
        sys.exit(2)

    rc = check_policy(report_path)
    sys.exit(rc)


if __name__ == "__main__":
    main()
