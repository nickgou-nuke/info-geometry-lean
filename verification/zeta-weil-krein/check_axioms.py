#!/usr/bin/env python3
"""Reject missing, duplicate, or non-foundational records in the focused axiom log."""

from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / "lean/InfoGeometry/Arithmetic/ZetaDihedralWeilKreinAudit.lean"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path, help="Compiler output from the focused audit")
    args = parser.parse_args()
    expected = re.findall(r"^#print axioms (\S+)\s*$", AUDIT.read_text(), re.MULTILINE)
    if len(expected) != 46 or len(set(expected)) != 46:
        raise SystemExit("Audit inventory must contain exactly 46 distinct declarations")

    records: dict[str, list[list[str]]] = defaultdict(list)
    pattern = re.compile(
        r"'([^'\n]+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|"
        r"does not depend on any axioms)"
    )
    for name, raw_axioms in pattern.findall(args.log.read_text()):
        records[name].append([a.strip() for a in raw_axioms.split(",") if a.strip()])

    errors: list[str] = []
    if set(records) - set(expected):
        errors.append("Unexpected declaration records: " + ", ".join(sorted(set(records) - set(expected))))
    for name in expected:
        entries = records.get(name, [])
        if len(entries) != 1:
            errors.append(f"{name}: expected one record, found {len(entries)}")
            continue
        rejected = set(entries[0]) - ALLOWED_AXIOMS
        if rejected:
            errors.append(f"{name}: rejected axioms {sorted(rejected)}")

    print(json.dumps({
        "audit": str(AUDIT.relative_to(ROOT)),
        "expected_declarations": len(expected),
        "reported_declarations": len(records),
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "passed": not errors,
        "errors": errors,
        "records": dict(records),
    }, indent=2))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
