#!/usr/bin/env python3
"""Reject missing, duplicate, or non-foundational records in the focused axiom log."""

from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
AUDITS = {
    "lean/InfoGeometry/Arithmetic/ZetaDihedralWeilKreinAudit.lean": 52,
    "lean/InfoGeometry/Categorical/CompatibleColimitAudit.lean": 24,
    "lean/InfoGeometry/Thermo/CompatibleMetriplecticColimitAudit.lean": 11,
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("logs", type=Path, nargs="+", help="Fresh compiler output from all three audits")
    args = parser.parse_args()
    expected: list[str] = []
    for audit, count in AUDITS.items():
        names = re.findall(r"^#print axioms (\S+)\s*$", (ROOT / audit).read_text(), re.MULTILINE)
        if len(names) != count or len(set(names)) != count:
            raise SystemExit(f"{audit}: expected exactly {count} distinct declarations")
        expected.extend(names)
    if len(set(expected)) != sum(AUDITS.values()):
        raise SystemExit("Declaration inventories must be disjoint")

    records: dict[str, list[list[str]]] = defaultdict(list)
    pattern = re.compile(
        r"'([^'\n]+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|"
        r"does not depend on any axioms)"
    )
    output = "\n".join(log.read_text() for log in args.logs)
    for name, raw_axioms in pattern.findall(output):
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
        "audits": AUDITS,
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
