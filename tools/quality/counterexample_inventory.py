#!/usr/bin/env python3
"""Inventory counterexample/obstruction declarations in Lean owners.

This is deliberately a navigation tool, not a proof checker.  It reports
declarations whose names advertise a negative witness or obstruction so that
each can be paired with a canonical positive theorem in its owner file.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


PATTERN = re.compile(
    r"^\s*(theorem|lemma)\s+([A-Za-z0-9_']*(?:counterexample|obstruction|"
    r"does_not|need_not|not_|not[A-Z]|nonmultip|not_exact|not_injective))"
)


def category(name: str) -> str:
    lowered = name.lower()
    if "counterexample" in lowered:
        return "countermodel"
    if "obstruction" in lowered or "nonmultip" in lowered:
        return "obstruction"
    if "injective" in lowered or "separate" in lowered:
        return "identifiability"
    return "negative-boundary"


def inventory(root: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for path in sorted((root / "lean" / "InfoGeometry").rglob("*.lean")):
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            match = PATTERN.match(line)
            if match:
                rows.append(
                    {
                        "file": str(path.relative_to(root)),
                        "line": line_number,
                        "kind": match.group(1),
                        "name": match.group(2),
                        "category": category(match.group(2)),
                    }
                )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    rows = inventory(args.root.resolve())
    if args.json:
        print(json.dumps(rows, indent=2, sort_keys=True))
        return
    print(f"counterexample-style declarations: {len(rows)}")
    by_category: dict[str, int] = {}
    for row in rows:
        key = str(row["category"])
        by_category[key] = by_category.get(key, 0) + 1
    for key in sorted(by_category):
        print(f"{key}: {by_category[key]}")
    for row in rows:
        print(f"{row['file']}:{row['line']}: {row['kind']} {row['name']} [{row['category']}]")


if __name__ == "__main__":
    try:
        main()
    except BrokenPipeError:
        pass
