#!/usr/bin/env python3
"""Check the reduction's public inventory, root pins, and fresh Lean axiom log.

Reuse the maintained real-matrix-split inventory and axiom checker. This is a
bounded source audit; Lean compilation and independent semantic review remain
separate checks.
"""

from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
from pathlib import Path
import re

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parents[1]
MODULE = "InfoGeometry.Arithmetic.RiemannHypothesisHalfPlaneReduction"
AUDIT = ROOT / "lean/InfoGeometry/Arithmetic/RiemannHypothesisHalfPlaneReductionAudit.lean"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log", type=Path, help="fresh Lean output from the audit module")
    args = parser.parse_args()

    checker_path = ROOT / "verification/real-matrix-split/audit.py"
    spec = importlib.util.spec_from_file_location("maintained_declaration_audit", checker_path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"Cannot load maintained checker: {checker_path}")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    checker.check_pins(PROJECT)
    heads = checker.owner_declarations(MODULE)
    source = checker.strip_comments(AUDIT.read_text(encoding="utf-8"))
    if checker.FORBIDDEN.search(source):
        raise SystemExit("Forbidden proof construct in the audit module")
    listed = re.findall(r"^#print axioms (\S+)\s*$", source, flags=re.MULTILINE)
    if Counter(listed) != Counter(heads) or any(count != 1 for count in Counter(heads).values()):
        raise SystemExit("Audit commands must list every public owner declaration exactly once")
    print(f"Source coverage: {len(heads)} explicit public declarations; root pins match")
    if args.log:
        checker.check_axioms(args.log.read_text(encoding="utf-8"), set(heads))


if __name__ == "__main__":
    main()
