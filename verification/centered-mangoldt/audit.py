#!/usr/bin/env python3
"""Check the centered bridge and both integrated prerequisite inventories.

The maintained declaration checker supplies source screening, dependency-pin
validation, and fresh axiom-log validation. This bounded source inventory does
not replace Lean compilation or independent mathematical review.
"""

from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
from pathlib import Path
import re

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parents[1]
OWNERS = (
    "InfoGeometry.Arithmetic.FiniteSmoothedMangoldt",
    "InfoGeometry.Arithmetic.RiemannHypothesisHalfPlaneReduction",
    "InfoGeometry.Analysis.CenteredLogInterpolation",
    "InfoGeometry.Arithmetic.SmoothedMangoldtReal",
    "InfoGeometry.Arithmetic.SmoothedMangoldtInterpolation",
    "InfoGeometry.Arithmetic.SmoothedMangoldtGrowth",
    "InfoGeometry.Arithmetic.SmoothedMangoldtMellin",
)
AUDIT = ROOT / "lean/InfoGeometry/Arithmetic/CenteredMangoldtBridgeAudit.lean"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate the explicit audit module")
    parser.add_argument("--log", type=Path, help="fresh Lean output from the audit module")
    args = parser.parse_args()

    checker_path = ROOT / "verification/real-matrix-split/audit.py"
    spec = importlib.util.spec_from_file_location("maintained_declaration_audit", checker_path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"Cannot load maintained checker: {checker_path}")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    checker.check_pins(PROJECT)
    heads = [head for module in OWNERS for head in checker.owner_declarations(module)]

    if args.write:
        header = (
            "/-\nCopyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
            "Released under Apache 2.0 license as described in the file LICENSE.\n"
            "Authors: InfoGeometry Engine Contributors\n-/\n\n"
        )
        imports = "".join(f"import {module}\n" for module in OWNERS)
        explanation = (
            "\n/-!\n# Centered Mangoldt bridge declaration audit\n\n"
            "Audit every explicitly named public declaration in the five new owners\n"
            "and the two integrated prerequisite owners. Private helpers are covered\n"
            "transitively by the public heads' axiom dependencies; generated\n"
            "declarations are not independently inventoried.\n\n"
            "Regenerate with `python3 verification/centered-mangoldt/audit.py --write`.\n"
            "-/\n\n"
        )
        AUDIT.write_text(header + imports + explanation +
                         "".join(f"#print axioms {head}\n" for head in heads), encoding="utf-8")

    source = checker.strip_comments(AUDIT.read_text(encoding="utf-8"))
    if checker.FORBIDDEN.search(source):
        raise SystemExit("Forbidden proof construct in the audit module")
    listed = re.findall(r"^#print axioms (\S+)\s*$", source, flags=re.MULTILINE)
    if Counter(listed) != Counter(heads) or any(count != 1 for count in Counter(heads).values()):
        raise SystemExit("Audit commands must list every public owner declaration exactly once")
    print(f"Source coverage: {len(heads)} explicit public declarations in {len(OWNERS)} owners; "
          "root pins match")
    if args.log:
        checker.check_axioms(args.log.read_text(encoding="utf-8"), set(heads))


if __name__ == "__main__":
    main()
