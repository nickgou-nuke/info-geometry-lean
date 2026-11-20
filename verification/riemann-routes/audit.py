#!/usr/bin/env python3
"""Audit the explicit public heads and root pins of the native RH route owners.

The maintained source inventory and axiom parser are reused. This bounded
inventory is separate from compilation and independent semantic review.
"""

from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
from pathlib import Path
import re

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parents[1]
AUDIT = ROOT / "lean/InfoGeometry/Arithmetic/RiemannRoutesAudit.lean"
OWNERS = (
    "InfoGeometry.Analysis.MulLogInterpolation",
    "InfoGeometry.Analysis.SmoothedMellinKernel",
    "InfoGeometry.Arithmetic.FiniteSmoothedMangoldt",
    "InfoGeometry.Arithmetic.CenteredSmoothedMangoldt",
    "InfoGeometry.Arithmetic.FiniteSmoothedMangoldtMellin",
    "InfoGeometry.Arithmetic.ActualRiemannZetaMobiusLSeriesBridge",
    "InfoGeometry.Arithmetic.MertensMellinRiemannHypothesis",
    "InfoGeometry.Arithmetic.RiemannHypothesisHalfPlaneReduction",
    "InfoGeometry.OperatorAlgebra.RealSkewDomainResidual",
    "InfoGeometry.OperatorAlgebra.UnboundedHilbertResidual",
    "InfoGeometry.Analysis.RealMatrixDikinScaling",
    "InfoGeometry.Analysis.DikinWeylBoundedness",
    "InfoGeometry.Arithmetic.MertensDikinBounds",
    "InfoGeometry.Arithmetic.ScaledEulerUniformBound",
)


def load_checker():
    path = ROOT / "verification/real-matrix-split/audit.py"
    spec = importlib.util.spec_from_file_location("maintained_declaration_audit", path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"Cannot load maintained checker: {path}")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    return checker


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate the explicit audit")
    parser.add_argument("--log", type=Path, help="fresh Lean output from the audit module")
    args = parser.parse_args()
    checker = load_checker()
    checker.check_pins(PROJECT)
    heads = [head for owner in OWNERS for head in checker.owner_declarations(owner)]
    if any(count != 1 for count in Counter(heads).values()):
        raise SystemExit("Repeated declaration in the source inventory")
    if args.write:
        header = (
            "/-\nCopyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
            "Released under Apache 2.0 license as described in the file LICENSE.\n"
            "Authors: InfoGeometry Engine Contributors\n-/\n\n"
        )
        imports = "".join(f"import {owner}\n" for owner in OWNERS)
        doc = (
            "\n/-!\n# Native arithmetic and real-operator route audit\n\n"
            "Every explicit public declaration in the selected owners is listed.\n"
            "Private helpers and imported dependencies are audited transitively.\n"
            "This target is not an umbrella import. It does not certify the\n"
            "unproved arithmetic cancellation premise or unconditional RH.\n\n"
            "Regenerate with `python3 verification/riemann-routes/audit.py --write`.\n-/\n\n"
        )
        AUDIT.write_text(header + imports + doc + "".join(f"#print axioms {h}\n" for h in heads))
    source = checker.strip_comments(AUDIT.read_text(encoding="utf-8"))
    if checker.FORBIDDEN.search(source):
        raise SystemExit("Forbidden proof construct in the audit module")
    listed = re.findall(r"^#print axioms (\S+)\s*$", source, flags=re.MULTILINE)
    if Counter(listed) != Counter(heads):
        raise SystemExit("The audit must list every explicit public head exactly once")
    imports = re.findall(r"^import (\S+)\s*$", source, flags=re.MULTILINE)
    if imports != list(OWNERS):
        raise SystemExit("The audit import list differs from the selected owners")
    print(f"Source coverage: {len(heads)} public declarations in {len(OWNERS)} owners; root pins match")
    if args.log:
        checker.check_axioms(args.log.read_text(encoding="utf-8"), set(heads))


if __name__ == "__main__":
    main()
