#!/usr/bin/env python3
"""Check the sandwich-localization source closure and audit its owned declarations.

The maintained checker supplies exact source snapshots, repository dependency
pins, serialized compilation, and exhaustive compiled-owner axiom auditing.
This focused check does not replace the root quality gates.
"""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.quality.check_perjes_klein import main  # noqa: E402

TARGETS = (
    "InfoGeometry.Algebra.SandwichLocalization",
    "InfoGeometry.Algebra.SandwichLocalizationActions",
    "InfoGeometry.Algebra.SandwichLocalizationStar",
    "InfoGeometry.Algebra.OneSidedLocalizationBoundary",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichCayley",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.EndogenousKernelBridge",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceDefectIdentities",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.KernelBridgeMatrixWitness",
)


if __name__ == "__main__":
    main(targets=TARGETS)
