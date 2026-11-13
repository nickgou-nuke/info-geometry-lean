#!/usr/bin/env python3
"""Check the integer tripotent grading and its algebraic source closure."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.quality.check_perjes_klein import main

TARGETS = [
    "InfoGeometry.Core.TripotentIntegerGrading",
    "InfoGeometry.Core.TripotentSpectralSubmodule",
    "InfoGeometry.Core.TripotentCornerGeneration",
    "InfoGeometry.Core.TripotentExtremeKernels",
    "InfoGeometry.Core.TripotentJordanPair",
    "InfoGeometry.Core.TripotentStarGrading",
    "InfoGeometry.Core.TripotentGradeTransport",
    "InfoGeometry.OperatorAlgebra.TripotentExponentialFlow",
    "InfoGeometry.Canonical.TripotentIntegerStructureExample",
    "InfoGeometry.Core.TripotentIntegerStructureAudit",
]

if __name__ == "__main__":
    main(targets=TARGETS)
