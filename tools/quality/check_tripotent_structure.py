#!/usr/bin/env python3
"""Check the tripotent structural owners and all owned declaration axioms."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.quality.check_perjes_klein import main

TARGETS = [
    "InfoGeometry.Core.TripotentIntegerGrading",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentIntegerSuperbracket",
    "InfoGeometry.Core.TripotentInvariantSubspaces",
    "InfoGeometry.Core.TripotentOddGeneration",
    "InfoGeometry.Core.TripotentInvolution",
    "InfoGeometry.OperatorAlgebra.TripotentCornerActions",
    "InfoGeometry.OperatorAlgebra.TripotentExtremalJordanPair",
    "InfoGeometry.OperatorAlgebra.TripotentGradeTransport",
    "InfoGeometry.Core.TripotentKreinBlocks",
    "InfoGeometry.Core.TripotentAdjointDefect",
]

if __name__ == "__main__":
    main(targets=TARGETS)
