#!/usr/bin/env python3
"""Check the tripotent signed-bracket and operator-flow source closure."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.quality.check_perjes_klein import main

TARGETS = [
    "InfoGeometry.Core.TripotentAdjointRigidity",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentSuperbracket",
    "InfoGeometry.Canonical.TripotentSuperbracketExample",
    "InfoGeometry.OperatorAlgebra.TripotentExponentialFlow",
]

if __name__ == "__main__":
    main(targets=TARGETS)
