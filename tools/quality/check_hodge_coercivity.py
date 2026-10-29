#!/usr/bin/env python3
"""Check positive-Hodge exact sources and transitive axioms under existing pins."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_peirce_weyl as checker

checker.TARGETS = [
    "InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge",
    "InfoGeometry.OperatorAlgebra.LieJordanHodgePairing",
    "InfoGeometry.OperatorAlgebra.BoundedHomotopyCoercivity",
    "InfoGeometry.OperatorAlgebra.LieJordanHodgeHilbert",
]

if __name__ == "__main__":
    checker.main()
