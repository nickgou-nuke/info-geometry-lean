#!/usr/bin/env python3
"""Check the real Lie–Jordan Hodge source closure with the existing pinned checker.

This is not a root-package build. No dependency revision is changed.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_peirce_weyl as checker

checker.TARGETS = [
    "InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge",
    "InfoGeometry.OperatorAlgebra.LieJordanHodgeCoercivity",
    "InfoGeometry.OperatorAlgebra.LieJordanHodgeReal",
    "InfoGeometry.OperatorAlgebra.LieJordanChiralState",
    "InfoGeometry.Canonical.LieJordanHodgeColimit",
    "InfoGeometry.Canonical.LieJordanHodgeSynthesis",
]

if __name__ == "__main__":
    checker.main()
