#!/usr/bin/env python3
"""Check exact Lie--Jordan/Peirce sources using the existing pinned-Mathlib checker.

This checks a source-import closure and its transitive axiom footprint, not
Atlas, GIFT, LeanArchitect, or the repository's complete Lake package.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_peirce_weyl as checker

checker.TARGETS = [
    "InfoGeometry.OperatorAlgebra.LieJordanDualTransport",
    "InfoGeometry.Algebra.PeirceLieJordanResolution",
    "InfoGeometry.Algebra.PeirceLieJordanEigen",
    "InfoGeometry.OperatorAlgebra.LieJordanTracePairing",
    "InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble",
    "InfoGeometry.Canonical.LieJordanPeirceColimit",
    "InfoGeometry.OperatorAlgebra.LieJordanPeirceExamples",
    "InfoGeometry.Canonical.LieJordanPeirceSynthesis",
    "InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus",
    "InfoGeometry.Algebra.PeirceQuadraticCycle",
    "InfoGeometry.OperatorAlgebra.LieJordanBoundaryMatrices",
    "InfoGeometry.Canonical.LieJordanBoundaryColimit",
    "InfoGeometry.Canonical.LieJordanBoundarySynthesis",
    "InfoGeometry.OperatorAlgebra.LieJordanOctet",
    "InfoGeometry.Algebra.PeirceSandwichDuality",
    "InfoGeometry.OperatorAlgebra.LieJordanOctetMatrices",
    "InfoGeometry.Canonical.LieJordanOctetColimit",
    "InfoGeometry.Canonical.LieJordanOctetSynthesis",
]

if __name__ == "__main__":
    checker.main()
