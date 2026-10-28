#!/usr/bin/env python3
"""Use the existing serial source-closure checker for Lie--Jordan/Peirce owners.

This is a scoped check against the unchanged Mathlib pin, not a root Lake build.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_peirce_weyl as checker

checker.TARGETS = [
    'InfoGeometry.OperatorAlgebra.LieJordanDuality',
    'InfoGeometry.OperatorAlgebra.PeirceLieJordanResolution',
    'InfoGeometry.OperatorAlgebra.LieJordanTraceDuality',
    'InfoGeometry.OperatorAlgebra.PeirceTracePairing',
    'InfoGeometry.OperatorAlgebra.OperatorDiracSchur',
    'InfoGeometry.OperatorAlgebra.LieJordanDiracPair',
    'InfoGeometry.OperatorAlgebra.LieJordanPeirceColimit',
    'InfoGeometry.OperatorAlgebra.LieJordanPeirceExamples',
    'InfoGeometry.OperatorAlgebra.LieJordanPeirce',
]

if __name__ == '__main__':
    checker.main()
