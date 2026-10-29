#!/usr/bin/env python3
"""Source-closure check and exhaustive native axiom audit, with existing machinery."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_cartan_drazin_mp as checker

checker.TARGETS = [
    'InfoGeometry.Core.PeirceAdjointCycle',
    'InfoGeometry.Core.PeirceQuadraticFrame',
    'InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus',
    'InfoGeometry.OperatorAlgebra.LieJordanOctet',
    'InfoGeometry.Algebra.PeirceSandwichDuality',
    'InfoGeometry.Core.PeirceQuadraticIteration',
    'InfoGeometry.Core.PeirceIterationWitness',
    'InfoGeometry.Core.PeirceSourceOrder',
]

if __name__ == '__main__':
    checker.main()
