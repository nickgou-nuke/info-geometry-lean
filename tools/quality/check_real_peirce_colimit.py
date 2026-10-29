#!/usr/bin/env python3
"""Verify the exact real Peirce/tensor-colimit closure at repository pins.

All acceptance logic is the existing sequential source-closure verifier.
This entrypoint selects only the new theorem owners and their real tower
dependencies; it does not alter the root package or its dependency graph.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_lie_jordan_geometry as checker

checker.TARGETS = [
    'InfoGeometry.Core.PeirceDoubleCommutator',
    'InfoGeometry.Clifford.Cl11StarUniversal',
    'InfoGeometry.Clifford.Cl11ColimitDimension',
    'InfoGeometry.Canonical.PeirceDissipatorColimit',
    'InfoGeometry.Canonical.PeirceColimitExamples',
]

if __name__ == '__main__':
    checker.main()
