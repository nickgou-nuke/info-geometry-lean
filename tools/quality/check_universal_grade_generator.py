#!/usr/bin/env python3
"""Verify the exact defect/tripotent source closure at the repository pins.

Reuse the maintained native Lean, exhaustive axiom, and isolated Lake checker.
The repository's unrelated root package and external submodules are out of scope.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_lie_jordan_geometry as checker

checker.TARGETS = [
    'InfoGeometry.Core.IdempotencyDefect',
    'InfoGeometry.Core.PeirceDefect',
    'InfoGeometry.Core.PeirceDefectAdjoint',
    'InfoGeometry.Core.DefectIteration',
    'InfoGeometry.Core.TripotentDefect',
    'InfoGeometry.Core.TripotentAdjoint',
    'InfoGeometry.Core.TripotentEigenspaces',
    'InfoGeometry.Canonical.TripotentMatrixExample',
]

if __name__ == '__main__':
    checker.main()
