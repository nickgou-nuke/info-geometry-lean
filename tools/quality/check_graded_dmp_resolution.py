#!/usr/bin/env python3
"""Reuse the existing pinned source-closure compiler and all-declaration audit."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_cartan_drazin_mp as checker

# The earlier retract compilation is checked in the same run, not merely cited.
checker.TARGETS = [
    'InfoGeometry.Algebra.RectangularRetract',
    'InfoGeometry.QuantumContext.RectangularDrazinLift',
    'InfoGeometry.QuantumContext.RectangularPeirceDrazin',
    'InfoGeometry.Canonical.GradedDMPResolution',
    'InfoGeometry.QuantumContext.GradedDMPTransport',
    'InfoGeometry.Canonical.GradedDMPMatrixWitness',
    'InfoGeometry.Canonical.GradedDMPDependencyOrder',
]

if __name__ == '__main__':
    checker.main()
