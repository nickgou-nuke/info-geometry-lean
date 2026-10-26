#!/usr/bin/env python3
"""Reuse the strict pinned source-closure checker for the quadratic bridge."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.quality import check_peirce_reflection as checker

checker.TARGETS = [
    'InfoGeometry.Canonical.QuadraticHamiltonianCoordinates',
    'InfoGeometry.Canonical.QuadraticHamiltonianCCR',
    'InfoGeometry.Canonical.QuadraticHamiltonianPolynomial',
]

if __name__ == '__main__':
    checker.main()
