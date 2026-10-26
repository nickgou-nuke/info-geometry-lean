#!/usr/bin/env python3
"""Pinned selected-source build and owned-declaration audit for finite absorption."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_peirce_reflection as checker
checker.TARGETS = [
    "InfoGeometry.Algebra.RankedMatrixPowers",
    "InfoGeometry.MassSpectrometry.FiniteFragmentAbsorption",
    "InfoGeometry.MassSpectrometry.FragmentationGreenResponse",
]
if __name__ == "__main__":
    checker.main()
