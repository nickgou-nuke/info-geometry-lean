#!/usr/bin/env python3
"""Compile and audit the exact operator logdet/Dikin geometry source closure.

All repository dependencies are rebuilt from copied, hashed sources. The native
audit checks every declaration owned by each selected module, including generated
helpers. The pinned Mathlib revision, compiler, process preflight, shared build
lock, and permitted foundational axioms are enforced by the common verifier.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.quality.check_peirce_bdg_geometry import main

TARGETS = [
    "InfoGeometry.Analysis.ComplexMatrixJacobi",
    "InfoGeometry.Analysis.ComplexMatrixLogDetCalculus",
    "InfoGeometry.Analysis.PositiveMatrixDikin",
    "InfoGeometry.Canonical.PolarFrameTraceDensity",
    "InfoGeometry.Canonical.OperatorLogDetDikinGeometry",
    "InfoGeometry.Canonical.BKMCommutatorDikin",
    "InfoGeometry.Canonical.PolarFrameBKMGeometry",
    "InfoGeometry.Canonical.OperatorLogDetDikinGeometryTests",
]


if __name__ == "__main__":
    main(targets=TARGETS, label="operator-logdet-dikin",
         audit_filename="OperatorLogDetDikinAudit.lean", description=__doc__)
