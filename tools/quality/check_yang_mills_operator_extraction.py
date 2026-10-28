#!/usr/bin/env python3
"""Compile and audit the noncommutative curvature and Dirichlet source closure.

Every repository dependency is rebuilt from copied, hashed source. The native
audit checks all declarations owned by the selected modules, including private
and generated helpers. The shared verifier enforces the dependency pins,
compiler preflight, exclusive build lock, and foundational axiom allowlist.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.quality.check_peirce_bdg_geometry import main

TARGETS = [
    "InfoGeometry.OperatorAlgebra.DerivationCurvatureVariation",
    "InfoGeometry.Analysis.MatrixTraceQuadratic",
    "InfoGeometry.Geometry.MatrixCurvatureEnergy",
    "InfoGeometry.Geometry.MatrixCurvatureHessian",
    "InfoGeometry.Geometry.MatrixCurvatureNonconvexity",
    "InfoGeometry.Geometry.DerivationMatrixCurvature",
    "InfoGeometry.OperatorAlgebra.PeirceCurvatureDefect",
    "InfoGeometry.Geometry.PeirceCurvatureHessian",
    "InfoGeometry.Analysis.OperatorDirichletLaplacian",
    "InfoGeometry.Analysis.OperatorDirichletSpectralGap",
    "InfoGeometry.Analysis.OperatorDirichletScaling",
    "InfoGeometry.OperatorAlgebra.TracialGNSDirichlet",
    "InfoGeometry.OperatorAlgebra.TracialGNSGauge",
    "InfoGeometry.OperatorAlgebra.TracialGNSMatrixTests",
    "InfoGeometry.Canonical.MatrixEntropyUnitaryOrbit",
]


if __name__ == "__main__":
    main(targets=TARGETS, label="yang-mills-operator-extraction",
         audit_filename="YangMillsOperatorExtractionAudit.lean", description=__doc__)
