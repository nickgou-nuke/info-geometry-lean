#!/usr/bin/env python3
"""Compile the Weyl/Dikin relative-operator source closure and audit its owners.

Reuses the maintained selected-source verifier: exact dependency/toolchain pins,
copied and hashed repository sources, the shared build lock, and a native audit
of every selected-owner declaration against the foundational axiom allowlist.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.quality.check_peirce_bdg_geometry import main

TARGETS = [
    "InfoGeometry.Analysis.PositiveMatrixDikinCongruence",
    "InfoGeometry.Analysis.RelativeOperatorNeumann",
    "InfoGeometry.OperatorAlgebra.CoarseGrainingRelativeStability",
    "InfoGeometry.Canonical.RelativeDikinCoarseGraining",
    "InfoGeometry.Canonical.WeylDikinRGTests",
]


if __name__ == "__main__":
    main(targets=TARGETS, label="weyl-dikin-rg",
         audit_filename="WeylDikinRGAudit.lean", description=__doc__)
