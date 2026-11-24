#!/usr/bin/env python3
"""Check canonical null incidence and the real Clifford/Zorn representation."""
from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

TARGETS = (
    "InfoGeometry.Lie.CanonicalZornRegularTrace",
    "InfoGeometry.Lie.CanonicalZornNullIncidence",
    "InfoGeometry.Clifford.Cl44BornReciprocity",
    "InfoGeometry.Canonical.ZornCl44DiracTransport",
)
REUSED = (
    "InfoGeometry.Lie.CanonicalZornRegularNorm.leftRegular_mul_conj",
    "InfoGeometry.Lie.CanonicalZornRegularNorm.conj_mul_leftRegular",
    "InfoGeometry.Lie.CanonicalZornRegularExactDet.leftRegular_cartesian_matrix",
    "InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalPolar_nondegenerate",
    "InfoGeometry.Canonical.ZornClifford.zornCliffordRepresentation",
    "InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.detZ_cartesianZornLinearEquiv",
    "InfoGeometry.Clifford.Cl44Witt.witt_CAR",
    "InfoGeometry.Clifford.Cl44Witt.witt_annihilation_anticomm",
    "InfoGeometry.Clifford.Cl44Witt.witt_creation_anticomm",
    "InfoGeometry.Clifford.Cl44VolumeElement.volumeElement_sq",
    "InfoGeometry.Clifford.Cl44VolumeElement.volumeElement_anticommutes_e",
    "InfoGeometry.Clifford.KoszulFoundation.cliffordVolumeElement_sq_of_pairwise",
    "CliffordAlgebra.equivOfIsometry",
    "LinearMap.IsProj.trace",
    "LinearMap.finrank_range_add_finrank_ker",
)
EXTRA_SOURCES = (
    "verification/split-null-cl44/check.py",
    "verification/split-null-cl44/README.md",
    "verification/split-null-cl44/SOURCE_REVIEW.md",
    "docs/SPLIT_NULL_CL44_INTAKE_CONTRACT.md",
    "docs/intake/split-null-cl44-20261124/proposal.txt",
    ".github/workflows/split-null-cl44.yml",
)

if __name__ == "__main__":
    sys.dont_write_bytecode = True
    verifier_path = Path(__file__).resolve().parents[1] / "zorn-souriau/check.py"
    spec = importlib.util.spec_from_file_location("split_null_cl44_verifier", verifier_path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"Cannot load shared verifier: {verifier_path}")
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    raise SystemExit(verifier.main(
        targets=TARGETS, reused=REUSED, extra_sources=EXTRA_SOURCES,
        task_name="split-null-cl44",
    ))
