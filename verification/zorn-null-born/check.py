#!/usr/bin/env python3
"""Fresh native Zorn null-kernel, Witt/Born, and oriented-volume validation.

Selects exact owners through the maintained focused verifier. The genuine
Cl(4,4) equivalence and the full Cl(4,3) noninjectivity boundary are also checked.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

TARGETS = (
    "InfoGeometry.Lie.CanonicalZornNullKernel",
    "InfoGeometry.Canonical.ZornWittBorn",
    "InfoGeometry.Canonical.ZornVolumeAction",
    "InfoGeometry.Canonical.ZornCliffordFaithful",
    "InfoGeometry.Lie.SplitOctonionCliffordNoninjective",
)
REUSED = (
    "InfoGeometry.Canonical.ZornClifford.zornNorm",
    "InfoGeometry.Canonical.ZornClifford.zornConj",
    "InfoGeometry.Canonical.ZornClifford.diracGamma_sq",
    "InfoGeometry.Canonical.ZornClifford.zornCliffordRepresentation",
    "InfoGeometry.Canonical.ZornClifford.zornCliffordRepresentation_ι",
    "InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.leftRegularRepresentation",
    "InfoGeometry.Lie.CanonicalZornRegularNorm.leftRegular_mul_conj",
    "InfoGeometry.Lie.CanonicalZornRegularNorm.conj_mul_leftRegular",
    "InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalPolar_nondegenerate",
    "InfoGeometry.Lie.SplitOctonionImaginaryAction.fullRightMul_ker_finrank",
    "InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv",
    "InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.detZ_cartesianZornLinearEquiv",
    "InfoGeometry.Clifford.Cl44Witt.witt_CAR",
    "InfoGeometry.Clifford.Cl44Witt.witt_annihilation_anticomm",
    "InfoGeometry.Clifford.Cl44Witt.witt_creation_anticomm",
    "InfoGeometry.Clifford.Cl44VolumeElement.volumeElement_sq",
    "InfoGeometry.Clifford.Cl44VolumeElement.volumeElement_anticommutes_e",
    "InfoGeometry.Clifford.Cl44VolumeElement.volumeElement_anticommutes_f",
    "InfoGeometry.Clifford.KoszulFoundation.cliffordVolumeElement_sq_of_pairwise",
    "LinearMap.IsProj.trace",
)
REUSED_OWNERS = (
    "InfoGeometry.Canonical.ZornCliffordRepresentation",
    "InfoGeometry.Canonical.ZornSpinor",
    "InfoGeometry.Lie.CanonicalZornRegularOperators",
    "InfoGeometry.Lie.CanonicalZornRegularNorm",
    "InfoGeometry.Lie.CanonicalZornWittRegularBridge",
    "InfoGeometry.Lie.SplitOctonionAnnihilatorDimension",
    "InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates",
    "InfoGeometry.Clifford.Cl44Witt",
    "InfoGeometry.Clifford.Cl44VolumeElement",
    "InfoGeometry.Clifford.KoszulFoundation",
)

if __name__ == "__main__":
    sys.dont_write_bytecode = True
    verifier_path = Path(__file__).resolve().parents[1] / "real-dirac-spin-nambu/check.py"
    spec = importlib.util.spec_from_file_location("focused_zorn_null_born_verifier", verifier_path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"Cannot load shared verifier: {verifier_path}")
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    raise SystemExit(verifier.main(
        targets=TARGETS, owners=TARGETS, reused=REUSED, reused_owners=REUSED_OWNERS,
        probe_name="ZornNullBornAxioms.lean", entrypoint=Path(__file__),
    ))
