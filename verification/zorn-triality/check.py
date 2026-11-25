#!/usr/bin/env python3
"""Fresh native real-Zorn triality, Clifford faithfulness, and derivation checks.

Uses the maintained focused verifier without changing its original defaults.
The existing eight-dimensional noninjectivity owner is checked alongside the
new doubled sixteen-dimensional representation, keeping their scopes distinct.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

TARGETS = (
    "InfoGeometry.Canonical.ZornInfinitesimalTriality",
    "InfoGeometry.Canonical.ZornTrialityMatrixDerivations",
    "InfoGeometry.Canonical.ZornCliffordFaithful",
    "InfoGeometry.Lie.SplitOctonionCliffordNoninjective",
)
REUSED = (
    "InfoGeometry.Canonical.ZornClifford.diracGamma_sq",
    "InfoGeometry.Canonical.ZornClifford.zornCliffordRepresentation",
    "InfoGeometry.Canonical.ZornClifford.zornCliffordRepresentation_ι",
    "InfoGeometry.Canonical.ZornClifford.zornNorm",
    "InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.leftRegularRepresentation",
    "InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.leftRegularRepresentation_injective",
    "InfoGeometry.Algebra.ZornPinorReconstruction.orientation_sourceProduct",
    "InfoGeometry.Algebra.ZornPinorReconstruction.orientation_norm",
    "InfoGeometry.Algebra.ZornPinorReconstruction.gamma_basis_product",
    "InfoGeometry.Algebra.ZornVectorMatrix.matrixDerivation",
    "InfoGeometry.Algebra.ZornVectorMatrix.matrixAction_leibniz_iff",
    "InfoGeometry.Algebra.ZornVectorMatrix.matrixAction_bracket",
    "InfoGeometry.Lie.CanonicalZornDerivation.vectorToCanonicalEnd_isDerivation",
    "InfoGeometry.Lie.CanonicalZornWittRegularBridge.wittZornEquiv",
    "InfoGeometry.Lie.CanonicalZornWittRegularBridge.zornNormFun_wittZornEquiv",
    "InfoGeometry.Lie.SplitOctonionWittVectorCovectorBridge.wittDualityEquiv",
    "InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.neutralToSplitIsometry",
    "InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv.splitTowerEquivMatrix",
)
REUSED_OWNERS = (
    "InfoGeometry.Canonical.ZornCliffordRepresentation",
    "InfoGeometry.Lie.CanonicalZornRegularOperators",
    "InfoGeometry.Algebra.ZornPinorReconstruction",
    "InfoGeometry.Algebra.Zorn.MatrixDerivation",
    "InfoGeometry.Lie.CanonicalZornDerivation",
    "InfoGeometry.Lie.CanonicalZornWittRegularBridge",
    "InfoGeometry.Lie.SplitOctonionWittVectorCovectorBridge",
    "InfoGeometry.Clifford.ClNNNeutralChevalleyBridge",
    "InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv",
)

if __name__ == "__main__":
    sys.dont_write_bytecode = True
    verifier_path = Path(__file__).resolve().parents[1] / "real-dirac-spin-nambu/check.py"
    spec = importlib.util.spec_from_file_location("focused_triality_verifier", verifier_path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"Cannot load shared verifier: {verifier_path}")
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    raise SystemExit(verifier.main(
        targets=TARGETS, owners=TARGETS, reused=REUSED, reused_owners=REUSED_OWNERS,
        probe_name="ZornTrialityAxioms.lean", entrypoint=Path(__file__),
    ))
