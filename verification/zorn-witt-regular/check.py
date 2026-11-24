#!/usr/bin/env python3
"""Fresh focused compilation and axiom audit of native Zorn regular operators.

Usage: python3 check.py --repo /absolute/repo --output /new/report/path
The existing verifier retains its original defaults. This entrypoint selects
the three new owners and the existing Clifford noninjectivity owner, so the
representation boundary is checked alongside the new operator statements.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

TARGETS = (
    "InfoGeometry.Lie.CanonicalZornRegularNorm",
    "InfoGeometry.Lie.CanonicalZornWittRegularBridge",
    "InfoGeometry.Lie.CanonicalZornRegularExactDet",
    "InfoGeometry.Lie.SplitOctonionCliffordNoninjective",
)
REUSED = (
    "InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.leftRegularRepresentation_apply_one",
    "InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.leftRegularRepresentation_injective",
    "InfoGeometry.Algebra.ZornVectorMatrix.associator_left_alternative",
    "InfoGeometry.Canonical.ZornClifford.mul_zornConj_mul",
    "InfoGeometry.Canonical.ZornClifford.zornConj_mul_mul",
    "InfoGeometry.Lie.SplitOctonionWittVectorCovectorBridge.wittDualityEquiv",
    "InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge.toCoord",
    "InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge.canonicalToCoord",
    "InfoGeometry.Lie.SplitOctonionImaginaryAction.imaginaryLeftMul_injective",
    "InfoGeometry.Lie.SplitOctonionImaginaryAction.splitOctonionLeftCliffordRepresentation_ι",
)
REUSED_OWNERS = (
    "InfoGeometry.Lie.CanonicalZornRegularOperators",
    "InfoGeometry.Algebra.ZornVectorMatrix",
    "InfoGeometry.Canonical.ZornCliffordRepresentation",
    "InfoGeometry.Lie.SplitOctonionWittVectorCovectorBridge",
    "InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge",
    "InfoGeometry.Lie.SplitOctonionCliffordAction",
)


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    verifier_path = Path(__file__).resolve().parents[1] / "real-dirac-spin-nambu/check.py"
    spec = importlib.util.spec_from_file_location("focused_zorn_verifier", verifier_path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"Cannot load shared verifier: {verifier_path}")
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    raise SystemExit(verifier.main(
        targets=TARGETS, owners=TARGETS, reused=REUSED, reused_owners=REUSED_OWNERS,
        probe_name="ZornWittRegularAxioms.lean", entrypoint=Path(__file__),
    ))
