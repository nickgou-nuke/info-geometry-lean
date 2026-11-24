#!/usr/bin/env python3
"""Select the triality/cotangent owners for the shared native verifier.

The underlying transaction retains its original Zorn/Souriau defaults and
all lock, package-pin, fresh-elaboration, inventory, and axiom checks.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

TARGETS = (
    "InfoGeometry.Algebraic.CoadjointActionGroupoid",
    "InfoGeometry.Algebraic.CotangentFormTransport",
    "InfoGeometry.Algebraic.CotangentFixedPointObstruction",
    "InfoGeometry.Algebraic.OrderThreeFixedForm",
    "InfoGeometry.Lie.TrialityCartanMatrixCore",
    "InfoGeometry.Lie.CartanTrialityFirstCoordinate",
    "InfoGeometry.Lie.CartanTrialityCotangentFixedForm",
)
REUSED = (
    "InfoGeometry.Canonical.SouriauContragredientPairing.contragredientLinearEquiv",
    "InfoGeometry.Canonical.SouriauContragredientPairing.contragredientGeneralLinearRepresentation",
    "InfoGeometry.Twistor.RealDualTwistor.frameAction",
    "InfoGeometry.Twistor.RealDualTwistor.eq_zero_of_dual_vanishes",
    "InfoGeometry.Twistor.RealDualTwistor.symplecticForm_nondegenerate",
    "InfoGeometry.Algebraic.CotangentBilinearGraph.cotangentForm",
    "InfoGeometry.Algebraic.CotangentBilinearGraph.cotangentForm_isAlt",
    "CategoryTheory.ActionCategory.objEquiv",
    "CategoryTheory.Functor.Elements.homMk",
    "LinearMap.fixedSubmodule_eq_ker",
    "LinearMap.BilinForm.restrict",
)
EXTRA_SOURCES = (
    "verification/triality-cotangent/check.py",
    "verification/triality-cotangent/README.md",
    "verification/triality-cotangent/SOURCE_REVIEW.md",
    "docs/TRIALITY_COTANGENT_INTAKE_CONTRACT.md",
    "docs/intake/triality-cotangent-20261124/proposal.lean.txt",
    ".github/workflows/triality-cotangent.yml",
)


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    verifier_path = Path(__file__).resolve().parents[1] / "zorn-souriau/check.py"
    spec = importlib.util.spec_from_file_location("triality_cotangent_verifier", verifier_path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"Cannot load shared verifier: {verifier_path}")
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    raise SystemExit(verifier.main(
        targets=TARGETS,
        reused=REUSED,
        extra_sources=EXTRA_SOURCES,
        task_name="triality-cotangent",
    ))
