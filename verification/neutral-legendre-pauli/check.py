#!/usr/bin/env python3
"""Fresh focused compilation and axiom audit for the neutral/Legendre/Pauli packet.

Usage: python3 check.py --repo /absolute/repo --output /new/report/path
The shared verifier retains its original Dirac packet as its default. This
entrypoint supplies six explicit owners and fingerprints itself as well as
that verifier, its lock wrapper, the pins, and every selected source.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

TARGETS = (
    "InfoGeometry.Canonical.OrientedPfaffianMatching",
    "InfoGeometry.Canonical.MajoranaPfaffian4",
    "InfoGeometry.Geometry.DualFlatKreinLegendreSubmodules",
    "InfoGeometry.OperatorAlgebra.OperatorDirichlet.MatrixLegendreFenchel",
    "InfoGeometry.Twistor.RealPauliIncidence",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.JordanCorner",
)
REUSED = (
    "InfoGeometry.Clifford.NeutralPhaseSpaceCore.neutralOmega",
    "InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin",
    "InfoGeometry.Geometry.DualFlatKreinLegendreGraph.IsSymmetricDuality",
    "InfoGeometry.OperatorAlgebra.OperatorDirichlet.legendre_conjugate_isGreatest",
    "InfoGeometry.Convex.fenchelConj_eq_of_isGreatest",
    "InfoGeometry.Canonical.RealPauliPfaffianKernel.pauli_sub_det_eq_zero_iff",
    "InfoGeometry.Canonical.RealPauliPfaffianKernel.pauli_commutes_phase",
    "InfoGeometry.Twistor.RealTwistorIncidence.shared_nonzero_twistor_iff",
    "InfoGeometry.Twistor.RealTwistorIncidence.spinorEquivIncidence",
    "InfoGeometry.Core.JordanAssociator.symm_associator_eq_double_commutator",
    "InfoGeometry.Core.JordanAssociator.jordan_associator_eq_expanded_double_commutator",
)
REUSED_OWNERS = (
    "InfoGeometry.Clifford.NeutralPhaseSpaceCore",
    "InfoGeometry.Geometry.DualFlatKreinLegendreGraph",
    "InfoGeometry.OperatorAlgebra.OperatorDirichlet.MatrixLegendre",
    "InfoGeometry.Convex.FenchelConjugate",
    "InfoGeometry.Convex.Bregman",
    "InfoGeometry.Canonical.RealPauliPfaffianKernel",
    "InfoGeometry.Twistor.RealTwistorIncidence",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman",
    "InfoGeometry.Core.JordanAssociatorRing",
    "InfoGeometry.Core.JordanAssociator",
)


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    verifier_path = Path(__file__).resolve().parents[1] / "real-dirac-spin-nambu/check.py"
    spec = importlib.util.spec_from_file_location("focused_packet_verifier", verifier_path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"Cannot load shared verifier: {verifier_path}")
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    raise SystemExit(verifier.main(
        targets=TARGETS, owners=TARGETS, reused=REUSED, reused_owners=REUSED_OWNERS,
        probe_name="NeutralLegendrePauliAxioms.lean", entrypoint=Path(__file__),
    ))
