#!/usr/bin/env python3
"""Check integral Peirce algebra, unitary Cayley transport, and the spectral criterion."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.quality.check_perjes_klein import main

TARGETS = [
    "InfoGeometry.OperatorAlgebra.PeirceSpine.IntegralOrder",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.IntegralReynolds",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.IntegralOrderReynolds",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.StarDaughterGeometry",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.UnitaryCayley",
    "InfoGeometry.OperatorAlgebra.PositiveSpectralGap",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.HomogenizedFourierDefect",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.StarMetricNondegeneracy",
    "InfoGeometry.Canonical.PeirceChannelCounterexamples",
    "InfoGeometry.Canonical.PeirceIntegralReynoldsCounterexample",
]

if __name__ == "__main__":
    main(targets=TARGETS)
