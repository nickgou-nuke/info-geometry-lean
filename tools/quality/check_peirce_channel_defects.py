#!/usr/bin/env python3
"""Check Peirce channel defects and adjoint-pair zero detection."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.quality.check_perjes_klein import main

TARGETS = [
    "InfoGeometry.OperatorAlgebra.PeirceSpine.HomogenizedFourierDefect",
    "InfoGeometry.OperatorAlgebra.PeirceSpine.StarMetricNondegeneracy",
    "InfoGeometry.Canonical.PeirceChannelCounterexamples",
]

if __name__ == "__main__":
    main(targets=TARGETS)
