#!/usr/bin/env python3
"""Check the exact twistor/homotope source closure with the existing locked checker."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tools.quality.check_perjes_klein import main

TARGETS = [
    "InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope",
    "InfoGeometry.Twistor.TwoTwistorHadamardFrame",
    "InfoGeometry.Twistor.RealInfinityMatrixPencil",
    "InfoGeometry.Twistor.RealInfinityMatrixPencilBridge",
    "InfoGeometry.Clifford.Cl11TensorTransposeCensus",
]

if __name__ == "__main__":
    main(targets=TARGETS)
