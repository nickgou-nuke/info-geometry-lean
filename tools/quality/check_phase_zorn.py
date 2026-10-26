#!/usr/bin/env python3
"""Run the existing scoped closure checker on the phase/Zorn additions."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.quality import check_peirce_reflection as checker
checker.TARGETS = [
    'InfoGeometry.Algebra.CARModuleDecomposition',
    'InfoGeometry.Canonical.PhaseFlowCARBridge',
    'InfoGeometry.Canonical.DoubledCARIntertwiner',
    'InfoGeometry.Canonical.ZornBdGPhaseFlowBridge',
]
if __name__ == '__main__':
    checker.main()
