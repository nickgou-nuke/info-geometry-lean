#!/usr/bin/env python3
"""Run the existing exact-pin source-closure and native axiom checker.

The imported checker preserves full repository imports and acquires the shared
sequential build lock. This does not claim a root-package Lake build.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_peirce_reflection as checker

checker.TARGETS = [
    'InfoGeometry.Core.DualSeedCartan',
    'InfoGeometry.OperatorAlgebra.PeirceCoupling.StarReflection',
    'InfoGeometry.OperatorAlgebra.PeirceCoupling.RealReflectionGeometry',
    'InfoGeometry.OperatorAlgebra.PeirceCoupling.CartanDirectLimit',
    'InfoGeometry.OperatorAlgebra.PeirceCoupling.RealCartanWitnesses',
    'InfoGeometry.OperatorAlgebra.PeirceCartanColimit',
]

if __name__ == '__main__':
    checker.main()
