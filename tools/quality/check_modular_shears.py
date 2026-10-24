#!/usr/bin/env python3
"""Scoped modular-shear check, reusing the parent PR's exact-pin audited runner."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_peirce_weyl as checker

checker.TARGETS = [
    'InfoGeometry.Core.ParabolicShearRelations',
    'InfoGeometry.Core.ParabolicModularRepresentation',
    'InfoGeometry.Canonical.PeirceModularBridge',
    'InfoGeometry.Canonical.IntegralModularShears',
]

if __name__ == '__main__':
    checker.main()
