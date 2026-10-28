#!/usr/bin/env python3
"""Specialize the existing serial source-closure checker; not a root Lake build."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_peirce_weyl as checker

checker.TARGETS = [
    'InfoGeometry.OperatorAlgebra.LieJordanDuality',
]

if __name__ == '__main__':
    checker.main()
