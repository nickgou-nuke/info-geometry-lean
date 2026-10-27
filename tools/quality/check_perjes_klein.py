#!/usr/bin/env python3
"""Exact pinned source-closure verification, using the existing native audit."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_peirce_reflection as checker
checker.TARGETS = [
    'InfoGeometry.Twistor.PerjesConventions',
    'InfoGeometry.Twistor.TwistorKinematicTensor',
]
if __name__ == '__main__':
    checker.main()
