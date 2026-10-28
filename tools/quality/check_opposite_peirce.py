#!/usr/bin/env python3
"""Pinned source-closure verification with native all-owned-declaration audit."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_cartan_drazin_mp as checker

checker.TARGETS = [
    'InfoGeometry.NCG.OppositePeirceCoupling',
    'InfoGeometry.NCG.OppositePeirceTrace',
    'InfoGeometry.NCG.OppositePeirceRealMetric',
    'InfoGeometry.NCG.OppositePeirceWitness',
    'InfoGeometry.NCG.OppositePeirceOrder',
    'InfoGeometry.NCG.OppositePeirceAudit',
]

if __name__ == '__main__':
    checker.main()
