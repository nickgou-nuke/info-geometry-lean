#!/usr/bin/env python3
"""Scoped Perjes/Klein verification; no root-package or full-paper claim.

Reuse the existing repository checker and public Lean collectAxioms audit.
The selected entry points grow only as actual owner files are implemented.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_bilateral_kernel as checker

OWNERS = [
    'InfoGeometry.Twistor.PerjesConventions',
    'InfoGeometry.Twistor.TwistorKinematicTensor',
    'InfoGeometry.Twistor.TwistorConstituentKinematics',
    'InfoGeometry.Twistor.TwistorConstituentCCR',
    'InfoGeometry.Twistor.PerjesNullLineCorrespondence',
    'InfoGeometry.Twistor.HomogeneousTwistorCech',
    'InfoGeometry.Twistor.PenroseContourTransform',
    'InfoGeometry.Twistor.TwistorInternalSymmetry',
    'InfoGeometry.Twistor.KleinTwistorPinTransport',
]

if __name__ == '__main__':
    checker.TARGETS = [m for m in OWNERS
        if (ROOT / 'lean' / (m.replace('.', '/') + '.lean')).is_file()]
    print('Implemented owners selected:', *checker.TARGETS, sep='\n', flush=True)
    checker.main()
