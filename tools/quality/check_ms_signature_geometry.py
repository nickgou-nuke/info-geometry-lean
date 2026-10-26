#!/usr/bin/env python3
"""Compile exact signature-operator sources and audit their owned declarations."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_peirce_reflection as checker
checker.TARGETS = [
    'InfoGeometry.MassSpectrometry.AbsorbingDrazinBridge',
    'InfoGeometry.MassSpectrometry.SignatureCorrelationGeometry',
    'InfoGeometry.MassSpectrometry.FragmentObservabilityGramian',
    'InfoGeometry.MassSpectrometry.SignatureIdentificationBridge',
    'InfoGeometry.MassSpectrometry.SignatureCyclotomicBridge',
    'InfoGeometry.MassSpectrometry.SpectralOperatorSynthesis',
    'InfoGeometry.MassSpectrometry.SignatureOperatorAudit',
]
if __name__ == '__main__':
    checker.main()
