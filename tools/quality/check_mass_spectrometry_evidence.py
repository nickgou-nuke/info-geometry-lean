#!/usr/bin/env python3
"""Scoped pinned-toolchain build and native declaration audit for MS evidence."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality import check_peirce_reflection as checker
checker.TARGETS = [
    "InfoGeometry.MassSpectrometry.ExperimentalObservation",
    "InfoGeometry.MassSpectrometry.PartialPeakAssignment",
    "InfoGeometry.MassSpectrometry.TerminatingFragmentation",
    "InfoGeometry.MassSpectrometry.NumericalEvidenceBounds",
    "InfoGeometry.MassSpectrometry.FiniteExperimentIdentifiability",
    "InfoGeometry.MassSpectrometry.MolecularExperimentEvidence",
    "InfoGeometry.MassSpectrometry.ExperimentalEvidenceAudit",
]
if __name__ == "__main__":
    checker.main()
