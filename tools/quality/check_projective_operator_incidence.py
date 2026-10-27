#!/usr/bin/env python3
"""Reuse the pinned source-closure checker and native axiom audit for incidence."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.quality import check_peirce_reflection as checker

checker.TARGETS = [
    "InfoGeometry.Projective.IncidenceRank",
    "InfoGeometry.Projective.IncidenceNondegeneracy",
    "InfoGeometry.Projective.ProjectionIncidence",
    "InfoGeometry.Projective.ProjectionRankGeometry",
    "InfoGeometry.Projective.ProjectionCovariance",
    "InfoGeometry.Projective.ProjectionNoncommutativity",
    "InfoGeometry.Projective.OperatorIncidence",
]

if __name__ == "__main__":
    checker.main()
