#!/usr/bin/env python3
"""Exact pinned-source check of graded boundaries; not a root Lake build."""
import check_cartan_drazin_mp as checker

checker.TARGETS = [
    'InfoGeometry.OperatorAlgebra.LieJordanEndomorphisms',
    'InfoGeometry.Algebra.PeirceLieJordanResolution',
    'InfoGeometry.OperatorAlgebra.LieJordanBoundaryComposition',
    'InfoGeometry.OperatorAlgebra.LieJordanGradedDifferential',
    'InfoGeometry.OperatorAlgebra.PeirceBoundaryDynamics',
    'InfoGeometry.OperatorAlgebra.PeirceBoundaryMetric',
    'InfoGeometry.OperatorAlgebra.PeirceBoundaryWitness',
    'InfoGeometry.OperatorAlgebra.PeirceBoundaryOrder',
]
if __name__ == '__main__':
    checker.main()
