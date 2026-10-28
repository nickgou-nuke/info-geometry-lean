#!/usr/bin/env python3
"""Check the signed real transport owners with the unchanged source-closure auditor."""
import check_cartan_drazin_mp as checker

checker.TARGETS = [
    'InfoGeometry.OperatorAlgebra.LieJordanEndomorphisms',
    'InfoGeometry.OperatorAlgebra.LieJordanBoundaryComposition',
    'InfoGeometry.OperatorAlgebra.PeirceBoundaryDynamics',
    'InfoGeometry.OperatorAlgebra.PeirceBoundaryMetric',
    'InfoGeometry.OperatorAlgebra.SignedBoundaryTransport',
    'InfoGeometry.OperatorAlgebra.PeirceSignedTransport',
    'InfoGeometry.OperatorAlgebra.SignedTransportMetric',
    'InfoGeometry.OperatorAlgebra.SignedTransportWitness',
    'InfoGeometry.OperatorAlgebra.SignedTransportOrder',
]

if __name__ == '__main__':
    checker.main()
