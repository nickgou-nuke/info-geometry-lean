#!/usr/bin/env python3
"""Exact coordinate checks for the native doubled Hestenes/Krein conventions.

Carrier: DoubledSpace E, specializing only the coordinate readout to E=R.
Basis: (physical, ghost), columns; multiplication is composition left-to-right.
Owners: Krein/DoubledSpace.lean (modular_j, spectral_epsilon, complex_i),
Algebra/ChiralRealHyperbolicRotor.lean (hyperbolicRotor).
Not a replacement for arbitrary-E operator proofs or a continuum argument.
Run with the repository's Sage Python (SymPy required).
"""
import hashlib
import json
from pathlib import Path
import sympy as S

root = Path(__file__).resolve().parents[1]
J = S.Matrix([[0, 1], [1, 0]])
eta = S.diag(1, -1)
W = J * eta
c, s = S.symbols('c s', real=True)
X = S.Matrix(2, 2, S.symbols('x0:4', real=True))
R = c * S.eye(2) + s * J
rev = c * S.eye(2) - s * J
checks = {
    'J_squared': J * J - S.eye(2),
    'W_squared': W * W + S.eye(2),
    'J_krein_skew': eta * J.T * eta + J,
    'rotor_krein_adjoint': eta * R.T * eta - rev,
    'rotor_reverse_product': R * rev - (c*c-s*s) * S.eye(2),
    'W_reverses_J': W * J * (-W) + J,
    'W_reverses_rotor': W * R * (-W) - rev,
    'W_krein_anti_isometry': W.T * eta * W + eta,
    'commutator_covariance': W*(J*X-X*J)*(-W)
        + J*(W*X*(-W))-(W*X*(-W))*J,
    'nonzero_action_readback': (J*eta-eta*J)*S.Matrix([1, 0])-S.Matrix([0, 2]),
}
for name, residual in checks.items():
    assert residual.applyfunc(S.expand) == S.zeros(*residual.shape), name
paths = ['lean/InfoGeometry/Krein/DoubledSpace.lean',
         'lean/InfoGeometry/Algebra/ChiralRealHyperbolicRotor.lean',
         'lean/InfoGeometry/Krein/HestenesWeylGenerator.lean']
print(json.dumps({'checks': list(checks), 'result': 'PASS',
                  'basis': ['physical', 'ghost'], 'anti_hom': False,
                  'round_trip_verified': True,
                  'round_trip_lean': 'HestenesWeylGenerator.commutator_nonzero',
                  'round_trip_input': [1, 0], 'round_trip_output': [0, 2],
                  'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  'sources': {p: hashlib.sha256((root/p).read_bytes()).hexdigest()
                              for p in paths}}, indent=2))
