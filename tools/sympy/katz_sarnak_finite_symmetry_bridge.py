#!/usr/bin/env python3
"""Finite Katz--Sarnak classical-symmetry witness.

This script mirrors `InfoGeometry.Canonical.KatzSarnakFiniteSymmetryBridge`.
It verifies the finite compact-group algebra only:

* the complex phase a + ib has unit norm when a^2 + b^2 = 1;
* the associated 2x2 real rotation is orthogonal;
* the same matrix preserves the standard symplectic form in dimension two.

No random-matrix universality, density conjecture, Frobenius equidistribution,
or zeta-zero statement is asserted here.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def main() -> None:
    theta = sp.symbols("theta", real=True)
    a = sp.cos(theta)
    b = sp.sin(theta)

    rotation = sp.Matrix([[a, -b], [b, a]])
    symplectic_j = sp.Matrix([[0, -1], [1, 0]])
    identity = sp.eye(2)

    phase_norm_sq = sp.simplify(a**2 + b**2)
    if phase_norm_sq != 1:
        raise AssertionError(f"complex phase norm failed: {phase_norm_sq}")

    assert_matrix_eq(rotation.T * rotation, identity, "R^T R = I")
    assert_matrix_eq(rotation.T * symplectic_j * rotation, symplectic_j, "R^T J R = J")

    print("katz_sarnak_finite_symmetry_bridge: PASS")
    print("  unitary phase norm is one")
    print("  real rotation is orthogonal")
    print("  real rotation preserves the 2D symplectic form")


if __name__ == "__main__":
    main()

