#!/usr/bin/env python3
"""Finite biquaternion dual-root regularizer witness.

This script mirrors the Lean owner
`InfoGeometry.Canonical.BiquaternionDualRootRegularizer`.

It checks only finite 2x2 matrix algebra:
  * trace splitting A = scalar(A) + traceless(A);
  * the traceless part has trace zero;
  * traceless Pauli-vector matrices square to a scalar matrix;
  * explicit roots of +I and -I;
  * nilpotent boundaries at the two centers T-I and T+I.

It deliberately does NOT compute or prove analytic matrix-log facts,
exceptional-point topology, GR/QCD physics, entropy production, or continuum
monodromy.  These require separate analytic/topological owner theorems.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def main() -> None:
    a, b, c, d = sp.symbols("a b c d")
    A = sp.Matrix([[a, b], [c, d]])
    I2 = sp.eye(2)

    tr = sp.trace(A)
    scalar = sp.Rational(1, 2) * tr * I2
    traceless = A - scalar
    assert sp.simplify(sp.trace(traceless)) == 0
    assert_matrix_eq("trace splitting", scalar + traceless, A)

    x, y, z = sp.symbols("x y z")
    V = sp.Matrix([[x, y], [z, -x]])
    assert sp.trace(V) == 0
    assert_matrix_eq("traceless vector square scalar", V * V, (x**2 + y * z) * I2)

    sigma_x = sp.Matrix([[0, 1], [1, 0]])
    sigma_z = sp.Matrix([[1, 0], [0, -1]])
    J = sp.Matrix([[0, -1], [1, 0]])
    N = sp.Matrix([[0, 1], [0, 0]])
    assert_matrix_eq("sigma_x root +I", sigma_x**2, I2)
    assert_matrix_eq("sigma_z root +I", sigma_z**2, I2)
    assert_matrix_eq("J root -I", J**2, -I2)

    assert_matrix_eq("nilpotent square", N**2, sp.zeros(2))
    assert sp.det(N) == 0
    assert sp.trace(N) == 0

    T_plus = I2 + N
    T_minus = -I2 + N
    assert_matrix_eq("plus-center boundary square", (T_plus - I2) ** 2, sp.zeros(2))
    assert sp.det(T_plus - I2) == 0
    assert_matrix_eq("minus-center boundary square", (T_minus + I2) ** 2, sp.zeros(2))
    assert sp.det(T_minus + I2) == 0

    print("BIQUATERNION_DUAL_ROOT_REGULARIZER_FINITE_OK")
    print("scope: finite 2x2 trace splitting, Pauli roots, and nilpotent +/-I boundaries only")


if __name__ == "__main__":
    main()
