#!/usr/bin/env python3
"""Finite light-cone string projection witness.

This script verifies the explicit 10x10 change-of-basis matrix used to isolate
the first light-cone pair from the remaining 8 transverse coordinates.

It checks only the finite algebraic shadow:

* the matrix is orthogonal;
* its first 2x2 block is the standard light-cone rotation;
* the remaining 8 coordinates are fixed;
* the transform is an involution on this finite model.

No mass-spectrum theorem, string quantization theorem, or E6(6) symmetry claim
is asserted here.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def basis_vector(n: int, i: int) -> sp.Matrix:
    v = sp.zeros(n, 1)
    v[i, 0] = 1
    return v


def build_projection_matrix() -> sp.Matrix:
    """10x10 finite change-of-basis matrix.

    The first two coordinates are rotated by the Hadamard light-cone block
    and the remaining eight coordinates are left unchanged.
    """
    m = sp.eye(10)
    block = sp.Matrix([[1, 1], [1, -1]]) / sp.sqrt(2)
    m[:2, :2] = block
    return m


def verify_orthogonality(m: sp.Matrix) -> None:
    i10 = sp.eye(10)
    assert_matrix_eq(m.T * m, i10, "M^T M = I")
    assert_matrix_eq(m * m.T, i10, "M M^T = I")
    assert_matrix_eq(m**2, i10, "M^2 = I")
    det_m = sp.simplify(m.det())
    if det_m != -1:
        raise AssertionError(f"det(M) expected -1, got {det_m}")


def verify_lightcone_block(m: sp.Matrix) -> None:
    e0 = basis_vector(10, 0)
    e1 = basis_vector(10, 1)
    root2 = sp.sqrt(2)

    assert_matrix_eq(m * e0, (e0 + e1) / root2, "first basis vector")
    assert_matrix_eq(m * e1, (e0 - e1) / root2, "second basis vector")

    for i in range(2, 10):
        ei = basis_vector(10, i)
        assert_matrix_eq(m * ei, ei, f"transverse basis vector e{i}")


def verify_inverse_action(m: sp.Matrix) -> None:
    root2 = sp.sqrt(2)
    xplus, xminus = sp.symbols("xplus xminus")
    doubled = sp.Matrix([xplus, xminus] + [sp.symbols(f"x{i}") for i in range(2, 10)])
    transformed = m * doubled
    recovered = m * transformed

    assert sp.simplify(transformed[0] - (xplus + xminus) / root2) == 0
    assert sp.simplify(transformed[1] - (xplus - xminus) / root2) == 0
    assert_matrix_eq(recovered, doubled, "recovery by involution")


def main() -> None:
    m = build_projection_matrix()
    verify_orthogonality(m)
    verify_lightcone_block(m)
    verify_inverse_action(m)

    print("lightcone_string_projection_matrix: PASS")
    print("  orthogonal change-of-basis verified")
    print("  first pair maps to the light-cone block")
    print("  transverse coordinates are fixed")
    print("  finite involutive readback verified")


if __name__ == "__main__":
    main()

