#!/usr/bin/env python3
"""Finite witness for two-sheeted complex polarization.

The Lean owner surface is
`InfoGeometry.Canonical.TwoSheetedComplexPolarization`.

This script checks the finite matrix atom:

* J swaps the two sheets.
* epsilon grades the two sheets.
* K = J epsilon is the real complex/polarization axis.
* K^2 = -I and J K J = -K.
* P_+ and P_- split the doubled carrier.
* a + b i reads back as a I + b K.
"""

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def main() -> None:
    print("=" * 72)
    print("TWO-SHEETED COMPLEX POLARIZATION -- SYMPY VERIFICATION")
    print("=" * 72)

    identity = sp.eye(2)
    zero = sp.zeros(2)

    # H = H_+ ⊕ H_- with one finite real coordinate per sheet.
    J = sp.Matrix([[0, 1], [1, 0]])
    epsilon = sp.Matrix([[1, 0], [0, -1]])
    K = J * epsilon

    assert_matrix_eq(J**2, identity, "sheet swap J^2 = I")
    assert_matrix_eq(epsilon**2, identity, "sheet grading epsilon^2 = I")
    assert_matrix_eq(J * epsilon + epsilon * J, zero, "J epsilon anticommutes")
    assert_matrix_eq(K, J * epsilon, "polarization axis K = J epsilon")
    assert_matrix_eq(K**2, -identity, "K^2 = -I")
    assert_matrix_eq(J * K * J, -K, "modular reflection flips K")
    assert_matrix_eq(epsilon * K, -J, "epsilon K = -J")
    assert_matrix_eq(K * epsilon, J, "K epsilon = J")
    print("  two-sheet involutions and emergent K^2 = -I verified")

    P_plus = (identity + epsilon) / 2
    P_minus = (identity - epsilon) / 2

    assert_matrix_eq(P_plus**2, P_plus, "P_plus idempotent")
    assert_matrix_eq(P_minus**2, P_minus, "P_minus idempotent")
    assert_matrix_eq(P_plus * P_minus, zero, "P_plus P_minus = 0")
    assert_matrix_eq(P_minus * P_plus, zero, "P_minus P_plus = 0")
    assert_matrix_eq(P_plus + P_minus, identity, "P_plus + P_minus = I")
    print("  sheet projectors split the doubled carrier")

    x, xi = sp.symbols("x xi")
    doubled = sp.Matrix([x, xi])
    physical = sp.Matrix([x, 0])
    ghost = sp.Matrix([0, xi])

    assert_matrix_eq(P_plus * doubled, physical, "P_plus extracts physical sheet")
    assert_matrix_eq(P_minus * doubled, ghost, "P_minus extracts ghost sheet")
    assert_matrix_eq(K * physical, sp.Matrix([0, x]), "K maps physical to ghost")
    assert_matrix_eq(K * ghost, sp.Matrix([-xi, 0]), "K maps ghost to negative physical")
    print("  K rotates between the two real sheets")

    a, b, c, d = sp.symbols("a b c d")
    hestenes_z = a * identity + b * K
    hestenes_w = c * identity + d * K
    expected_product = (a * c - b * d) * identity + (a * d + b * c) * K
    assert_matrix_eq(hestenes_z * hestenes_w, expected_product, "(a+bK)(c+dK)")
    assert_matrix_eq(0 * identity + 1 * K, K, "scalar i reads as K")
    print("  Hestenes scalar readback a+bi -> aI+bK verified")

    print("=" * 72)
    print("TWO-SHEETED COMPLEX POLARIZATION VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
