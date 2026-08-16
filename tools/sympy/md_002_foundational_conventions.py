#!/usr/bin/env python3
"""Finite witness for MD 002 foundational matrix conventions.

Mirrors `InfoGeometry.Physics.MD002FoundationalConventions`.

Verified theorem-safe content only:
* normalized Pauli spacetime determinant with c^2 = 1/2;
* interval convention ds^2 = -2 det(dX) for signature (-,+,+,+);
* normalized Hilbert--Schmidt readouts;
* Jordan product symmetry and commutator antisymmetry;
* finite quaternion relations for the real complex-structure matrices.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, assert_zero, pauli_matrices


def main() -> int:
    print("=" * 72)
    print("MD 002 FOUNDATIONAL FINITE MATRIX CONVENTIONS")
    print("=" * 72)

    I2, s1, s2, s3 = pauli_matrices()

    dt, dx, dy, dz, c = sp.symbols("dt dx dy dz c")
    X_std = dt * I2 + dx * s1 + dy * s2 + dz * s3
    X_norm = c * X_std
    q_plus_minus = dt**2 - (dx**2 + dy**2 + dz**2)
    assert_zero(X_norm.det() - c**2 * q_plus_minus, "normalized determinant before c^2 gate")
    interval = (-2) * X_norm.det()
    interval_gate = sp.expand(interval.subs(c**2, sp.Rational(1, 2)))
    assert_zero(interval_gate - (-dt**2 + dx**2 + dy**2 + dz**2), "-2 det normalized interval")
    print("normalized determinant and interval: OK")

    def hs(A: sp.Matrix, B: sp.Matrix) -> sp.Expr:
        return sp.trace(A * B) / 2

    assert_zero(hs(c * I2, c * I2).subs(c**2, sp.Rational(1, 2)) - sp.Rational(1, 2), "normalized HS identity")
    assert_zero(hs(c * s1, c * s1).subs(c**2, sp.Rational(1, 2)) - sp.Rational(1, 2), "normalized HS sigma1")
    print("normalized Hilbert--Schmidt readouts: OK")

    a = sp.symbols("a0:4")
    b = sp.symbols("b0:4")
    A = sp.Matrix([[a[0], a[1]], [a[2], a[3]]])
    B = sp.Matrix([[b[0], b[1]], [b[2], b[3]]])
    jordan_AB = (A * B + B * A) / 2
    jordan_BA = (B * A + A * B) / 2
    lie_AB = A * B - B * A
    lie_BA = B * A - A * B
    assert_matrix_zero(jordan_AB - jordan_BA, "Jordan product symmetry")
    assert_matrix_zero(lie_BA + lie_AB, "Lie product antisymmetry")
    print("Jordan/Lie finite products: OK")

    I4 = sp.eye(4)
    complexI = sp.Matrix([[0, -1, 0, 0], [1, 0, 0, 0], [0, 0, 0, -1], [0, 0, 1, 0]])
    complexJ = sp.Matrix([[0, 0, -1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, -1, 0, 0]])
    complexK = sp.Matrix([[0, 0, 0, -1], [0, 0, -1, 0], [0, 1, 0, 0], [1, 0, 0, 0]])
    assert_matrix_zero(complexI * complexI + I4, "I^2 = -1")
    assert_matrix_zero(complexJ * complexJ + I4, "J^2 = -1")
    assert_matrix_zero(complexK * complexK + I4, "K^2 = -1")
    assert_matrix_zero(complexI * complexJ - complexK, "IJ = K")
    assert_matrix_zero(complexJ * complexK - complexI, "JK = I")
    assert_matrix_zero(complexK * complexI - complexJ, "KI = J")
    print("quaternion complex-structure relations: OK")

    print("=" * 72)
    print("MD 002 FOUNDATIONAL FINITE MATRIX CONVENTIONS VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
