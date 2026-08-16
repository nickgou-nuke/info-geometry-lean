#!/usr/bin/env python3
"""Finite witness for MD 000 / n000 foundational matrix framework.

The fetched MD repository does not contain `000.md`; the closest source is
`n000.md`.  This script mirrors
`InfoGeometry.Physics.MD000FoundationalMatrixFramework`.

Verified theorem-safe content only:
* Pauli determinant/Minkowski readout;
* normalized interval convention with c^2=1/2;
* trace coordinate recovery and Euclidean norm readout;
* Jordan symmetry and Lie-commutator antisymmetry;
* finite quaternionic coordinate complex structures and ambient complex
  structure metric/skew-form identities.

No smooth manifold, Lorentz-cover, Clifford-bundle, tetrad/spin-connection,
Bures/QFI, Kähler-Einstein, or physical spacetime-identification theorem is
claimed.
"""

from __future__ import annotations

import sys
from pathlib import Path
import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_zero, assert_zero


def dot4(a: sp.Matrix, b: sp.Matrix) -> sp.Expr:
    return (a.T * b)[0]


def I4(v: sp.Matrix) -> sp.Matrix:
    t, x, y, z = v
    return sp.Matrix([-x, t, -z, y])


def J4(v: sp.Matrix) -> sp.Matrix:
    t, x, y, z = v
    return sp.Matrix([-y, z, t, -x])


def K4(v: sp.Matrix) -> sp.Matrix:
    t, x, y, z = v
    return sp.Matrix([-z, -y, x, t])


def J0(v: sp.Matrix) -> sp.Matrix:
    a0, b0, a1, b1, a2, b2, a3, b3 = v
    return sp.Matrix([-b0, a0, -b1, a1, -b2, a2, -b3, a3])


def main() -> int:
    print("=" * 72)
    print("MD 000 / n000 FINITE FOUNDATIONAL MATRIX FRAMEWORK")
    print("=" * 72)

    I = sp.I
    I2 = sp.eye(2)
    s1 = sp.Matrix([[0, 1], [1, 0]])
    s2 = sp.Matrix([[0, -I], [I, 0]])
    s3 = sp.Matrix([[1, 0], [0, -1]])
    t, x, y, z, c = sp.symbols("t x y z c")
    X = t * I2 + x * s1 + y * s2 + z * s3
    assert_zero(X.det() - (t**2 - x**2 - y**2 - z**2), "Pauli determinant readout")
    Xn = c * X
    assert_zero(Xn.det() - c**2 * (t**2 - x**2 - y**2 - z**2), "normalized determinant")
    interval = -2 * Xn.det()
    assert_zero(interval.subs(c**2, sp.Rational(1, 2)) - (-t**2 + x**2 + y**2 + z**2), "normalized interval")
    print("Pauli determinant / interval identities: OK")

    axes = [c * I2, c * s1, c * s2, c * s3]
    for label, axis, coord in zip(["t", "x", "y", "z"], axes, [t, x, y, z]):
        assert_zero(sp.trace(axis * Xn).subs(c**2, sp.Rational(1, 2)) - coord, f"trace recovers {label}")
    assert_zero(sp.trace(Xn * Xn).subs(c**2, sp.Rational(1, 2)) - (t**2 + x**2 + y**2 + z**2), "trace self norm")
    print("trace coordinate/norm identities: OK")

    a00, a01, a10, a11, b00, b01, b10, b11 = sp.symbols("a00 a01 a10 a11 b00 b01 b10 b11")
    A = sp.Matrix([[a00, a01], [a10, a11]])
    B = sp.Matrix([[b00, b01], [b10, b11]])
    jordan = sp.Rational(1, 2) * (A * B + B * A)
    jordan_rev = sp.Rational(1, 2) * (B * A + A * B)
    lie = A * B - B * A
    lie_rev = B * A - A * B
    assert_matrix_zero(jordan - jordan_rev, "Jordan product symmetry")
    assert_matrix_zero(lie_rev + lie, "Lie product antisymmetry")
    print("Jordan/Lie finite algebra: OK")

    u = sp.Matrix(sp.symbols("u0:4"))
    v = sp.Matrix(sp.symbols("v0:4"))
    assert_matrix_zero(I4(I4(u)) + u, "I4 square")
    assert_matrix_zero(J4(J4(u)) + u, "J4 square")
    assert_matrix_zero(K4(K4(u)) + u, "K4 square")
    assert_matrix_zero(I4(J4(u)) - K4(u), "I4 J4 = K4")
    assert_zero(dot4(I4(u), I4(v)) - dot4(u, v), "I4 metric preservation")
    assert_zero(dot4(I4(v), u) + dot4(I4(u), v), "omegaI skew")
    print("coordinate quaternion complex structures: OK")

    p = sp.Matrix(sp.symbols("p0:8"))
    q = sp.Matrix(sp.symbols("q0:8"))
    assert_matrix_zero(J0(J0(p)) + p, "ambient J0 square")
    assert_zero(dot4(J0(p)[:4, :], J0(q)[:4, :]) + dot4(J0(p)[4:, :], J0(q)[4:, :]) - (p.T * q)[0], "ambient metric preservation")
    assert_zero((J0(q).T * p)[0] + (J0(p).T * q)[0], "ambient omega0 skew")
    print("ambient complex structure: OK")

    print("=" * 72)
    print("MD 000 / n000 FINITE FOUNDATIONAL MATRIX FRAMEWORK VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
