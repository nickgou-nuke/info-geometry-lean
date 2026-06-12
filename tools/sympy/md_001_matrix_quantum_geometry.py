#!/usr/bin/env python3
"""Finite witness for MD 001, Chapter 1 matrix quantum geometry.

Mirrors `InfoGeometry.Physics.MD001MatrixQuantumGeometry`.

Verified finite content only:
* Pauli matrices square to the identity;
* cyclic Pauli anticommutators vanish;
* the determinant of v^0 I + v^1 σ1 + v^2 σ2 + v^3 σ3 is
  (v^0)^2 - (v^1)^2 - (v^2)^2 - (v^3)^2;
* normalized trace/Hilbert--Schmidt readout normalizes Pauli axes;
* every 2x2 matrix recomposes from its Pauli coefficients.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed:\n{reduced}")


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    reduced = mat.applyfunc(lambda x: sp.expand(sp.simplify(x)))
    if reduced != sp.zeros(*reduced.shape):
        raise AssertionError(f"{label} failed:\n{reduced}")


def main() -> int:
    print("=" * 72)
    print("MD 001 MATRIX QUANTUM GEOMETRY FINITE CORE")
    print("=" * 72)

    I2 = sp.eye(2)
    s1 = sp.Matrix([[0, 1], [1, 0]])
    s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    s3 = sp.Matrix([[1, 0], [0, -1]])

    for name, s in [("σ1", s1), ("σ2", s2), ("σ3", s3)]:
        assert_matrix_zero(s * s - I2, f"{name} squares to identity")
    print("Pauli squares: OK")

    assert_matrix_zero(s1 * s2 + s2 * s1, "σ1/σ2 anticommutator")
    assert_matrix_zero(s2 * s3 + s3 * s2, "σ2/σ3 anticommutator")
    assert_matrix_zero(s3 * s1 + s1 * s3, "σ3/σ1 anticommutator")
    print("Pauli anticommutators: OK")

    dt, dx, dy, dz = sp.symbols("dt dx dy dz")
    X = dt * I2 + dx * s1 + dy * s2 + dz * s3
    minkowski = dt**2 - (dx**2 + dy**2 + dz**2)
    assert_zero(X.det() - minkowski, "Pauli determinant/Minkowski readout")
    print("determinant Minkowski readout: OK")

    def hs(A: sp.Matrix, B: sp.Matrix) -> sp.Expr:
        return sp.trace(A * B) / 2

    assert_zero(hs(I2, I2) - 1, "HS(I,I)")
    assert_zero(hs(s1, s1) - 1, "HS(σ1,σ1)")
    assert_zero(hs(s2, s2) - 1, "HS(σ2,σ2)")
    assert_zero(hs(s3, s3) - 1, "HS(σ3,σ3)")
    assert_zero(hs(I2, s1), "HS(I,σ1)")
    print("Hilbert--Schmidt normalization: OK")

    a00, a01, a10, a11 = sp.symbols("a00 a01 a10 a11")
    A = sp.Matrix([[a00, a01], [a10, a11]])
    coeff = [
        (A[0, 0] + A[1, 1]) / 2,
        (A[0, 1] + A[1, 0]) / 2,
        sp.I / 2 * (A[0, 1] - A[1, 0]),
        (A[0, 0] - A[1, 1]) / 2,
    ]
    recomposed = coeff[0] * I2 + coeff[1] * s1 + coeff[2] * s2 + coeff[3] * s3
    assert_matrix_zero(recomposed - A, "Pauli coefficient recomposition")
    print("Pauli coefficient recomposition: OK")

    print("=" * 72)
    print("MD 001 MATRIX QUANTUM GEOMETRY FINITE CORE VERIFIED")
    print("=" * 72)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
