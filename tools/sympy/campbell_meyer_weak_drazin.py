#!/usr/bin/env python3
"""
Exact SymPy certificate for Campbell--Meyer 1978, "Weak Drazin Inverses".

The packet uses A = diag(2, N_2), where N_2 is square-zero.  It checks the
weak relation B A^(k+1) = A^k at k = 2, the Drazin subcase, the
polynomial/Souriau--Frame commuting weak inverse 1/2 I, a projective readout,
and GL_3(Q) conjugation.
"""

from __future__ import annotations

import sympy as sp


def assert_zero_matrix(m: sp.Matrix, label: str) -> None:
    if any(sp.simplify(entry) != 0 for entry in m):
        raise AssertionError(f"{label} failed:\n{m}")


def assert_weak(a: sp.Matrix, b: sp.Matrix, k: int, label: str) -> None:
    assert_zero_matrix(b * (a ** (k + 1)) - (a ** k), f"{label}: B A^(k+1) = A^k")


def assert_drazin(a: sp.Matrix, d: sp.Matrix, k: int, label: str) -> None:
    assert_zero_matrix(a * d - d * a, f"{label}: A D = D A")
    assert_zero_matrix(d * a * d - d, f"{label}: D A D = D")
    assert_zero_matrix((a ** (k + 1)) * d - (a ** k), f"{label}: A^(k+1)D = A^k")


def main() -> None:
    print("=== Campbell--Meyer 1978 weak Drazin SymPy certificate ===")

    a = sp.Matrix([[2, 0, 0], [0, 0, 1], [0, 0, 0]])
    nil = sp.Matrix([[0, 0, 0], [0, 0, 1], [0, 0, 0]])
    ident = sp.eye(3)

    assert nil**2 == sp.zeros(3)
    assert a**2 == sp.diag(4, 0, 0)
    assert a**3 == 2 * (a**2)
    print("PASS: diag(2,N2) packet and polynomial x^2(x-2) readout")

    drazin = sp.diag(sp.Rational(1, 2), 0, 0)
    assert_drazin(a, drazin, 2, "Drazin inverse")
    assert_weak(a, drazin, 2, "Drazin inverse")

    wild = sp.Matrix([[sp.Rational(1, 2), 3, 5], [0, 7, 11], [0, 13, 17]])
    assert_weak(a, wild, 2, "wild weak inverse")
    assert wild != drazin
    assert a * wild != wild * a
    print("PASS: weak inverses are non-unique and need not commute")

    polynomial = sp.Rational(1, 2) * ident
    assert_weak(a, polynomial, 2, "polynomial weak inverse")
    assert a * polynomial == polynomial * a
    assert polynomial.det() == sp.Rational(1, 8)
    p1 = sp.trace(a * ident)
    assert p1 == 2
    assert p1 ** -1 * ident == polynomial
    assert polynomial != drazin
    print("PASS: polynomial/Souriau--Frame inverse is invertible and weak")

    projective = sp.Matrix([[sp.Rational(1, 2), 2, 3], [0, 0, 5], [0, 0, 7]])
    assert_weak(a, projective, 2, "projective-shaped weak inverse")
    ba = projective * a
    assert ba == sp.Matrix([[1, 0, 2], [0, 0, 0], [0, 0, 0]])
    assert ba**2 == ba
    print("PASS: projective-shaped weak inverse has idempotent BA readout")

    commuting = sp.Matrix([[sp.Rational(1, 2), 0, 0], [0, 3, 4], [0, 0, 3]])
    assert_weak(a, commuting, 2, "commuting weak inverse")
    assert a * commuting == commuting * a
    print("PASS: commuting weak inverse with nonzero nilpotent-lane data")

    p = sp.Matrix([[0, 0, 1], [0, 1, 0], [1, 0, 0]])
    assert p * p == ident
    assert_weak(p * a * p, p * polynomial * p, 2, "GL_3(Q) conjugate")
    print("PASS: GL_3(Q) conjugation preserves the weak relation")

    print("CAMPBELL_MEYER_WEAK_DRAZIN_SYMPY_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
