#!/usr/bin/env python3
"""
SymPy certificate for Greville 1973, "The Souriau--Frame Algorithm and the
Drazin Pseudoinverse".

The exact packet has a size-two zero Jordan block and a regular eigenvalue 2.
For the Souriau--Frame recurrence

    B_0 = I,  p_j = j^-1 trace(A B_(j-1)),  B_j = A B_(j-1) - p_j I,

we get r = 3, s = 1, k = r - s = 2.  Greville's formula

    X = p_s^(-k-1) A^k B_(s-1)^(k+1)

then gives the Drazin pseudoinverse at index 2.
"""

from __future__ import annotations

import sympy as sp


def assert_zero_matrix(m: sp.Matrix, label: str) -> None:
    if any(sp.simplify(entry) != 0 for entry in m):
        raise AssertionError(f"{label} failed:\n{m}")


def main() -> None:
    print("=== Greville 1973 Souriau--Frame / Drazin SymPy certificate ===")

    a = sp.Matrix([[0, 1, 0], [0, 0, 0], [0, 0, 2]])
    ident = sp.eye(3)

    b0 = ident
    p1 = sp.trace(a * b0)
    b1 = a * b0 - p1 * ident
    p2 = sp.Rational(1, 2) * sp.trace(a * b1)
    b2 = a * b1 - p2 * ident
    p3 = sp.Rational(1, 3) * sp.trace(a * b2)
    b3 = a * b2 - p3 * ident

    assert p1 == 2
    assert p2 == 0
    assert p3 == 0
    assert b2 != sp.zeros(3)
    assert b3 == sp.zeros(3)
    print("PASS: Souriau--Frame recurrence has r=3, s=1, k=2")

    k = 2
    x = p1 ** (-(k + 1)) * (a**k) * (b0 ** (k + 1))
    expected = sp.diag(0, 0, sp.Rational(1, 2))
    assert x == expected
    print("PASS: Greville formula gives the expected Drazin inverse")

    assert_zero_matrix(a * x - x * a, "A X = X A")
    assert_zero_matrix(x * a * x - x, "X A X = X")
    assert_zero_matrix(a ** (k + 1) * x - a**k, "A^(k+1) X = A^k")
    assert_zero_matrix(a * x * x - x, "A X^2 = X")
    print("PASS: Drazin index-2 equations hold")

    regular = a * x
    nilpotent = ident - regular
    assert regular == sp.diag(0, 0, 1)
    assert nilpotent == sp.diag(1, 1, 0)
    assert_zero_matrix(regular**2 - regular, "regular projector")
    assert_zero_matrix(nilpotent**2 - nilpotent, "nilpotent projector")
    assert_zero_matrix((a * nilpotent) ** 2, "nilpotent lane square-zero")
    print("PASS: Drazin projectors split regular and nilpotent lanes")

    p = sp.Matrix([[0, 0, 1], [0, 1, 0], [1, 0, 0]])
    p_inv = p.inv()
    ac = p * a * p_inv
    xc = p * x * p_inv
    assert_zero_matrix(ac * xc - xc * ac, "conjugated commutation")
    assert_zero_matrix(xc * ac * xc - xc, "conjugated X A X = X")
    assert_zero_matrix(ac ** (k + 1) * xc - ac**k, "conjugated Drazin power law")
    print("PASS: GL_3(Q) conjugation preserves the Drazin packet")

    print("GREVILLE1973_SYMPY_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
