#!/usr/bin/env python3
"""
SymPy certificate for Hartwig 1976, "More on the Souriau--Frame Algorithm and
the Drazin Inverse".

Checks an exact rank-defective matrix with characteristic polynomial
lambda(lambda - 2)(lambda - 3).  The adjugate coefficients of
lambda I - A give Hartwig's group-inverse formula

    A# = (I - A_0 / a_k) (-A_k / a_k)

with a_k = 6.  The certificate also checks the principal idempotent
Z = I - A A# and invariance under an invertible conjugation.
"""

from __future__ import annotations

import sympy as sp


def assert_zero_matrix(m: sp.Matrix, label: str) -> None:
    if any(sp.simplify(entry) != 0 for entry in m):
        raise AssertionError(f"{label} failed:\n{m}")


def main() -> None:
    print("=== Hartwig 1976 Souriau--Frame / Drazin SymPy certificate ===")

    lam = sp.symbols("lambda")
    a = sp.diag(0, 2, 3)
    ident = sp.eye(3)
    char_poly = sp.factor((lam * ident - a).det())
    assert char_poly == lam * (lam - 3) * (lam - 2)

    adj = (lam * ident - a).adjugate()
    coeff = [
        adj.applyfunc(lambda entry, i=i: sp.Poly(entry, lam).coeff_monomial(lam**i))
        for i in range(3)
    ]
    a0, a1, a2 = coeff
    assert a0 == sp.diag(6, 0, 0)
    assert a1 == sp.diag(-5, -3, -2)
    assert a2 == ident
    print("PASS: adj(lambda I - A) Souriau--Frame coefficients recovered")

    ak = sp.Integer(6)
    group_candidate = (ident - a0 / ak) * (-a1 / ak)
    expected = sp.diag(0, sp.Rational(1, 2), sp.Rational(1, 3))
    assert group_candidate == expected
    print("PASS: Hartwig formula produces the expected group inverse")

    x = group_candidate
    assert_zero_matrix(a * x * a - a, "A X A = A")
    assert_zero_matrix(x * a * x - x, "X A X = X")
    assert_zero_matrix(a * x - x * a, "A X = X A")
    assert_zero_matrix(a**2 * x - a, "Drazin index-one power law")
    print("PASS: group inverse and Drazin index-one equations hold")

    z = ident - a * x
    assert z == sp.diag(1, 0, 0)
    assert_zero_matrix(z**2 - z, "Z^2 = Z")
    assert_zero_matrix(a * z, "A Z = 0")
    assert_zero_matrix(z * a, "Z A = 0")
    print("PASS: principal idempotent selects the zero-root lane")

    p = sp.Matrix([[0, 1, 0], [1, 0, 0], [0, 0, 1]])
    p_inv = p.inv()
    a_conj = p * a * p_inv
    x_conj = p * x * p_inv
    assert_zero_matrix(a_conj * x_conj * a_conj - a_conj, "conjugated A X A = A")
    assert_zero_matrix(x_conj * a_conj * x_conj - x_conj, "conjugated X A X = X")
    assert_zero_matrix(a_conj * x_conj - x_conj * a_conj, "conjugated commutation")
    print("PASS: strict GL_3 conjugation preserves the group-inverse representation")

    print("HARTWIG1976_SYMPY_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
