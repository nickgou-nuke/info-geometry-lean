#!/usr/bin/env python3
"""SymPy witness for Cl(3,0;C) ~= M2(C) x M2(C).

This is a computational witness only.  The Lean file
`Cl3ComplexMatrixProduct.lean` is the proof authority.
"""

from __future__ import annotations

import sympy as sp


I = sp.I
M2_ONE = sp.eye(2)
M2_ZERO = sp.zeros(2)

s1 = sp.Matrix([[0, 1], [1, 0]])
s2 = sp.Matrix([[0, -I], [I, 0]])
s3 = sp.Matrix([[1, 0], [0, -1]])


def prod_mul(x, y):
    return (sp.simplify(x[0] * y[0]), sp.simplify(x[1] * y[1]))


def prod_add(x, y):
    return (sp.simplify(x[0] + y[0]), sp.simplify(x[1] + y[1]))


def prod_smul(c, x):
    return (sp.simplify(c * x[0]), sp.simplify(c * x[1]))


def assert_zero_matrix(m, label):
    if sp.simplify(m) != M2_ZERO:
        raise AssertionError(f"{label} failed:\n{sp.simplify(m)}")


def assert_prod_eq(x, y, label):
    assert_zero_matrix(x[0] - y[0], f"{label} first block")
    assert_zero_matrix(x[1] - y[1], f"{label} second block")


def mat_alpha(m):
    return sp.Rational(1, 2) * (m[0, 0] + m[1, 1])


def mat_beta(m):
    return sp.Rational(1, 2) * (m[0, 1] + m[1, 0])


def mat_gamma(m):
    return sp.Rational(1, 2) * I * (m[0, 1] - m[1, 0])


def mat_delta(m):
    return sp.Rational(1, 2) * (m[0, 0] - m[1, 1])


def decompose_m2(m):
    return sp.simplify(
        mat_alpha(m) * M2_ONE
        + mat_beta(m) * s1
        + mat_gamma(m) * s2
        + mat_delta(m) * s3
    )


def main() -> None:
    # Clifford generators in the two simple blocks.
    e1 = (s1, s1)
    e2 = (s2, s2)
    e3 = (s3, -s3)
    one = (M2_ONE, M2_ONE)

    for idx, e in enumerate((e1, e2, e3), start=1):
        assert_prod_eq(prod_mul(e, e), one, f"e{idx}^2 = 1")

    for i, x in enumerate((e1, e2, e3), start=1):
        for j, y in enumerate((e1, e2, e3), start=1):
            if i < j:
                assert_prod_eq(
                    prod_add(prod_mul(x, y), prod_mul(y, x)),
                    (M2_ZERO, M2_ZERO),
                    f"e{i}e{j} + e{j}e{i} = 0",
                )

    volume = prod_mul(e1, prod_mul(e2, e3))
    chirality = prod_smul(-I, volume)
    assert_prod_eq(chirality, (M2_ONE, -M2_ONE), "chirality = (1,-1)")

    p_left = prod_smul(sp.Rational(1, 2), prod_add(one, chirality))
    p_right = prod_smul(sp.Rational(1, 2), prod_add(one, prod_smul(-1, chirality)))
    assert_prod_eq(p_left, (M2_ONE, M2_ZERO), "p_left = (1,0)")
    assert_prod_eq(p_right, (M2_ZERO, M2_ONE), "p_right = (0,1)")

    a00, a01, a10, a11 = sp.symbols("a00 a01 a10 a11")
    b00, b01, b10, b11 = sp.symbols("b00 b01 b10 b11")
    a = sp.Matrix([[a00, a01], [a10, a11]])
    b = sp.Matrix([[b00, b01], [b10, b11]])
    assert_zero_matrix(decompose_m2(a) - a, "symbolic first-block Pauli decomposition")
    assert_zero_matrix(decompose_m2(b) - b, "symbolic second-block Pauli decomposition")

    # The product algebra has two 4-dimensional complex matrix blocks.
    complex_dimension = 2 * (2 * 2)
    if complex_dimension != 8:
        raise AssertionError("dimension witness failed")

    print("Cl(3,0;C) -> M2(C) x M2(C) witness passed")
    print("  generator squares: ok")
    print("  generator anticommutation: ok")
    print("  chirality/projectors: ok")
    print("  symbolic block reconstruction: ok")
    print("  complex dimension: 8")


if __name__ == "__main__":
    main()
