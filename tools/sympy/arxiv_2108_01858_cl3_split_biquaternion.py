#!/usr/bin/env python3
"""Finite witness for arXiv:2108.01858v2, Cl(3) split-biquaternion slice.

The paper discusses complex split biquaternions via the decomposition of
complex Clifford algebra Cl(3).  This script checks only the theorem-safe
finite algebraic readout already owned in Lean by
`InfoGeometry.Clifford.Cl3ComplexMatrixProduct`:

  Cl(3; C) -> M2(C) x M2(C),
  chirality -> (I, -I),
  pL -> (I, 0), pR -> (0, I),
  dim_C(M2 x M2) = 8.

No sterile-neutrino, Pati-Salam, gauge-group, generation-count, Higgs, dark
matter, or exceptional-Jordan physics claim is checked here.
"""

from __future__ import annotations

import sympy as sp

I = sp.I
Z2 = sp.zeros(2)
I2 = sp.eye(2)

s1 = sp.Matrix([[0, 1], [1, 0]])
s2 = sp.Matrix([[0, -I], [I, 0]])
s3_left = sp.Matrix([[1, 0], [0, -1]])
s3_right = -s3_left


def prod_mul(x, y):
    return (sp.simplify(x[0] * y[0]), sp.simplify(x[1] * y[1]))


def prod_add(x, y):
    return (sp.simplify(x[0] + y[0]), sp.simplify(x[1] + y[1]))


def prod_sub(x, y):
    return (sp.simplify(x[0] - y[0]), sp.simplify(x[1] - y[1]))


def prod_smul(c, x):
    return (sp.simplify(c * x[0]), sp.simplify(c * x[1]))


def assert_prod_eq(x, y, label):
    if sp.simplify(x[0] - y[0]) != Z2 or sp.simplify(x[1] - y[1]) != Z2:
        raise AssertionError(f"{label}: {x} != {y}")


def main() -> None:
    one = (I2, I2)
    e1 = (s1, s1)
    e2 = (s2, s2)
    e3 = (s3_left, s3_right)

    for idx, e in enumerate([e1, e2, e3], start=1):
        assert_prod_eq(prod_mul(e, e), one, f"e{idx}^2=1")

    volume = prod_mul(e1, prod_mul(e2, e3))
    chirality = prod_smul(-I, volume)
    assert_prod_eq(chirality, (I2, -I2), "chirality block split")
    assert_prod_eq(prod_mul(chirality, chirality), one, "chirality square")

    pL = prod_smul(sp.Rational(1, 2), prod_add(one, chirality))
    pR = prod_smul(sp.Rational(1, 2), prod_sub(one, chirality))
    assert_prod_eq(pL, (I2, Z2), "left projector")
    assert_prod_eq(pR, (Z2, I2), "right projector")
    assert_prod_eq(prod_mul(pL, pL), pL, "pL idempotent")
    assert_prod_eq(prod_mul(pR, pR), pR, "pR idempotent")
    assert_prod_eq(prod_mul(pL, pR), (Z2, Z2), "pL pR orthogonal")
    assert_prod_eq(prod_add(pL, pR), one, "pL+pR=1")

    assert 2 * 2 * 2 == 8
    print("ARXIV_2108_01858_CL3_SPLIT_BIQUATERNION_OK")
    print("scope: finite Cl(3;C) split-biquaternion/chirality projector slice only")


if __name__ == "__main__":
    main()
