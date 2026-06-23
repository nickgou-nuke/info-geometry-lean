#!/usr/bin/env python3
"""Exact-rational SymPy certificate for the projective Klein compactification bridge."""

from __future__ import annotations

import sympy as sp


def moebius(mat: sp.Matrix, z: sp.Symbol) -> sp.Expr:
    a, b, c, d = mat.tolist()[0][0], mat.tolist()[0][1], mat.tolist()[1][0], mat.tolist()[1][1]
    return sp.simplify((a * z + b) / (c * z + d))


def main() -> None:
    print("=== Projective Klein compactification SymPy certificate ===")

    a = sp.Matrix([[1, 0], [0, -1]])
    b = sp.Matrix([[1, 1], [0, 1]])
    a_inv = sp.Matrix([[1, 0], [0, -1]])
    I2 = sp.eye(2)
    z = sp.symbols("z")

    assert a * a_inv == I2
    assert a * b * a_inv * b == I2
    assert moebius(a, z) == -z
    assert moebius(-a, z) == moebius(a, z)
    assert sp.simplify(moebius(a, moebius(a, z)) - z) == 0

    x = sp.symbols("x", positive=True)
    mobius_inv = sp.simplify(1 / x)
    assert sp.simplify(1 / mobius_inv - x) == 0
    assert sp.simplify((mobius_inv.subs(x, sp.oo))) == 0
    print("PROJECTIVE_KLEIN_COMPACTIFICATION_SYMPY_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
