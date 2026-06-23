#!/usr/bin/env python3
"""Exact rational audit for Rose 1976 Drazin polynomial, Example 1."""

from __future__ import annotations

import sympy as sp


def assert_zero_matrix(mat: sp.Matrix, label: str) -> None:
    simplified = mat.applyfunc(sp.simplify)
    if simplified != sp.zeros(*mat.shape):
        raise AssertionError(f"{label} failed:\n{simplified}")


def block_diag(*blocks: sp.Matrix) -> sp.Matrix:
    return sp.diag(*blocks)


def main() -> None:
    n = sp.Matrix([[0, 1], [0, 0]])
    c = sp.Matrix([[0, -1], [1, -5]])
    a = block_diag(n, c)
    ident = sp.eye(4)

    assert_zero_matrix(n**2, "nilpotent block N^2 = 0")
    assert_zero_matrix(c**2 + 5 * c + sp.eye(2), "nonsingular block C^2+5C+I=0")

    x = a**2 * (-24 * a - 115 * ident)
    expected = block_diag(sp.zeros(2), -c - 5 * sp.eye(2))
    assert_zero_matrix(x - expected, "Rose polynomial equals block Drazin candidate")

    assert_zero_matrix(a * x - x * a, "A X = X A")
    assert_zero_matrix(x * a * x - x, "X A X = X")
    assert_zero_matrix(a**3 * x - a**2, "A^(k+1) X = A^k for k=2")

    print("PASS: Rose Example 1 Drazin polynomial and index-two laws")
    print("ROSE1976_SYMPY_AUDIT_OK")


if __name__ == "__main__":
    main()
