"""Exact-rational SymPy audit for the split-octonion projective null boundary."""

from __future__ import annotations

import sympy as sp


def zorn_norm(a: sp.Rational, b: sp.Rational, u, v) -> sp.Expr:
    return sp.expand(a * b - sum(ui * vi for ui, vi in zip(u, v)))


def main() -> None:
    P = sp.Matrix([[1, 0], [0, 0]])
    M = sp.Matrix([[0, 0], [0, 1]])
    I2 = sp.eye(2)

    assert P * P == P
    assert M * M == M
    assert P * M == sp.zeros(2)
    assert M * P == sp.zeros(2)
    assert P + M == I2
    assert P.det() == 0
    assert M.det() == 0

    zero3 = (sp.Integer(0), sp.Integer(0), sp.Integer(0))
    assert zorn_norm(sp.Integer(1), sp.Integer(0), zero3, zero3) == 0
    assert zorn_norm(sp.Integer(0), sp.Integer(1), zero3, zero3) == 0

    print("split-octonion projective null boundary SymPy certificate: ok")


if __name__ == "__main__":
    main()
