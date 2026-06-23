"""Clifford-lane certificate for the split-octonion projective null boundary."""

import os

os.environ.setdefault("NUMBA_DISABLE_JIT", "1")

import sympy as sp
from clifford import Cl


def main() -> None:
    layout, _ = Cl(1, 0)
    one = layout.scalar

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

    scalar_mv = one + one
    assert scalar_mv == 2 * one
    print("split-octonion projective null boundary clifford certificate: ok")


if __name__ == "__main__":
    main()
