#!/usr/bin/env python3
"""SymPy audit for the finite Cuntz/Tomita projector shadow."""

from __future__ import annotations

import sympy as sp


def assert_zero_matrix(matrix: sp.Matrix) -> None:
    for entry in matrix:
        assert sp.trigsimp(sp.simplify(entry)) == 0


def main() -> None:
    delta = sp.Symbol("delta", real=True)
    x11, x12, x21, x22 = sp.symbols("x11 x12 x21 x22", complex=True)

    i2 = sp.eye(2)
    p_plus = sp.Matrix([[1, 0], [0, 0]])
    p_minus = sp.Matrix([[0, 0], [0, 1]])
    eta = p_plus - p_minus
    x = sp.Matrix([[x11, x12], [x21, x22]])
    x_star = x.conjugate().T

    c = sp.cosh(delta / 2)
    s = sp.sinh(delta / 2)
    thermal_minus = c * i2 - s * eta
    thermal_plus = c * i2 + s * eta

    assert p_plus * p_plus == p_plus
    assert p_minus * p_minus == p_minus
    assert p_plus * p_minus == sp.zeros(2)
    assert p_minus * p_plus == sp.zeros(2)
    assert p_plus + p_minus == i2
    assert eta * eta == i2
    assert_zero_matrix(thermal_minus * thermal_plus - i2)
    assert_zero_matrix(thermal_plus * thermal_minus - i2)

    delta_half_x = sp.simplify(thermal_minus * x * thermal_plus)
    j_delta_half_x = sp.simplify(thermal_minus * delta_half_x.conjugate().T * thermal_plus)

    assert_zero_matrix(j_delta_half_x - x_star)
    print("Cuntz Tomita-Takesaki finite SymPy audit: ok")


if __name__ == "__main__":
    main()
