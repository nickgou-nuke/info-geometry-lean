#!/usr/bin/env python3
"""Finite Fibonacci braid witness.

This script checks the concrete two-dimensional Fibonacci anyon F/R matrices:

  F^2 = I
  R^* R = I
  sigma_1 sigma_2 sigma_1 = sigma_2 sigma_1 sigma_2

It does not prove density in a unitary group, a Hayden-Preskill scrambling
bound, or an identification of Betti certificates with protected Majorana
boundary modes.
"""

import sympy as sp


def verify_fibonacci_braiding() -> None:
    golden_ratio = (1 + sp.sqrt(5)) / 2
    identity = sp.eye(2)

    f_matrix = sp.Matrix(
        [
            [1 / golden_ratio, sp.sqrt(1 / golden_ratio)],
            [sp.sqrt(1 / golden_ratio), -1 / golden_ratio],
        ]
    )
    assert sp.simplify(f_matrix * f_matrix - identity) == sp.zeros(2)

    r_matrix = sp.Matrix(
        [
            [sp.exp(-4 * sp.I * sp.pi / 5), 0],
            [0, sp.exp(sp.I * 3 * sp.pi / 5)],
        ]
    )
    assert sp.simplify(r_matrix.H * r_matrix - identity) == sp.zeros(2)

    sigma_1 = r_matrix
    sigma_2 = sp.simplify(f_matrix * r_matrix * f_matrix)

    braid_defect = sp.simplify(sigma_1 * sigma_2 * sigma_1 - sigma_2 * sigma_1 * sigma_2)
    assert braid_defect.applyfunc(sp.nsimplify) == sp.zeros(2)

    print("Finite Fibonacci braid witness")
    print("F^2 = I")
    print("R^* R = I")
    print("sigma_1 sigma_2 sigma_1 = sigma_2 sigma_1 sigma_2")
    print("SUCCESS: finite Fibonacci braid relations verified.")


if __name__ == "__main__":
    verify_fibonacci_braiding()
