#!/usr/bin/env python3
"""SymPy shadow for `ClosureInvolution.lean` and `FiveGradeClosureSymmetry.lean`.

Lean owners:
  lean/InfoGeometry/OperatorAlgebra/ClosureInvolution.lean
  lean/InfoGeometry/OperatorAlgebra/FiveGradeClosureSymmetry.lean

Finite shadow:
  A five-grade basis `g_-2, g_-1, g_0, g_+1, g_+2` with closure involution
  reversing opposite grades and fixing the middle sector.
"""

from __future__ import annotations

import sympy as sp

from common import check, matrix_eq


def basis(index: int) -> sp.Matrix:
    return sp.eye(5)[:, index]


def run() -> None:
    print("ClosureInvolution/FiveGradeClosureSymmetry finite shadow")
    theta = sp.Matrix(
        [
            [0, 0, 0, 0, 1],
            [0, 0, 0, 1, 0],
            [0, 0, 1, 0, 0],
            [0, 1, 0, 0, 0],
            [1, 0, 0, 0, 0],
        ]
    )
    identity = sp.eye(5)
    x = sp.Matrix(sp.symbols("x0:5"))
    fixed = (x + theta * x) / 2
    anti = (x - theta * x) / 2

    check("theta^2 = I", matrix_eq(theta * theta, identity))
    check("fixed part is fixed", matrix_eq(theta * fixed, fixed))
    check("anti part is anti-fixed", matrix_eq(theta * anti, -anti))
    check("fixed + anti = x", matrix_eq(fixed + anti, x))
    check("g0 is setwise stable", matrix_eq(theta * basis(2), basis(2)))
    check("g_-1 maps to g_+1", matrix_eq(theta * basis(1), basis(3)))
    check("g_+1 maps to g_-1", matrix_eq(theta * basis(3), basis(1)))
    check("g_-2 maps to g_+2", matrix_eq(theta * basis(0), basis(4)))
    check("g_+2 maps to g_-2", matrix_eq(theta * basis(4), basis(0)))


if __name__ == "__main__":
    run()
