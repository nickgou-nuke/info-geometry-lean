#!/usr/bin/env python3
"""SymPy shadow for `SuperchargeCentralChargeClosure.lean`.

Lean owner:
  lean/InfoGeometry/Canonical/SuperchargeCentralChargeClosure.lean

Finite shadow:
  Nilpotent odd layers `Q` and `R` with `{Q,R}=Z`; their recursive square is
  exactly the central channel `Z`.
"""

from __future__ import annotations

import sympy as sp

from common import check, matrix_eq, scalar_eq


def run() -> None:
    print("SuperchargeCentralChargeClosure finite shadow")
    q, r = sp.symbols("Q R", commutative=False)
    expanded = sp.expand((q + r) * (q + r))
    expected = q * q + (q * r + r * q) + r * r
    check("free recursive square expands correctly", scalar_eq(expanded, expected))

    Q = sp.Matrix([[0, 1], [0, 0]])
    R = sp.Matrix([[0, 0], [1, 0]])
    Z = Q * R + R * Q
    X = sp.Matrix([[2, 3], [5, 7]])

    check("Q^2 = 0", matrix_eq(Q * Q, sp.zeros(2)))
    check("R^2 = 0", matrix_eq(R * R, sp.zeros(2)))
    check("(Q+R)^2 = {Q,R}", matrix_eq((Q + R) * (Q + R), Z))
    check("central channel is identity", matrix_eq(Z, sp.eye(2)))
    check("central channel commutes with sample X", matrix_eq(Z * X, X * Z))


if __name__ == "__main__":
    run()
