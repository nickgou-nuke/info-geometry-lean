#!/usr/bin/env python3
"""SymPy shadow for the concrete Z3 Yang-Baxter owner.

Lean owners:
  lean/InfoGeometry/Canonical/FibonacciParafermionAtoms.lean
  lean/InfoGeometry/Canonical/CelikErlangenBraidBridge.lean

Finite shadow:
  `q = -1`, `a = 1/2`, `b = sqrt(3)/2`, `R = diag(q^-4, q^3)`,
  `B = F R F`, and `R B R = B R B`.
"""

from __future__ import annotations

import sympy as sp

from common import check, matrix_eq, scalar_eq


def run() -> None:
    print("Concrete Z3 Yang-Baxter finite shadow")
    q = sp.Integer(-1)
    a = sp.Rational(1, 2)
    b = sp.sqrt(3) / 2
    F = sp.Matrix([[a, b], [b, -a]])
    R = sp.diag(q ** -4, q ** 3)
    B = F * R * F
    artin_constraint = a**2 * (q ** -4 - q**3) ** 2 + q ** -4 * q**3

    check("a^2 + b^2 = 1", scalar_eq(a**2 + b**2, 1))
    check("scalar Artin constraint is zero", scalar_eq(artin_constraint, 0))
    check("F^2 = I", matrix_eq(F * F, sp.eye(2)))
    check("R B R = B R B", matrix_eq(R * B * R, B * R * B))


if __name__ == "__main__":
    run()
