#!/usr/bin/env python3
"""SymPy shadow for `SuperBracketHestenesKreinClosure.lean`.

Lean owner:
  lean/InfoGeometry/Canonical/SuperBracketHestenesKreinClosure.lean

Finite shadow:
  Even operators commute with a Krein axis `Gamma`; odd operators anticommute.
  The expected graded closure laws are checked on symbolic 4x4 block matrices.
"""

from __future__ import annotations

import sympy as sp

from common import anticommutator, block_diag2, check, commutator, matrix2, matrix_eq


def run() -> None:
    print("SuperBracketHestenesKreinClosure finite shadow")
    gamma = sp.diag(1, 1, -1, -1)
    E1 = block_diag2(matrix2("A"), matrix2("B"))
    E2 = block_diag2(matrix2("C"), matrix2("D"))
    X = matrix2("X")
    Y = matrix2("Y")
    Z = matrix2("Z")
    W = matrix2("W")
    O1 = sp.Matrix.vstack(sp.Matrix.hstack(sp.zeros(2), X), sp.Matrix.hstack(Y, sp.zeros(2)))
    O2 = sp.Matrix.vstack(sp.Matrix.hstack(sp.zeros(2), Z), sp.Matrix.hstack(W, sp.zeros(2)))

    check("even operator commutes with Gamma", matrix_eq(gamma * E1, E1 * gamma))
    check("odd operator anticommutes with Gamma", matrix_eq(gamma * O1, -O1 * gamma))
    check("even-even commutator is even", matrix_eq(gamma * commutator(E1, E2), commutator(E1, E2) * gamma))
    check("even-odd commutator is odd", matrix_eq(gamma * commutator(E1, O1), -commutator(E1, O1) * gamma))
    check("odd-odd anticommutator is even", matrix_eq(gamma * anticommutator(O1, O2), anticommutator(O1, O2) * gamma))


if __name__ == "__main__":
    run()
