#!/usr/bin/env python3
"""SymPy shadow for `OperatorCartanSuperbracketClosure.lean`.

Lean owner:
  lean/InfoGeometry/Canonical/OperatorCartanSuperbracketClosure.lean

Finite shadow:
  Checks the operator-level Cartan profile in conjugation form:
  `Gamma*T*Gamma = ±T` and closure of commutators/anticommutators.
"""

from __future__ import annotations

import sympy as sp

from common import anticommutator, block_diag2, check, commutator, matrix2, matrix_eq


def conjugate(gamma: sp.Matrix, operator: sp.Matrix) -> sp.Matrix:
    return gamma * operator * gamma


def run() -> None:
    print("OperatorCartanSuperbracketClosure finite shadow")
    gamma = sp.diag(1, 1, -1, -1)
    e1 = block_diag2(matrix2("E"), matrix2("F"))
    e2 = block_diag2(matrix2("G"), matrix2("H"))
    x = matrix2("X")
    y = matrix2("Y")
    z = matrix2("Z")
    w = matrix2("W")
    o1 = sp.Matrix.vstack(sp.Matrix.hstack(sp.zeros(2), x), sp.Matrix.hstack(y, sp.zeros(2)))
    o2 = sp.Matrix.vstack(sp.Matrix.hstack(sp.zeros(2), z), sp.Matrix.hstack(w, sp.zeros(2)))

    check("Gamma^2 = I", matrix_eq(gamma * gamma, sp.eye(4)))
    check("even conjugation fixed", matrix_eq(conjugate(gamma, e1), e1))
    check("odd conjugation flips sign", matrix_eq(conjugate(gamma, o1), -o1))
    check("even-even commutator fixed", matrix_eq(conjugate(gamma, commutator(e1, e2)), commutator(e1, e2)))
    check("even-odd commutator odd", matrix_eq(conjugate(gamma, commutator(e1, o1)), -commutator(e1, o1)))
    check("odd-odd commutator fixed", matrix_eq(conjugate(gamma, commutator(o1, o2)), commutator(o1, o2)))
    check("odd-odd anticommutator fixed", matrix_eq(conjugate(gamma, anticommutator(o1, o2)), anticommutator(o1, o2)))
    check("odd square is even", matrix_eq(conjugate(gamma, o1 * o1), o1 * o1))


if __name__ == "__main__":
    run()
