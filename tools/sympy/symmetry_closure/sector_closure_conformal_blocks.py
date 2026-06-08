#!/usr/bin/env python3
"""SymPy shadow for `SymmetryClosureConformalBlocks.lean`.

Lean owner:
  lean/InfoGeometry/Canonical/SymmetryClosureConformalBlocks.lean

Finite shadow:
  Block-diagonal operators preserve computational/noncomputational sectors.
  Their sums, differences, commutators, and anticommutators remain block
  diagonal, hence have no leakage between the two sectors.
"""

from __future__ import annotations

import sympy as sp

from common import (
    anticommutator,
    block_diag2,
    check,
    commutator,
    matrix2,
    matrix_eq,
    offdiag_blocks_zero,
)


def run() -> None:
    print("SymmetryClosureConformalBlocks finite shadow")
    Ac, An = matrix2("Ac"), matrix2("An")
    Bc, Bn = matrix2("Bc"), matrix2("Bn")
    A = block_diag2(Ac, An)
    B = block_diag2(Bc, Bn)

    x0, x1 = sp.symbols("x0 x1")
    computational_vector = sp.Matrix([x0, x1, 0, 0])
    image = A * computational_vector

    check("block action preserves computational sector", matrix_eq(image[2:4, :], sp.zeros(2, 1)))
    check("composition remains sector-preserving", offdiag_blocks_zero(A * B))
    check("sum remains sector-preserving", offdiag_blocks_zero(A + B))
    check("difference remains sector-preserving", offdiag_blocks_zero(A - B))
    check("commutator remains sector-preserving", offdiag_blocks_zero(commutator(A, B)))
    check("anticommutator remains sector-preserving", offdiag_blocks_zero(anticommutator(A, B)))


if __name__ == "__main__":
    run()
