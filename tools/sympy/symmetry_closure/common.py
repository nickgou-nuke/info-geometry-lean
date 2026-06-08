#!/usr/bin/env python3
"""Shared helpers for finite SymPy shadows of Lean symmetry-closure files.

These helpers intentionally check finite matrix/scalar shadows only.  Lean
source remains the proof authority for the universal theorem statements.
"""

from __future__ import annotations

import sympy as sp


def simplify_matrix(matrix: sp.MatrixBase) -> sp.Matrix:
    return sp.Matrix(matrix).applyfunc(sp.simplify)


def matrix_eq(left: sp.MatrixBase, right: sp.MatrixBase) -> bool:
    diff = simplify_matrix(sp.Matrix(left) - sp.Matrix(right))
    return diff == sp.zeros(diff.rows, diff.cols)


def scalar_eq(left, right=0) -> bool:
    return sp.simplify(left - right) == 0


def check(name: str, condition: bool) -> bool:
    if not condition:
        raise AssertionError(name)
    print(f"  {name}: OK")
    return True


def matrix2(prefix: str) -> sp.Matrix:
    a00, a01, a10, a11 = sp.symbols(f"{prefix}00 {prefix}01 {prefix}10 {prefix}11")
    return sp.Matrix([[a00, a01], [a10, a11]])


def block_diag2(left: sp.MatrixBase, right: sp.MatrixBase) -> sp.Matrix:
    return sp.diag(sp.Matrix(left), sp.Matrix(right))


def commutator(left: sp.MatrixBase, right: sp.MatrixBase) -> sp.Matrix:
    return sp.Matrix(left) * sp.Matrix(right) - sp.Matrix(right) * sp.Matrix(left)


def anticommutator(left: sp.MatrixBase, right: sp.MatrixBase) -> sp.Matrix:
    return sp.Matrix(left) * sp.Matrix(right) + sp.Matrix(right) * sp.Matrix(left)


def offdiag_blocks_zero(matrix: sp.MatrixBase) -> bool:
    matrix = sp.Matrix(matrix)
    top_right = matrix[:2, 2:4]
    bottom_left = matrix[2:4, :2]
    return matrix_eq(top_right, sp.zeros(2)) and matrix_eq(bottom_left, sp.zeros(2))
