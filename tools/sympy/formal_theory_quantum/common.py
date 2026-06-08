#!/usr/bin/env python3
"""Common SymPy helpers for `formal-theory-quantum.lean` companions.

These scripts are computational shadows for chapter stubs.  They do not certify
Lean declarations and must not be treated as replacements for theorem-owned
Lean proofs.
"""

from __future__ import annotations

import sympy as sp


def mat_eq(left: sp.MatrixBase, right: sp.MatrixBase) -> bool:
    diff = sp.Matrix(left) - sp.Matrix(right)
    diff = diff.applyfunc(sp.simplify)
    return diff == sp.zeros(diff.rows, diff.cols)


def scalar_eq(left, right=0) -> bool:
    return sp.simplify(left - right) == 0


def check(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)
    print(f"  {name}: OK")


def kron(left: sp.MatrixBase, right: sp.MatrixBase) -> sp.Matrix:
    return sp.kronecker_product(left, right)


def swap_2_tensor() -> sp.Matrix:
    return sp.Matrix(
        [
            [1, 0, 0, 0],
            [0, 0, 1, 0],
            [0, 1, 0, 0],
            [0, 0, 0, 1],
        ]
    )


def fundamental_uqsl2(q) -> tuple[sp.Matrix, sp.Matrix, sp.Matrix, sp.Matrix]:
    E = sp.Matrix([[0, 1], [0, 0]])
    F = sp.Matrix([[0, 0], [1, 0]])
    K = sp.diag(q, q**-1)
    return E, F, K, K.inv()


def universal_R_fundamental(q) -> sp.Matrix:
    return sp.Matrix(
        [
            [q, 0, 0, 0],
            [0, 1, 0, 0],
            [0, q - q**-1, 1, 0],
            [0, 0, 0, q],
        ]
    )


def braid_Rcheck_fundamental(q) -> sp.Matrix:
    return swap_2_tensor() * universal_R_fundamental(q)


def fibonacci_groebner():
    q, a, s = sp.symbols("q a s")
    relations = [q**4 - q**3 + q**2 - q + 1, a - (q**2 - q**3), s**2 - a]
    return q, a, s, sp.groebner(relations, q, a, s, order="lex")


def reduce_mod_fibonacci(expr, gb) -> sp.Expr:
    return sp.factor(gb.reduce(sp.expand(expr))[1])


def matrix_zero_mod_fibonacci(matrix: sp.MatrixBase, gb) -> bool:
    return all(reduce_mod_fibonacci(entry, gb) == 0 for entry in sp.Matrix(matrix))
