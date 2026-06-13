#!/usr/bin/env python3
"""Audit the proposed split-octonion Peirce R-matrix ansatz.

This is intentionally a guard, not a theorem witness.  It tests the displayed
ansatz

    R_ij(q) = q e+⊗e+ + q^-1 e-⊗e- + up_i⊗down_j + up_j⊗down_i

under the natural finite left-multiplication matrices of the concrete Zorn
split-octonion table.  For i=0, j=1, q=2, the adjacent Yang-Baxter residual is
nonzero.  That blocks the stronger claim that Peirce nilpotency alone certifies
an R-matrix/Yang-Baxter solution.

Lean companion obstruction:
    SplitOctonionPeirceYangBaxterBridge.peirceWitt_nonassociative_obstruction
"""

from __future__ import annotations

import sympy as sp


Vector = sp.MutableDenseMatrix


def mul_z(x: Vector, y: Vector) -> Vector:
    """Concrete Zorn split-octonion multiplication over integers."""
    a, b, x0, x1, x2, y0, y1, y2 = x
    c, d, u0, u1, u2, v0, v1, v2 = y
    return sp.Matrix(
        [
            a * c + x0 * v0 + x1 * v1 + x2 * v2,
            b * d + y0 * u0 + y1 * u1 + y2 * u2,
            a * u0 + d * x0 - (y1 * v2 - y2 * v1),
            a * u1 + d * x1 - (y2 * v0 - y0 * v2),
            a * u2 + d * x2 - (y0 * v1 - y1 * v0),
            b * v0 + c * y0 + (x1 * u2 - x2 * u1),
            b * v1 + c * y1 + (x2 * u0 - x0 * u2),
            b * v2 + c * y2 + (x0 * u1 - x1 * u0),
        ]
    )


def basis_vector(index: int) -> Vector:
    return sp.Matrix([1 if row == index else 0 for row in range(8)])


def left_multiplication_matrix(x: Vector) -> sp.Matrix:
    basis = [basis_vector(index) for index in range(8)]
    return sp.Matrix.hstack(*(mul_z(x, basis_element) for basis_element in basis))


def nonzero_entries(matrix: sp.Matrix) -> list[tuple[int, int, sp.Expr]]:
    return [
        (row, col, sp.simplify(matrix[row, col]))
        for row in range(matrix.rows)
        for col in range(matrix.cols)
        if sp.simplify(matrix[row, col]) != 0
    ]


def verify_ansatz_is_not_ybe_solution() -> None:
    e_plus = basis_vector(0)
    e_minus = basis_vector(1)
    up = [basis_vector(2), basis_vector(3), basis_vector(4)]
    down = [basis_vector(5), basis_vector(6), basis_vector(7)]

    q = sp.Rational(2)
    left = left_multiplication_matrix
    r_ansatz = (
        q * sp.kronecker_product(left(e_plus), left(e_plus))
        + q**-1 * sp.kronecker_product(left(e_minus), left(e_minus))
        + sp.kronecker_product(left(up[0]), left(down[1]))
        + sp.kronecker_product(left(up[1]), left(down[0]))
    )

    identity = sp.eye(8)
    r12 = sp.kronecker_product(r_ansatz, identity)
    r23 = sp.kronecker_product(identity, r_ansatz)
    residual = r12 * r23 * r12 - r23 * r12 * r23
    entries = nonzero_entries(residual)

    assert entries, "unexpected: proposed R ansatz satisfied this finite YBE audit"
    assert len(entries) == 576
    assert entries[0] == (1, 367, 1)

    print("SPLIT_OCTONION_RMATRIX_ANSATZ_AUDIT_OBSTRUCTION_OK")
    print("residual_nonzero_entries=576")
    print("first_nonzero_entry=(1, 367, 1)")
    print("scope=blocks Peirce-nilpotency-alone R-matrix/Yang-Baxter certification")


if __name__ == "__main__":
    verify_ansatz_is_not_ybe_solution()
