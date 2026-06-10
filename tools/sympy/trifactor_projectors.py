#!/usr/bin/env python3
"""Trifactor projectors for an operator satisfying OP^3 = OP.

This is the SymPy companion to
`InfoGeometry.Canonical.TrifactorDecomposition`.

The Lean theorem is finite polynomial algebra.  This script mirrors that
workflow: it reduces every projector identity modulo the relation
`x^3 - x`, then checks representative matrices with eigenvalues in
`{-1, 0, 1}`.
"""

from __future__ import annotations

import sympy as sp


x = sp.Symbol("x")
TRIPOTENT_RELATION = x**3 - x

P_ZERO = 1 - x**2
P_PLUS = (x**2 + x) / 2
P_MINUS = (x**2 - x) / 2


def reduce_mod_tripotent(expr: sp.Expr) -> sp.Expr:
    """Reduce a polynomial expression modulo x^3 - x."""
    poly = sp.Poly(sp.expand(expr), x, domain=sp.QQ)
    modulus = sp.Poly(TRIPOTENT_RELATION, x, domain=sp.QQ)
    return sp.factor(sp.rem(poly, modulus).as_expr())


def assert_reduces_to_zero(name: str, expr: sp.Expr) -> None:
    remainder = reduce_mod_tripotent(expr)
    if remainder != 0:
        raise AssertionError(f"{name} failed: remainder {remainder}")
    print(f"  {name}: OK")


def matrix_projectors(op: sp.Matrix) -> tuple[sp.Matrix, sp.Matrix, sp.Matrix]:
    op2 = op * op
    eye = sp.eye(op.rows)
    return eye - op2, (op2 + op) / 2, (op2 - op) / 2


def assert_matrix_eq(name: str, lhs: sp.Matrix, rhs: sp.Matrix) -> None:
    diff = (lhs - rhs).applyfunc(sp.simplify)
    if diff != sp.zeros(*diff.shape):
        raise AssertionError(f"{name} failed:\n{diff}")
    print(f"  {name}: OK")


def verify_polynomial_identities() -> None:
    print("Polynomial reduction modulo x^3 - x")
    print(f"  factor(x^3 - x) = {sp.factor(TRIPOTENT_RELATION)}")

    assert_reduces_to_zero("P0^2 = P0", P_ZERO**2 - P_ZERO)
    assert_reduces_to_zero("P+^2 = P+", P_PLUS**2 - P_PLUS)
    assert_reduces_to_zero("P-^2 = P-", P_MINUS**2 - P_MINUS)

    assert_reduces_to_zero("P+ P- = 0", P_PLUS * P_MINUS)
    assert_reduces_to_zero("P0 P+ = 0", P_ZERO * P_PLUS)
    assert_reduces_to_zero("P0 P- = 0", P_ZERO * P_MINUS)

    assert_reduces_to_zero("P0 + P+ + P- = 1", P_ZERO + P_PLUS + P_MINUS - 1)
    assert_reduces_to_zero("x P0 = 0", x * P_ZERO)
    assert_reduces_to_zero("x P+ = P+", x * P_PLUS - P_PLUS)
    assert_reduces_to_zero("x P- = -P-", x * P_MINUS + P_MINUS)
    assert_reduces_to_zero("x = P+ - P-", x - (P_PLUS - P_MINUS))


def verify_matrix_example(name: str, op: sp.Matrix) -> None:
    print(f"\nMatrix example: {name}")
    zero = sp.zeros(op.rows)
    eye = sp.eye(op.rows)
    p_zero, p_plus, p_minus = matrix_projectors(op)

    assert_matrix_eq("OP^3 = OP", op**3, op)
    assert_matrix_eq("P0^2 = P0", p_zero * p_zero, p_zero)
    assert_matrix_eq("P+^2 = P+", p_plus * p_plus, p_plus)
    assert_matrix_eq("P-^2 = P-", p_minus * p_minus, p_minus)

    assert_matrix_eq("P+ P- = 0", p_plus * p_minus, zero)
    assert_matrix_eq("P0 P+ = 0", p_zero * p_plus, zero)
    assert_matrix_eq("P0 P- = 0", p_zero * p_minus, zero)

    assert_matrix_eq("P0 + P+ + P- = I", p_zero + p_plus + p_minus, eye)
    assert_matrix_eq("OP P0 = 0", op * p_zero, zero)
    assert_matrix_eq("OP P+ = P+", op * p_plus, p_plus)
    assert_matrix_eq("OP P- = -P-", op * p_minus, -p_minus)
    assert_matrix_eq("OP = P+ - P-", op, p_plus - p_minus)


def main() -> None:
    print("=" * 72)
    print("TRIFACTOR PROJECTORS: OP^3 = OP")
    print("=" * 72)

    verify_polynomial_identities()
    verify_matrix_example("diag(+1, 0, -1)", sp.diag(1, 0, -1))
    verify_matrix_example("projector diag(+1, 0)", sp.diag(1, 0))
    verify_matrix_example("mirror diag(+1, -1)", sp.diag(1, -1))

    print("\nAll trifactor projector checks passed.")


if __name__ == "__main__":
    main()
