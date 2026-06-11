#!/usr/bin/env python3
"""Finite Hodge/trifactor bridge verifier.

This mirrors `InfoGeometry.GrandUnification.HodgeTrifactorBridge`.
The script checks only finite polynomial/projector identities for a tripotent
operator `x^3 = x`; it does not model analytic Hodge theory or zeta zeros.
"""

from __future__ import annotations

import sympy as sp


x = sp.Symbol("x")
RELATION = x**3 - x

P_ZERO = 1 - x**2
P_PLUS = (x**2 + x) / 2
P_MINUS = (x**2 - x) / 2


def reduce_mod_tripotent(expr: sp.Expr) -> sp.Expr:
    poly = sp.Poly(sp.expand(expr), x, domain=sp.QQ)
    modulus = sp.Poly(RELATION, x, domain=sp.QQ)
    return sp.factor(sp.rem(poly, modulus).as_expr())


def assert_zero(name: str, expr: sp.Expr) -> None:
    remainder = reduce_mod_tripotent(expr)
    if remainder != 0:
        raise AssertionError(f"{name} failed: remainder {remainder}")
    print(f"  {name}: OK")


def verify_polynomial_bridge() -> None:
    print("Polynomial Hodge/trifactor identities modulo x^3 - x")
    assert_zero("harmonic + exact + coexact = 1", P_ZERO + P_PLUS + P_MINUS - 1)
    assert_zero("x harmonic = 0", x * P_ZERO)
    assert_zero("x exact = exact", x * P_PLUS - P_PLUS)
    assert_zero("x coexact = -coexact", x * P_MINUS + P_MINUS)


def verify_matrix_bridge() -> None:
    print("\nMatrix Hodge/trifactor identities")
    op = sp.diag(1, 0, -1)
    eye = sp.eye(3)
    zero = sp.zeros(3)
    p_zero = eye - op**2
    p_plus = (op**2 + op) / 2
    p_minus = (op**2 - op) / 2
    rho = sp.Matrix(sp.symbols("rho0:3"))

    checks = {
        "OP^3 = OP": op**3 - op,
        "sector sum recovers rho": p_zero * rho + p_plus * rho + p_minus * rho - rho,
        "OP harmonic = 0": op * p_zero * rho,
        "OP exact = exact": op * p_plus * rho - p_plus * rho,
        "OP coexact = -coexact": op * p_minus * rho + p_minus * rho,
        "active vanish implies harmonic equals rho": (p_plus * rho + p_minus * rho).subs(
            {rho[0]: 0, rho[2]: 0}
        ),
    }
    for name, expr in checks.items():
        if isinstance(expr, sp.MatrixBase):
            simplified = expr.applyfunc(sp.simplify)
            target = zero if simplified.shape == zero.shape else sp.zeros(*simplified.shape)
            if simplified != target:
                raise AssertionError(f"{name} failed:\n{simplified}")
        elif sp.simplify(expr) != 0:
            raise AssertionError(f"{name} failed: {expr}")
        print(f"  {name}: OK")


def verify_functorial_bridge() -> None:
    print("\nFunctorial sector preservation for a commuting linear map")
    op = sp.diag(1, 0, -1)
    eye = sp.eye(3)
    p_zero = eye - op**2
    p_plus = (op**2 + op) / 2
    p_minus = (op**2 - op) / 2

    f_plus, f_zero, f_minus = sp.symbols("f_plus f_zero f_minus")
    linear_map = sp.diag(f_plus, f_zero, f_minus)
    rho = sp.Matrix(sp.symbols("rho0:3"))

    checks = {
        "F commutes with OP": linear_map * op - op * linear_map,
        "F preserves harmonic": linear_map * p_zero * rho - p_zero * linear_map * rho,
        "F preserves exact": linear_map * p_plus * rho - p_plus * linear_map * rho,
        "F preserves coexact": linear_map * p_minus * rho - p_minus * linear_map * rho,
        "F preserves sector sum": linear_map * (p_zero + p_plus + p_minus) * rho
        - (p_zero + p_plus + p_minus) * linear_map * rho,
    }
    for name, expr in checks.items():
        simplified = expr.applyfunc(sp.simplify)
        if simplified != sp.zeros(*simplified.shape):
            raise AssertionError(f"{name} failed:\n{simplified}")
        print(f"  {name}: OK")


def verify_cuntz_tomita_chiral_anticommutation() -> None:
    """Check the finite two-sheet shadow of D = S_L + J S_L J.

    This is only the 2x2 algebraic atom: the left/right shifts are nilpotent
    matrix units, J swaps the two sheets, and Gamma is the sheet grading.
    """

    print("\nFinite Cuntz-Tomita chiral anticommutation")
    left_shift = sp.Matrix([[0, 0], [1, 0]])
    tomita_swap = sp.Matrix([[0, 1], [1, 0]])
    gamma = sp.Matrix([[1, 0], [0, -1]])
    p_plus = sp.Matrix([[1, 0], [0, 0]])
    p_minus = sp.Matrix([[0, 0], [0, 1]])
    right_shift = tomita_swap * left_shift * tomita_swap
    dirac_hodge = left_shift + right_shift
    zero = sp.zeros(2)

    checks = {
        "S_L^2 = 0": left_shift**2,
        "S_R^2 = 0": right_shift**2,
        "J^2 = I": tomita_swap**2 - sp.eye(2),
        "Gamma^2 = I": gamma**2 - sp.eye(2),
        "J S_L J = S_R": tomita_swap * left_shift * tomita_swap - right_shift,
        "D = S_L + J S_L J": dirac_hodge - (left_shift + tomita_swap * left_shift * tomita_swap),
        "{D, Gamma} = 0": dirac_hodge * gamma + gamma * dirac_hodge,
        "D Gamma D = -Gamma": dirac_hodge * gamma * dirac_hodge + gamma,
        "D P+ D = P-": dirac_hodge * p_plus * dirac_hodge - p_minus,
        "D P- D = P+": dirac_hodge * p_minus * dirac_hodge - p_plus,
        "D P+ = P- D": dirac_hodge * p_plus - p_minus * dirac_hodge,
        "D P- = P+ D": dirac_hodge * p_minus - p_plus * dirac_hodge,
    }
    for name, expr in checks.items():
        simplified = expr.applyfunc(sp.simplify)
        if simplified != zero:
            raise AssertionError(f"{name} failed:\n{simplified}")
        print(f"  {name}: OK")


def main() -> None:
    print("=" * 72)
    print("HODGE-TRIFACTOR BRIDGE: FINITE PROJECTOR CHECKS")
    print("=" * 72)
    verify_polynomial_bridge()
    verify_matrix_bridge()
    verify_functorial_bridge()
    verify_cuntz_tomita_chiral_anticommutation()
    print("\nAll finite Hodge/trifactor checks passed.")


if __name__ == "__main__":
    main()
