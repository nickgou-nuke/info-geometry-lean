#!/usr/bin/env python3
"""SymPy witness for scalar KAN factorization of the centered Dirichlet mode.

This mirrors `InfoGeometry.Arithmetic.ZetaKANDirichletFactorization`.

The scalar zeta summand sees:

    K = exp(-I v L)      compact phase
    A = exp(-u L)        abelian scale
    N = 1                trivial scalar character

The genuine parabolic KAN matrix `N(eta) = [[1, eta], [0, 1]]` is checked
separately as the unipotent owner lane.
"""

from __future__ import annotations

import sympy as sp


u, v, L, eta, theta = sp.symbols("u v L eta theta", real=True)


def critical_line_weight(log_weight: sp.Expr) -> sp.Expr:
    return sp.exp(-sp.Rational(1, 2) * log_weight)


def scalar_k_character(log_weight: sp.Expr, height: sp.Expr) -> sp.Expr:
    return sp.exp(-sp.I * height * log_weight)


def scalar_a_character(log_weight: sp.Expr, normal: sp.Expr) -> sp.Expr:
    return sp.exp(-normal * log_weight)


def scalar_n_character(_shear: sp.Expr) -> sp.Expr:
    return sp.Integer(1)


def centered_dirichlet_mode(log_weight: sp.Expr, normal: sp.Expr, height: sp.Expr) -> sp.Expr:
    return sp.exp(-log_weight / 2) * sp.exp(-normal * log_weight) * sp.exp(
        -sp.I * height * log_weight
    )


def scalar_kan_dirichlet_product(
    log_weight: sp.Expr, normal: sp.Expr, height: sp.Expr, shear: sp.Expr
) -> sp.Expr:
    return (
        critical_line_weight(log_weight)
        * scalar_k_character(log_weight, height)
        * scalar_a_character(log_weight, normal)
        * scalar_n_character(shear)
    )


def component_n(shear: sp.Expr) -> sp.Matrix:
    return sp.Matrix([[1, shear], [0, 1]])


def main() -> None:
    mode = centered_dirichlet_mode(L, u, v)
    kan_mode = scalar_kan_dirichlet_product(L, u, v, eta)

    assert sp.simplify(mode - kan_mode) == 0
    assert sp.simplify(scalar_a_character(L, 0) - 1) == 0
    assert sp.simplify(scalar_k_character(L, 0) - 1) == 0
    assert sp.simplify(scalar_n_character(eta) - 1) == 0
    assert sp.simplify(scalar_kan_dirichlet_product(L, 0, v, eta) - sp.exp(-L / 2) * sp.exp(-sp.I * v * L)) == 0

    n_eta = component_n(eta)
    n_theta = component_n(theta)
    assert n_eta.det() == 1
    assert component_n(0) == sp.eye(2)
    assert sp.simplify(n_eta * n_theta - component_n(eta + theta)) == sp.zeros(2)

    weights = sp.symbols("L0:4", real=True)
    finite_dirichlet = sum(centered_dirichlet_mode(weight, u, v) for weight in weights)
    finite_kan = sum(scalar_kan_dirichlet_product(weight, u, v, eta) for weight in weights)
    assert sp.simplify(finite_dirichlet - finite_kan) == 0

    finite_euler = sp.prod(1 / (1 - centered_dirichlet_mode(weight, u, v)) for weight in weights)
    finite_euler_kan = sp.prod(
        1 / (1 - scalar_kan_dirichlet_product(weight, u, v, eta)) for weight in weights
    )
    assert sp.simplify(finite_euler - finite_euler_kan) == 0

    print("zeta_kan_dirichlet_factorization: ok")
    print("  K character: exp(-I v L)")
    print("  A character: exp(-u L)")
    print("  N scalar character: 1")
    print("  mode: exp(-L/2) * K * A * N")
    print("  critical line: A=1, leaving half-density times K")
    print("  matrix N owner lane: [[1, eta], [0, 1]], det=1, additive shear")
    print("  finite Dirichlet/Euler readouts factor through scalar KAN characters")


if __name__ == "__main__":
    main()
