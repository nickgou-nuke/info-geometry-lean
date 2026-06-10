#!/usr/bin/env python3
"""Section 10: spinorial curvature antisymmetry.

Exact SymPy companion to ``lean/InfoGeometry/Section10.lean``.
"""

from __future__ import annotations

import sympy as sp


def assert_matrix_zero(name: str, matrix: sp.Matrix) -> None:
    diff = matrix.applyfunc(sp.simplify)
    if diff != sp.zeros(*diff.shape):
        raise AssertionError(f"{name} failed:\n{diff}")
    print(f"  {name}: OK")


def commutator(A: sp.Matrix, B: sp.Matrix) -> sp.Matrix:
    return A * B - B * A


def spinorial_curvature(
    d_mu_omega_nu: sp.Matrix,
    d_nu_omega_mu: sp.Matrix,
    omega_mu: sp.Matrix,
    omega_nu: sp.Matrix,
) -> sp.Matrix:
    return d_mu_omega_nu - d_nu_omega_mu + commutator(omega_mu, omega_nu)


def main() -> int:
    print("=" * 72)
    print("SECTION 10: SPINORIAL CURVATURE ANTISYMMETRY")
    print("=" * 72)

    a = sp.symbols("a0:4")
    b = sp.symbols("b0:4")
    c = sp.symbols("c0:4")
    d = sp.symbols("d0:4")
    d_mu_omega_nu = sp.Matrix(2, 2, a)
    d_nu_omega_mu = sp.Matrix(2, 2, b)
    omega_mu = sp.Matrix(2, 2, c)
    omega_nu = sp.Matrix(2, 2, d)

    f_mu_nu = spinorial_curvature(d_mu_omega_nu, d_nu_omega_mu, omega_mu, omega_nu)
    f_nu_mu = spinorial_curvature(d_nu_omega_mu, d_mu_omega_nu, omega_nu, omega_mu)
    assert_matrix_zero("F_mu_nu + F_nu_mu = 0", f_mu_nu + f_nu_mu)

    print("\nSECTION 10 VERIFIED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

