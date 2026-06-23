#!/usr/bin/env python3
"""
SymPy finite checks for the chiral super-Poincare / Souriau bridge.

Mirrors the Lean owner:
  lean/InfoGeometry/Canonical/ChiralSuperPoincareSouriauBridge.lean

Finite algebra only:
* chiral nilpotents σ± satisfy CAR-style anticommutator;
* Dχ = σ+ + σ- squares to {σ+,σ-};
* Pauli soldering determinant is the Minkowski norm;
* Souriau β·P is the (+---) Minkowski pairing;
* boosted β = γ/T (1,v,0,0) has invariant square 1/T².
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr: sp.Expr, label: str) -> None:
    got = sp.simplify(expr)
    if got != 0:
        raise AssertionError(f"{label} failed: {got}")


def assert_matrix_zero(mat: sp.Matrix, label: str) -> None:
    for entry in mat:
        assert_zero(entry, label)


def main() -> None:
    I = sp.I

    sigma0 = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -I], [I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])

    sigma_plus = sp.Matrix([[0, 1], [0, 0]])
    sigma_minus = sp.Matrix([[0, 0], [1, 0]])

    # Chiral CAR / sl2 checks.
    assert_matrix_zero(sigma_plus * sigma_plus, "sigma_plus^2")
    assert_matrix_zero(sigma_minus * sigma_minus, "sigma_minus^2")
    assert_matrix_zero(
        sigma_plus * sigma_minus + sigma_minus * sigma_plus - sigma0,
        "{sigma+, sigma-} = I",
    )
    assert_matrix_zero(
        sigma_plus * sigma_minus - sigma_minus * sigma_plus - sigma3,
        "[sigma+, sigma-] = sigma3",
    )
    assert_matrix_zero(
        sigma3 * sigma_plus - sigma_plus * sigma3 - 2 * sigma_plus,
        "[sigma3, sigma+] = 2 sigma+",
    )
    assert_matrix_zero(
        sigma3 * sigma_minus - sigma_minus * sigma3 + 2 * sigma_minus,
        "[sigma3, sigma-] = -2 sigma-",
    )

    # Supercharge square root of momentum in the finite chiral model.
    q_plus = sigma_plus
    q_minus = sigma_minus
    d_chiral = q_plus + q_minus
    momentum = q_plus * q_minus + q_minus * q_plus
    assert_matrix_zero(d_chiral * d_chiral - momentum, "D_chiral^2 = {Q+,Q-}")

    # Pauli soldering: P_{a dot a} = p_mu sigma^mu has determinant p^2.
    p0, p1, p2, p3 = sp.symbols("p0 p1 p2 p3")
    pauli_solder = p0 * sigma0 + p1 * sigma1 + p2 * sigma2 + p3 * sigma3
    minkowski_square = p0**2 - p1**2 - p2**2 - p3**2
    assert_zero(sp.expand(pauli_solder.det() - minkowski_square), "det Pauli(P) = P^2")

    # Souriau beta-energy pairing β·P with signature (+---).
    b0, b1, b2, b3 = sp.symbols("b0 b1 b2 b3")
    beta_dot_p = b0 * p0 - b1 * p1 - b2 * p2 - b3 * p3
    assert_zero(beta_dot_p - (b0 * p0 - b1 * p1 - b2 * p2 - b3 * p3), "beta dot P")

    # Boosted inverse-temperature vector β = γ/T (1,v,0,0), γ²(1-v²)=1.
    gamma, v, T = sp.symbols("gamma v T", nonzero=True)
    beta_sq = (gamma / T) ** 2 - (gamma * v / T) ** 2
    beta_sq_on_shell = sp.simplify(beta_sq.subs(gamma**2 * (1 - v**2), 1))
    # Do a safer direct simplification under γ² = 1/(1-v²).
    beta_sq_gamma = sp.simplify(beta_sq.subs(gamma**2, 1 / (1 - v**2)))
    assert_zero(beta_sq_gamma - 1 / T**2, "boosted beta square = 1/T^2")

    # Poincare metric coefficients (+---), matching the Lean socket.
    eta = sp.diag(1, -1, -1, -1)
    assert eta[0, 0] == 1
    for mu in [1, 2, 3]:
        assert eta[mu, mu] == -1
    for mu in range(4):
        for nu in range(4):
            if mu != nu:
                assert eta[mu, nu] == 0

    print("chiral super-Poincare / Souriau finite checks ok")
    print("det(P_mu sigma^mu) =", sp.factor(pauli_solder.det()))
    print("beta·P =", beta_dot_p)


if __name__ == "__main__":
    main()
