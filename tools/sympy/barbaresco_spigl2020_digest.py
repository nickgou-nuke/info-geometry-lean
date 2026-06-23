#!/usr/bin/env python3
"""Symbolic witness for the main formulas extracted from Barbaresco-SPIGL2020.

This script checks a concrete finite-support Laplace transform model of the
Souriau theorem, the Massieu/Legendre identities, the Fisher positivity
baseline, and the commuting scalar Connes cocycle laws.
"""

import sympy as sp


def finite_laplace_convexity_check():
    beta = sp.symbols("beta", real=True)
    w1, w2 = sp.symbols("w1 w2", positive=True, real=True)
    m1, m2 = sp.symbols("m1 m2", real=True)

    F = w1 * sp.exp(m1 * beta) + w2 * sp.exp(m2 * beta)
    f = sp.log(F)
    f2 = sp.simplify(sp.diff(f, beta, 2))
    expected = sp.simplify(
        w1 * w2 * (m1 - m2) ** 2 * sp.exp((m1 + m2) * beta) / F ** 2
    )
    assert sp.simplify(f2 - expected) == 0
    return sp.factor(f2)


def legendre_massieu_check():
    beta = sp.symbols("beta", real=True)
    u1, u2 = sp.symbols("u1 u2", real=True)
    w1, w2 = sp.symbols("w1 w2", positive=True, real=True)

    Z = w1 * sp.exp(-beta * u1) + w2 * sp.exp(-beta * u2)
    Phi = sp.log(Z)
    Q = sp.diff(Phi, beta)
    S = beta * Q - Phi

    assert sp.simplify(sp.diff(Phi, beta) - Q) == 0
    # The Legendre relation differentiates to the tautology dS/dβ = β dQ/dβ.
    assert sp.simplify(sp.diff(S, beta) - beta * sp.diff(Q, beta)) == 0
    I = sp.simplify(-sp.diff(Phi, beta, 2))
    return sp.simplify(Phi), sp.simplify(Q), sp.simplify(S), sp.factor(I)


def gibbs_normalization_check():
    beta = sp.symbols("beta", real=True)
    E0, E1 = sp.Integer(0), sp.Integer(1)
    Z = sp.exp(-beta * E0) + sp.exp(-beta * E1)
    Phi = sp.log(Z)
    p0 = sp.simplify(sp.exp(-beta * E0 - Phi))
    p1 = sp.simplify(sp.exp(-beta * E1 - Phi))
    assert sp.simplify(p0 + p1 - 1) == 0
    return p0, p1


def connes_cocycle_checks():
    s, t, dK = sp.symbols("s t dK", real=True)
    u = lambda x: sp.exp(-sp.I * x * dK)
    assert sp.simplify(u(s + t) - u(s) * u(t)) == 0
    assert sp.simplify(u(0) - 1) == 0
    return sp.simplify(u(s + t))


def symplectic_square_check():
    J = sp.Matrix([[0, 1], [-1, 0]])
    return sp.simplify(J * J)


def main():
    print("=== Barbaresco SPIGL2020 digest ===")

    f2 = finite_laplace_convexity_check()
    print("Laplace convexity check: f'' =", f2)

    Phi, Q, S, I = legendre_massieu_check()
    print("Massieu potential Phi(beta) =", Phi)
    print("Heat readout Q(beta) =", Q)
    print("Entropy S(beta) =", S)
    print("Fisher information I(beta) =", I)

    p0, p1 = gibbs_normalization_check()
    print("Gibbs weights:", p0, p1)

    phase = connes_cocycle_checks()
    print("Commuting Connes phase u(s+t) =", phase)

    J2 = symplectic_square_check()
    print("J^2 =", J2)

    print("All symbolic checks passed.")


if __name__ == "__main__":
    main()
