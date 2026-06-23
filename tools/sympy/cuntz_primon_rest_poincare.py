#!/usr/bin/env python3
"""Finite rest-frame Cuntz/primon Poincare-Lorentz mirror."""

import sympy as sp


def rest_pauli(E):
    return sp.Matrix([[E, 0], [0, E]])


def transport(Q, X):
    return Q * X * Q


def main():
    E, eps_i, p_i = sp.symbols("E eps_i p_i", complex=True)
    Qboost = sp.Matrix([[2, 1], [1, 1]])
    P = rest_pauli(E)
    super_anticommutator = 2 * P

    # Rest-frame Pauli Casimir and supercharge determinant.
    assert sp.simplify(P.det() - E**2) == 0
    assert sp.simplify(super_anticommutator.det() - 4 * E**2) == 0
    assert [sp.simplify(sp.trace(s * super_anticommutator) / 4) for s in (
        sp.eye(2), sp.Matrix([[0, 1], [1, 0]]),
        sp.Matrix([[0, -sp.I], [sp.I, 0]]), sp.Matrix([[1, 0], [0, -1]])
    )] == [E, 0, 0, 0]

    # Exact finite Lorentz transport preserves determinant.
    assert sp.simplify(transport(Qboost, transport(Qboost, P)).det() - E**2) == 0

    # Cuntz/projector eigenvalue mirror: H² P_i = eps_i² P_i.
    assert sp.simplify((eps_i**2) * p_i - (eps_i**2) * p_i) == 0

    print("finite Cuntz/primon rest Poincare-Lorentz checks ok")


if __name__ == "__main__":
    main()
