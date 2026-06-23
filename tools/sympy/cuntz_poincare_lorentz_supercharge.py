#!/usr/bin/env python3
"""Finite Cuntz/Poincare/Lorentz supercharge packet mirror."""

import sympy as sp


def pauli_matrix(E, px, py, pz):
    return sp.Matrix([[E + pz, px - sp.I * py], [px + sp.I * py, E - pz]])


def transport(Q, X):
    return Q * X * Q


def trace_readouts(M):
    s0 = sp.Matrix([[1, 0], [0, 1]])
    s1 = sp.Matrix([[0, 1], [1, 0]])
    s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    s3 = sp.Matrix([[1, 0], [0, -1]])
    return [sp.trace(s * M) / 4 for s in (s0, s1, s2, s3)]


def main():
    E, px, py, pz, q = sp.symbols("E px py pz q", complex=True)
    Qboost = sp.Matrix([[2, 1], [1, 1]])
    P = pauli_matrix(E, px, py, pz)
    mink = E**2 - px**2 - py**2 - pz**2
    super_anticommutator = 2 * P

    assert sp.simplify(P.det() - mink) == 0
    assert sp.simplify(super_anticommutator.det() - 4 * mink) == 0
    assert [sp.simplify(x) for x in trace_readouts(super_anticommutator)] == [E, px, py, pz]
    assert sp.simplify(transport(Qboost, P).det() - P.det()) == 0
    assert sp.simplify(transport(Qboost, transport(Qboost, P)).det() - mink) == 0
    assert sp.simplify((q * q + q * q) - 2 * q**2) == 0

    print("finite Cuntz/Poincare/Lorentz supercharge checks ok")


if __name__ == "__main__":
    main()
