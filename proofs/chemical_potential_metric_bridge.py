#!/usr/bin/env python3
"""Symbolic audit for chemical potential -> Pauli metric/g00 bridge."""

import sympy as sp

E, px, py, pz, dmu, lam, mu, mu0 = sp.symbols("E px py pz dmu lambda mu mu0")
i = sp.I


def pauli(Ev, pxv, pyv, pzv):
    return sp.Matrix([[Ev + pzv, pxv - i * pyv], [pxv + i * pyv, Ev - pzv]])


def main():
    X_shift = pauli(E - dmu, px, py, pz)
    shifted_q = (E - dmu) ** 2 - px**2 - py**2 - pz**2
    assert sp.simplify(X_shift.det() - shifted_q) == 0

    X_scaled = pauli(lam * E, px, py, pz)
    g00 = lam**2
    scaled_q = g00 * E**2 - px**2 - py**2 - pz**2
    assert sp.simplify(X_scaled.det() - scaled_q) == 0

    # Tolman/Ehrenfest-style algebraic socket: lambda * mu = mu0,
    # so if solved formally lambda = mu0/mu, then g00 = (mu0/mu)^2.
    g00_mu = (mu0 / mu) ** 2
    assert sp.simplify(g00_mu - (mu0**2 / mu**2)) == 0

    # First-order additive perturbation of the determinant under E -> E-dmu.
    delta_q = sp.expand(shifted_q - (E**2 - px**2 - py**2 - pz**2))

    print("shifted determinant:", sp.factor(X_shift.det()))
    print("expected shifted quadric:", sp.factor(shifted_q))
    print("time-scaled determinant:", sp.factor(X_scaled.det()))
    print("effective g00:", g00)
    print("Tolman-style socket g00=(mu0/mu)^2:", g00_mu)
    print("additive determinant perturbation Δq:", sp.factor(delta_q))
    print("chemical_potential_metric_bridge.py: finite audit passed")


if __name__ == "__main__":
    main()
