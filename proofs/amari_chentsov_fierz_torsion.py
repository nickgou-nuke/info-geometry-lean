#!/usr/bin/env python3
"""SymPy witness for Amari--Chentsov cubic skewness / Fierz-Jones torsion.

Checks:
  psi(eps)=g eps^2/2 + C eps^3/6
  psi''(0)=g   (Dikin/Fisher quadratic metric)
  psi'''(0)=C  (Amari--Chentsov cubic skewness)
  tau=C_R-C_L  (left-right torsion-like mismatch)
  Jones/Fierz torsion matrix [[0,tau],[-tau,0]] is traceless and antisymmetric.
"""

import sympy as sp


def main():
    eps = sp.symbols("eps", real=True)
    g, C = sp.symbols("g C", real=True)
    CL, CR = sp.symbols("C_L C_R", real=True)
    v0, v1 = sp.symbols("v0 v1", real=True)

    psi = g * eps**2 / 2 + C * eps**3 / 6
    dikin = g * eps**2 / 2
    tail = C * eps**3 / 6

    assert sp.simplify(psi - (dikin + tail)) == 0
    assert sp.diff(psi, eps, 2).subs(eps, 0) == g
    assert sp.diff(psi, eps, 3).subs(eps, 0) == C

    tau = CR - CL
    Jtau = sp.Matrix([[0, tau], [-tau, 0]])
    assert sp.trace(Jtau) == 0
    assert Jtau.T == -Jtau

    v = sp.Matrix([v0, v1])
    assert sp.simplify(Jtau * v - sp.Matrix([tau * v1, -tau * v0])) == sp.zeros(2, 1)

    print("amari_chentsov_fierz_torsion.py: finite witnesses passed")
    print("psi(eps) =")
    sp.pprint(psi)
    print("psi''(0) =", sp.diff(psi, eps, 2).subs(eps, 0), "  [Dikin metric]")
    print("psi'''(0) =", sp.diff(psi, eps, 3).subs(eps, 0), "  [Amari-Chentsov cubic]")
    print("tau = C_R - C_L =", tau)
    print("Jones/Fierz torsion matrix =")
    sp.pprint(Jtau)
    print("trace=0, transpose=-matrix, action=(tau*v1, -tau*v0)")
    print("Analytic Chentsov uniqueness / Poisson limit / Fierz derivation forms remain sockets.")


if __name__ == "__main__":
    main()
