#!/usr/bin/env python3
"""Exact SymPy witness for the finite squashing/Cayley/DKT pipeline."""

import sympy as sp


def dagger(A):
    return A.conjugate().T


def main():
    lam = sp.Symbol("lam", real=True, positive=True)
    I2 = sp.eye(2)
    T = sp.diag(lam, 2 * lam)
    T_reg = T - I2

    squash = sp.diag(sp.tanh(1 - 1 / lam), sp.tanh(1 - 1 / (2 * lam)))
    squash_limit = squash.applyfunc(lambda z: sp.limit(z, lam, sp.oo))

    cayley = (T - sp.I * I2) * (T + sp.I * I2).inv()
    assert sp.simplify(cayley * dagger(cayley) - I2) == sp.zeros(2)
    cayley_limit = cayley.applyfunc(lambda z: sp.limit(z, lam, sp.oo))

    eta = sp.diag(1, -1)
    nplus = sp.diag(1, 0)
    nminus = sp.diag(0, 1)
    assert eta == nplus - nminus
    assert eta * eta == I2

    x00, x01, x10, x11 = sp.symbols("x00 x01 x10 x11", complex=True)
    y00, y01, y10, y11 = sp.symbols("y00 y01 y10 y11", complex=True)
    X = sp.Matrix([[x00, x01], [x10, x11]])
    Y = sp.Matrix([[y00, y01], [y10, y11]])

    def dkt(A):
        return eta * dagger(A) * eta

    assert sp.simplify(dkt(dkt(X)) - X) == sp.zeros(2)
    assert sp.simplify(dkt(X * Y) - dkt(Y) * dkt(X)) == sp.zeros(2)
    assert sp.simplify(dkt(T) - T) == sp.zeros(2)
    assert sp.simplify(dkt(cayley) - dagger(cayley)) == sp.zeros(2)
    assert sp.simplify(cayley * dkt(cayley) - I2) == sp.zeros(2)

    print("spectral_squash_cayley_dkt.py: finite witnesses passed")
    print("T =")
    sp.pprint(T)
    print("T-I =")
    sp.pprint(T_reg)
    print("squash =")
    sp.pprint(squash)
    print("limit squash =")
    sp.pprint(squash_limit)
    print("Cayley(T) unitary: True")
    print("limit Cayley(T) =")
    sp.pprint(cayley_limit)
    print("eta = Nplus - Nminus and eta^2 = I")
    print("finite DKT/Krein adjoint X ↦ η X† η is an anti-involution")
    print("for the finite Cayley stage: U^DKT = U† and U U^DKT = I")
    print("Analytic C*-colimit / full Tomita J / inverse-Cayley boundary recovery remain sockets.")


if __name__ == "__main__":
    main()
