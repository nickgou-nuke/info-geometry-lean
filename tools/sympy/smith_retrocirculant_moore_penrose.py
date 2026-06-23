#!/usr/bin/env python3
"""Exact-rational SymPy witnesses for Smith's retrocirculant Moore--Penrose inverse."""

import sympy as sp


def retro(a, b):
    return sp.Matrix([[0, b], [a, 0]])


def main():
    a, b = sp.symbols('a b', nonzero=True)
    A = retro(a, b)
    Ap = sp.Matrix([[0, 1/a], [1/b, 0]])
    assert sp.simplify(A * Ap * A - A) == sp.zeros(2)
    assert sp.simplify(Ap * A * Ap - Ap) == sp.zeros(2)
    assert sp.simplify((A * Ap).T - A * Ap) == sp.zeros(2)
    assert sp.simplify((Ap * A).T - Ap * A) == sp.zeros(2)

    A0 = retro(sp.Rational(2), sp.Rational(3))
    Ap0 = sp.Matrix([[0, sp.Rational(1, 2)], [sp.Rational(1, 3), 0]])
    assert A0 * Ap0 * A0 == A0
    eigA = sorted(A0.eigenvals().keys(), key=lambda z: str(z))
    eigAp = sorted(Ap0.eigenvals().keys(), key=lambda z: str(z))
    assert set(eigAp) == {sp.simplify(1/e) for e in eigA}

    B0 = retro(sp.Rational(5), sp.Rational(7))
    prod = A0 * B0
    assert prod[0, 1] == 0 and prod[1, 0] == 0  # circulant diagonal in n=2 model
    print("smith retrocirculant Moore-Penrose SymPy certificate: ok")


if __name__ == "__main__":
    main()
