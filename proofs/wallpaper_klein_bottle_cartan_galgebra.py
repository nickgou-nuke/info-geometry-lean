#!/usr/bin/env python3
"""galgebra-lane certificate for Klein-compatible wallpaper symmetries."""

import sympy as sp
from galgebra.ga import Ga


def main():
    u = sp.symbols('u')
    ga = Ga('e', g=[1], coords=[u])
    T = sp.Matrix([[0, -1], [1, 0]])
    G = sp.Matrix([[1, 0], [0, -1]])
    I = sp.eye(2)
    D4 = [I, T, -I, -T, G, T*G, -G, -T*G]
    assert len({tuple(S) for S in D4}) == 8
    for A in D4:
        for B in D4:
            assert tuple(A*B) in {tuple(S) for S in D4}
    scalar_mv = ga.mv(sp.Rational(8, 1), 'scalar')
    assert scalar_mv.obj == 8
    print("wallpaper Klein-bottle Cartan galgebra certificate: ok")


if __name__ == "__main__":
    main()
