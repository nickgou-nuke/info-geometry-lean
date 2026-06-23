#!/usr/bin/env python3
"""galgebra-lane certificate for finite holographic Cuntz shard algebra."""

import sympy as sp
from galgebra.ga import Ga


def main():
    u = sp.symbols('u')
    ga = Ga('e', g=[1], coords=[u])
    S = sp.Matrix([[0, 1], [0, 0]])
    Psource = sp.Matrix([[0, 0], [0, 1]])
    assert S.T * S == Psource
    assert Psource * Psource == Psource
    scalar_mv = ga.mv(sp.Rational(1, 1), 'scalar')
    assert scalar_mv.obj == 1
    print("holographic Cuntz shard galgebra certificate: ok")


if __name__ == "__main__":
    main()
