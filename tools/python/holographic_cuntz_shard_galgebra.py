#!/usr/bin/env python3
"""GAlgebra-lane audit for finite holographic Cuntz shard algebra."""

from galgebra.ga import Ga
import sympy as sp


def main():
    ga = Ga("e1 e2", g=[1, 1])
    one = ga.mv(sp.Rational(1), "scalar")
    e1 = ga.mv_basis[0]

    p_plus = (one + e1) / 2
    assert str((p_plus * p_plus - p_plus).simplify()) == "0"

    S = sp.Matrix([[0, 1], [0, 0]])
    T = sp.Matrix([[0, 0], [1, 0]])
    P_source = sp.Matrix([[0, 0], [0, 1]])
    P_aperture = sp.Matrix([[1, 0], [0, 0]])
    assert S.T * S == P_source
    assert S * S.T == P_aperture
    assert P_source * P_source == P_source
    assert P_aperture * P_aperture == P_aperture
    assert S * S.T * S == S
    assert S.T * S + T.T * T == sp.eye(2)

    print("holographic Cuntz shard galgebra audit: ok")


if __name__ == "__main__":
    main()
