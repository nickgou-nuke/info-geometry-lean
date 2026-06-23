#!/usr/bin/env python3
"""Clifford-lane audit for finite holographic Cuntz shard algebra."""

import sympy as sp
from clifford import Cl


def main():
    layout, blades = Cl(1, 0)
    e1 = blades["e1"]
    one = layout.scalar

    # Clifford idempotent: algebraic aperture half-space.
    p_plus = (one + e1) / 2
    assert (p_plus * p_plus - p_plus).grades() == set()
    assert abs(float((p_plus * p_plus - p_plus).value[0])) < 1e-12

    # Exact-rational matrix shard checked in the same lane.
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

    print("holographic Cuntz shard clifford audit: ok")


if __name__ == "__main__":
    main()
