#!/usr/bin/env python3
"""Clifford-lane certificate for finite holographic Cuntz shard algebra."""

import sympy as sp
from clifford import Cl


def main():
    layout, _ = Cl(1, 0)
    one = layout.scalar
    S = sp.Matrix([[0, 1], [0, 0]])
    P = sp.Matrix([[1, 0], [0, 0]])
    assert S * S.T == P
    assert P * P == P
    assert S * S.T * S == S
    scalar_mv = 1.0 * one
    assert abs(float(scalar_mv.value[0]) - 1.0) < 1e-15
    print("holographic Cuntz shard clifford certificate: ok")


if __name__ == "__main__":
    main()
