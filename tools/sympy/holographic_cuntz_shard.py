#!/usr/bin/env python3
"""Exact-rational SymPy audit for finite holographic Cuntz shard algebra."""

import sympy as sp


def main():
    print("=== Holographic Cuntz shard SymPy audit ===")

    S = sp.Matrix([[0, 1], [0, 0]])
    T = sp.Matrix([[0, 0], [1, 0]])
    P_source = sp.Matrix([[0, 0], [0, 1]])
    P_complement_source = sp.Matrix([[1, 0], [0, 0]])
    P_aperture = sp.Matrix([[1, 0], [0, 0]])
    I2 = sp.eye(2)
    x1, x2 = sp.symbols('x1 x2')
    x = sp.Matrix([x1, x2])

    assert S.T * S == P_source
    assert S * S.T == P_aperture
    assert T.T * T == P_complement_source
    assert S.T * (S * x) == P_source * x
    assert P_source * P_source == P_source
    assert P_aperture * P_aperture == P_aperture
    assert P_source + P_complement_source == I2
    assert P_aperture != I2
    assert S * S.T * S == S
    assert S.T * S * S.T == S.T

    # Two-shard finite analogue: source sectors partition a 2D signal.
    assert S.T * S + T.T * T == I2
    print("HOLOGRAPHIC_CUNTZ_SHARD_SYMPY_AUDIT_OK")


if __name__ == "__main__":
    main()
