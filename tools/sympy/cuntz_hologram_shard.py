#!/usr/bin/env python3
"""
Exact-rational certificate for the finite Cuntz hologram shard picture.

We use two exact branch isometries S_left, S_right : Q^2 -> Q^4 with orthogonal
ranges. Their adjoints recover the whole input on each branch, and their range
projections sum to the identity on Q^4.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    print("=== CUNTZ HOLOGRAM SHARD SYMPY CERTIFICATE ===")

    S_left = sp.Matrix([
        [1, 0],
        [0, 1],
        [0, 0],
        [0, 0],
    ])
    S_right = sp.Matrix([
        [0, 0],
        [0, 0],
        [1, 0],
        [0, 1],
    ])
    I2 = sp.eye(2)
    I4 = sp.eye(4)

    assert S_left.T * S_left == I2
    assert S_right.T * S_right == I2
    assert S_left.T * S_right == sp.zeros(2, 2)
    assert S_right.T * S_left == sp.zeros(2, 2)
    print("PASS: branch isometries and orthogonality")

    P_left = S_left * S_left.T
    P_right = S_right * S_right.T
    assert P_left + P_right == I4
    print("PASS: branch range projections sum to identity")

    x0, x1 = sp.symbols('x0 x1', rational=True)
    X = sp.Matrix([x0, x1])
    assert sp.simplify(S_left.T * (S_left * X) - X) == sp.zeros(2, 1)
    assert sp.simplify(S_right.T * (S_right * X) - X) == sp.zeros(2, 1)
    print("PASS: each branch recovers the whole input via its adjoint")

    print("CUNTZ_HOLOGRAM_SHARD_SYMPY_OK")


if __name__ == '__main__':
    main()
