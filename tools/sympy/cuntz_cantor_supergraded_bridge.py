#!/usr/bin/env python3
"""SymPy twin for `InfoGeometry.Algebra.CuntzCantorSupergradedBridge`.

Checked here:
- one binary Cuntz/Cantor branch step is odd by length parity mod 2;
- two one-bit branch steps compose to an even word;
- the finite wallpaper matrix anticommutator satisfies `{Q,Q} = 2P_x`.

Not checked here:
- a Hilbert-space Cuntz representation;
- physical supersymmetry;
- super-Poincare covariance.
"""

from __future__ import annotations

import sympy as sp


def parity_z2(word: list[bool]) -> int:
    return len(word) % 2


def main() -> None:
    print("--- SymPy Twin: Cuntz-Cantor Supergraded Bridge ---")

    odd_left = [False]
    odd_right = [True]
    two_step = odd_left + odd_right

    assert parity_z2(odd_left) == 1
    assert parity_z2(odd_right) == 1
    assert parity_z2(two_step) == 0
    print("binary word parity: odd + odd = even: OK")

    Q = sp.Matrix(
        [
            [1, 0, sp.Rational(1, 2)],
            [0, -1, 0],
            [0, 0, 1],
        ]
    )
    P_x = sp.Matrix(
        [
            [1, 0, 1],
            [0, 1, 0],
            [0, 0, 1],
        ]
    )

    anticommutator = Q * Q + Q * Q
    assert anticommutator == 2 * P_x
    print("finite matrix self-anticommutator {Q,Q} = 2P_x: OK")

    print("[SUCCESS] finite Cuntz-Cantor supergraded bridge verified.")


if __name__ == "__main__":
    main()
