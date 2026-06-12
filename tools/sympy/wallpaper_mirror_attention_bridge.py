#!/usr/bin/env python3
"""SymPy twin for the wallpaper-to-Mirror Phase attention bridge.

This mirrors `InfoGeometry.LLM.WallpaperMirrorAttentionBridge`.

Checked here:
- the concrete `pg` glide inverts transverse translation;
- orientation reversal is invisible modulo two;
- exact dyadic Mirror Phase attention kills the real branch anomaly.

Not checked here:
- trained transformer behavior;
- semantic reliability;
- quotient-manifold or physical band-structure classification.
"""

from __future__ import annotations

import sympy as sp


def mod2(x: int) -> int:
    return x % 2


def main() -> None:
    print("--- SymPy Twin: Wallpaper pg -> Mirror Attention Bridge ---")

    x, y = sp.symbols("x y", real=True)
    left, right = sp.symbols("left right")

    def ty(point: sp.Matrix) -> sp.Matrix:
        return sp.Matrix([point[0], point[1] + 1])

    def ty_inv(point: sp.Matrix) -> sp.Matrix:
        return sp.Matrix([point[0], point[1] - 1])

    def glide(point: sp.Matrix) -> sp.Matrix:
        return sp.Matrix([point[0] + sp.Rational(1, 2), -point[1]])

    p = sp.Matrix([x, y])
    assert sp.simplify(glide(ty(p)) - ty_inv(glide(p))) == sp.zeros(2, 1)
    print("pg glide relation G*T_y = T_y^-1*G: OK")

    for charge in [-9, -2, -1, 0, 1, 6, 11]:
        assert mod2(-charge) == mod2(charge)
    print("charge orientation reversal is invisible in Z2: OK")

    M = sp.Matrix(
        [
            [sp.Rational(1, 2), sp.Rational(1, 2)],
            [sp.Rational(1, 2), sp.Rational(1, 2)],
        ]
    )
    v = sp.Matrix([left, right])
    projected = sp.simplify(M * v)
    anomaly = sp.simplify(projected[1] - projected[0])

    assert sp.simplify(M * M - M) == sp.zeros(2)
    assert anomaly == 0
    print("dyadic Mirror attention is idempotent and kills branch anomaly: OK")

    print("[SUCCESS] finite wallpaper glide and Mirror attention bridge verified.")


if __name__ == "__main__":
    main()
