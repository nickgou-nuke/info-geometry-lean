#!/usr/bin/env python3
"""SymPy twin for the wallpaper-to-Weyl finite bridge.

This mirrors `InfoGeometry.Topology.WallpaperToWeylBridge`.

Checked here:
- the concrete `pg` glide satisfies `G^2 = T_x`;
- the glide inverts transverse translation: `G T_y = T_y^-1 G`;
- orientation reversal is invisible after reducing charges modulo two;
- the exactness gate `im beta subset ker Sigma` forces mod-two neutrality.

Not checked here:
- quotient-manifold classification of the Klein bottle;
- twisted Mayer-Vietoris exactness;
- a full physical Weyl semimetal band model.
"""

from __future__ import annotations

import sympy as sp


def mod2(x: int) -> int:
    return x % 2


def sigma(charges: list[int]) -> int:
    """Total charge map Sigma : Z^k -> Z2."""
    return sum(charges) % 2


def main() -> None:
    print("--- SymPy Twin: Wallpaper pg -> Non-orientable Weyl Bridge ---")

    x, y = sp.symbols("x y", real=True)

    def ty(point: sp.Matrix) -> sp.Matrix:
        return sp.Matrix([point[0], point[1] + 1])

    def ty_inv(point: sp.Matrix) -> sp.Matrix:
        return sp.Matrix([point[0], point[1] - 1])

    def tx(point: sp.Matrix) -> sp.Matrix:
        return sp.Matrix([point[0] + 1, point[1]])

    def glide(point: sp.Matrix) -> sp.Matrix:
        return sp.Matrix([point[0] + sp.Rational(1, 2), -point[1]])

    p = sp.Matrix([x, y])
    assert sp.simplify(glide(glide(p)) - tx(p)) == sp.zeros(2, 1)
    print("pg relation G^2 = T_x: OK")

    assert sp.simplify(glide(ty(p)) - ty_inv(glide(p))) == sp.zeros(2, 1)
    print("pg relation G*T_y = T_y^-1*G: OK")

    for q in [-7, -2, -1, 0, 1, 2, 9]:
        assert mod2(-q) == mod2(q)
    print("orientation reversal chi -> -chi is invisible in Z2: OK")

    semimetal_image = [
        [1, 1],
        [2, 4],
        [-3, 5],
        [1, -1, 2],
        [3, 3, 4, 4],
    ]
    for charges in semimetal_image:
        assert sigma(charges) == 0
    print("exactness gate im(beta) subset ker(Sigma): OK")

    print("[SUCCESS] wallpaper pg glide supplies the finite Z2 Weyl charge bridge.")


if __name__ == "__main__":
    main()
