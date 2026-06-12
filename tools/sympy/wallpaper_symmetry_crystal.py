#!/usr/bin/env python3
"""
SymPy witness for `InfoGeometry.Topology.Wallpaper.WallpaperSymmetry`.

It checks the elementary `pg` wallpaper relations for the glide
G(x,y) = (x + 1/2, -y):

  G^2 = T_x,
  G T_y = T_y^{-1} G,
  G T_y G^{-1} = T_y^{-1}.

These are the finite presentation relations behind a Klein-bottle quotient.  The
script does not prove a full quotient-manifold classification or a physical
Brillouin-zone theorem.
"""

from __future__ import annotations

import sympy as sp


def compose(f, g):
    """Return f ∘ g for maps represented as callables on `(x,y)`."""
    return lambda x, y: f(*g(x, y))


def matrix_of(pair):
    return sp.Matrix(pair)


def main() -> None:
    x, y = sp.symbols("x y", real=True)

    def T_x(a, b):
        return (a + 1, b)

    def T_y(a, b):
        return (a, b + 1)

    def T_y_inv(a, b):
        return (a, b - 1)

    def G(a, b):
        return (a + sp.Rational(1, 2), -b)

    def G_inv(a, b):
        return (a - sp.Rational(1, 2), -b)

    p = matrix_of((x, y))
    g_squared = matrix_of(compose(G, G)(x, y))
    tx = matrix_of(T_x(x, y))
    g_ty = matrix_of(compose(G, T_y)(x, y))
    ty_inv_g = matrix_of(compose(T_y_inv, G)(x, y))
    g_ty_g_inv = matrix_of(compose(compose(G, T_y), G_inv)(x, y))
    ty_inv = matrix_of(T_y_inv(x, y))

    glide_square_residual = sp.simplify(g_squared - tx)
    commutation_residual = sp.simplify(g_ty - ty_inv_g)
    conjugation_residual = sp.simplify(g_ty_g_inv - ty_inv)

    print("=== Wallpaper Group `pg` finite relations ===")
    print(f"lattice coordinate: {p.T}")
    print(f"G^2 residual against T_x: {glide_square_residual}")
    print(f"G*T_y - T_y^-1*G residual: {commutation_residual}")
    print(f"G*T_y*G^-1 - T_y^-1 residual: {conjugation_residual}")

    assert glide_square_residual == sp.zeros(2, 1)
    assert commutation_residual == sp.zeros(2, 1)
    assert conjugation_residual == sp.zeros(2, 1)

    print("[SUCCESS] finite `pg` wallpaper relations match the Lean proofs.")


if __name__ == "__main__":
    main()
