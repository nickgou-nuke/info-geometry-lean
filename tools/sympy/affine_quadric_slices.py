#!/usr/bin/env python3
"""Finite symbolic audit for affine slices of homogeneous quadrics."""

from __future__ import annotations

import sympy as sp


def require_zero(name: str, expr) -> None:
    simplified = sp.expand(sp.simplify(expr))
    if simplified != 0:
        raise AssertionError(f"{name} failed: {simplified}")
    print(f"[ok] {name}")


def main() -> None:
    x, y, z, w, l = sp.symbols("x y z w l")

    ellipsoid_hom = x**2 + y**2 + z**2 - w**2
    hyperboloid_hom = x**2 + y**2 - z**2 - w**2
    paraboloid_hom = x**2 + y**2 - z * w

    ellipsoid_scaled = (l * x) ** 2 + (l * y) ** 2 + (l * z) ** 2 - (l * w) ** 2
    hyperboloid_scaled = (l * x) ** 2 + (l * y) ** 2 - (l * z) ** 2 - (l * w) ** 2
    paraboloid_scaled = (l * x) ** 2 + (l * y) ** 2 - (l * z) * (l * w)

    require_zero("ellipsoid scaling law", ellipsoid_scaled - l**2 * ellipsoid_hom)
    require_zero(
        "hyperboloid scaling law", hyperboloid_scaled - l**2 * hyperboloid_hom
    )
    require_zero("paraboloid scaling law", paraboloid_scaled - l**2 * paraboloid_hom)

    require_zero("ellipsoid chart w=1", ellipsoid_hom.subs(w, 1) - (x**2 + y**2 + z**2 - 1))
    require_zero(
        "hyperboloid chart w=1", hyperboloid_hom.subs(w, 1) - (x**2 + y**2 - z**2 - 1)
    )
    require_zero("paraboloid chart w=1", paraboloid_hom.subs(w, 1) - (x**2 + y**2 - z))

    print("ellipsoid_hom =", ellipsoid_hom)
    print("hyperboloid_hom =", hyperboloid_hom)
    print("paraboloid_hom =", paraboloid_hom)


if __name__ == "__main__":
    main()
