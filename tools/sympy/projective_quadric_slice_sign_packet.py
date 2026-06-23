"""Finite symbolic audit for the projective quadric slice/sign packet.

Scope:
* unit-coefficient affine slice identities at `w = 1`;
* determinant signs of the canonical homogeneous representative matrices.

No general projective classification is claimed.
"""

from __future__ import annotations

import sympy as sp


def require_zero(name: str, expr) -> None:
    simplified = sp.expand(sp.simplify(expr))
    if simplified != 0:
        raise AssertionError(f"{name} failed: {simplified}")
    print(f"[ok] {name}")


def main() -> None:
    x, y, z, w = sp.symbols("x y z w")

    ellipsoid_hom = x**2 + y**2 + z**2 - w**2
    hyperboloid_hom = x**2 + y**2 - z**2 - w**2
    paraboloid_hom = x**2 + y**2 - z * w

    require_zero(
        "ellipsoid chart w=1",
        ellipsoid_hom.subs(w, 1) - (x**2 + y**2 + z**2 - 1),
    )
    require_zero(
        "hyperboloid chart w=1",
        hyperboloid_hom.subs(w, 1) - (x**2 + y**2 - z**2 - 1),
    )
    require_zero(
        "paraboloid chart w=1",
        paraboloid_hom.subs(w, 1) - (x**2 + y**2 - z),
    )

    ellipsoid_quadric = sp.diag(1, 1, 1, -1)
    hyperboloid_quadric = sp.diag(1, 1, -1, -1)
    paraboloid_quadric = sp.diag(1, 1, -1, 1)  # sign packet only

    det_ellipsoid = sp.simplify(ellipsoid_quadric.det())
    det_hyperboloid = sp.simplify(hyperboloid_quadric.det())
    det_paraboloid = sp.simplify(paraboloid_quadric.det())

    print("det(ellipsoid)   =", det_ellipsoid)
    print("det(hyperboloid) =", det_hyperboloid)
    print("det(paraboloid)  =", det_paraboloid)

    assert det_ellipsoid == -1
    assert det_hyperboloid == 1
    assert det_paraboloid == -1
    print("[ok] determinant sign packet")


if __name__ == "__main__":
    main()
