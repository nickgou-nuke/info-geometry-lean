"""Finite symbolic audit for the Brillouin Klein wallpaper/Weyl bridge.

Scope:
* the `pg` glide relation on the 2D wallpaper chart;
* the Klein boundary charge evenness `a + b + a - b = 2a`;
* the `Z₂` orientation-reversal cancellation and gauge stability;
* the exact coordinate-level wallpaper-to-`D₅` lift.

No global Brillouin-zone classification is claimed.
"""

from __future__ import annotations

import sympy as sp


def check_zero(name: str, expr) -> None:
    simplified = sp.expand(sp.simplify(expr))
    if simplified != 0:
        raise AssertionError(f"{name} failed: {simplified}")
    print(f"[ok] {name}")


def main() -> None:
    x, y, theta, n, a, b = sp.symbols("x y theta n a b", integer=True)
    half = sp.Rational(1, 2)

    # 2D wallpaper chart: glide relation on the explicit finite model.
    p = sp.Matrix([x, y])
    glide = lambda q: sp.Matrix([q[0] + half, -q[1]])
    Ty = lambda q: sp.Matrix([q[0], q[1] + 1])
    Ty_inv = lambda q: sp.Matrix([q[0], q[1] - 1])

    check_zero("glide relation x-component", (glide(Ty(p)) - Ty_inv(glide(p)))[0])
    check_zero("glide relation y-component", (glide(Ty(p)) - Ty_inv(glide(p)))[1])

    # Klein boundary: a + b + a - b = 2a.
    boundary = a + b + a - b
    check_zero("Klein boundary even charge", boundary - 2 * a)

    # Z2 readout on the Brillouin Klein bottle.
    z2 = lambda g0, gp: (g0 + gp) % 2
    assert z2(theta, -theta) == 0
    print("[ok] orientation reversal cancels in Z2 readout")
    assert z2(theta + 2 * n, -theta) == z2(theta, -theta)
    print("[ok] gauge stability under adding two crossings")

    # Exact coordinate-level wallpaper-to-D5 lift.
    lattice = sp.Matrix([x, y, -x, -y, 0])
    check_zero("lattice sum zero", sum(lattice))

    sigma_x = sp.diag(-1, 1, -1, 1, 1)
    sigma_d = sp.Matrix([
        [0, 1, 0, 0, 0],
        [1, 0, 0, 0, 0],
        [0, 0, 0, 1, 0],
        [0, 0, 1, 0, 0],
        [0, 0, 0, 0, 1],
    ])
    check_zero("sigmaX lift x", (sigma_x * lattice - sp.Matrix([-x, y, x, -y, 0]))[0])
    check_zero("sigmaX lift y", (sigma_x * lattice - sp.Matrix([-x, y, x, -y, 0]))[1])
    check_zero("sigmaD lift x", (sigma_d * lattice - sp.Matrix([y, x, -y, -x, 0]))[0])
    check_zero("sigmaD lift y", (sigma_d * lattice - sp.Matrix([y, x, -y, -x, 0]))[1])


if __name__ == "__main__":
    main()
