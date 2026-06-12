"""Finite 4D Hodge-star mirror for the Lean owner module.

This script mirrors `InfoGeometry.Canonical.HodgeStar4DFinite`.  It checks the
six-component Lorentzian two-form shadow only:

* component order `(01, 02, 03, 23, 31, 12)`;
* `star^2 = -1`;
* complex `+i` and `-i` eigenspace projections;
* reconstruction from self-dual and anti-self-dual parts.

It does not claim smooth Hodge theory, integration, Stokes' theorem, instantons,
Maxwell equations, or Yang-Mills dynamics.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr: sp.Matrix, label: str) -> None:
    if sp.simplify(expr) != sp.zeros(*expr.shape):
        raise AssertionError(f"{label} did not simplify to zero:\n{sp.simplify(expr)}")


def hodge_star_matrix() -> sp.Matrix:
    """Lorentzian Hodge star on `(01, 02, 03, 23, 31, 12)`."""
    return sp.Matrix(
        [
            [0, 0, 0, 1, 0, 0],
            [0, 0, 0, 0, 1, 0],
            [0, 0, 0, 0, 0, 1],
            [-1, 0, 0, 0, 0, 0],
            [0, -1, 0, 0, 0, 0],
            [0, 0, -1, 0, 0, 0],
        ]
    )


def main() -> None:
    star = hodge_star_matrix()
    identity = sp.eye(6)
    assert_zero(star * star + identity, "star^2 = -1")

    f = sp.Matrix(sp.symbols("f01 f02 f03 f23 f31 f12"))
    self_dual = (f - sp.I * star * f) / 2
    anti_self_dual = (f + sp.I * star * f) / 2

    assert_zero(star * self_dual - sp.I * self_dual, "self-dual +i eigenvalue")
    assert_zero(star * anti_self_dual + sp.I * anti_self_dual, "anti-self-dual -i eigenvalue")
    assert_zero(self_dual + anti_self_dual - f, "self+anti reconstruction")
    assert_zero(self_dual - anti_self_dual + sp.I * star * f, "self-anti star recovery")

    print("hodge_star_4d: ok")
    print("  star^2 = -1 on finite Lorentzian two-forms")
    print("  complex self/anti-self decomposition reconstructs the input")
    print("  honest scope: finite six-component algebra only")


if __name__ == "__main__":
    main()
