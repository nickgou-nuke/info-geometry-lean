#!/usr/bin/env python3
"""Finite Jones/Stokes/Pauli checks.

Mirrors `InfoGeometry.Optics.JonesPoincareSphere`.

Closed finite content only:
* a Jones spinor `(a + i b, c + i d)` defines Stokes coordinates;
* the Stokes coordinates satisfy the light-cone identity;
* unit intensity gives the unit Poincare sphere;
* circular-basis poles are the two coordinate axes;
* the Pauli/Hestenes determinant of the Stokes four-vector is zero.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr: sp.Expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed:\n{reduced}")


def main() -> int:
    a, b, c, d = sp.symbols("a b c d", real=True)

    left_intensity = a**2 + b**2
    right_intensity = c**2 + d**2
    s0 = left_intensity + right_intensity
    s1 = left_intensity - right_intensity
    s2 = 2 * (a * c + b * d)
    s3 = 2 * (b * c - a * d)

    assert_zero(s1**2 + s2**2 + s3**2 - s0**2, "finite Stokes light-cone identity")

    sigma0 = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    pauli = s0 * sigma0 + s2 * sigma1 + s3 * sigma2 + s1 * sigma3
    assert_zero(pauli.det(), "Pauli determinant of Stokes four-vector")

    plus = {a: 1, b: 0, c: 0, d: 0}
    minus = {a: 0, b: 0, c: 1, d: 0}
    assert_zero(s0.subs(plus) - 1, "plus circular total intensity")
    assert_zero(s1.subs(plus) - 1, "plus circular pole")
    assert_zero(s2.subs(plus), "plus circular real coherence")
    assert_zero(s3.subs(plus), "plus circular imaginary coherence")
    assert_zero(s0.subs(minus) - 1, "minus circular total intensity")
    assert_zero(s1.subs(minus) + 1, "minus circular pole")
    assert_zero(s2.subs(minus), "minus circular real coherence")
    assert_zero(s3.subs(minus), "minus circular imaginary coherence")

    sphere_gap = s1**2 + s2**2 + s3**2 - 1
    assert_zero(sphere_gap - (s0**2 - 1), "unit-intensity sphere residual")

    print("OK finite Jones/Stokes/Poincare-sphere/Pauli checks")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
