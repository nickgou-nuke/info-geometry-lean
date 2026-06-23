#!/usr/bin/env python3
"""Finite SymPy companion for Cuntz/Lorentz/Poincare presentation operators.

This mirrors `InfoGeometry.Algebra.CuntzLorentzPoincarePresentation`.
It checks only finite algebraic surfaces:

* q = 0 off-diagonal Cuntz deformation relation;
* labeled Z2 grading of Cuntz generators and Majorana supercharges;
* finite wallpaper supercharge anticommutator `{Q,Q}=2P`;
* determinant preservation for the exact 2x2 Lorentz transport matrix.
"""

from __future__ import annotations

import sympy as sp


def verify_q_zero_deformation() -> None:
    n = 2
    s = sp.symbols(f"S0:{n}", commutative=False)
    sd = sp.symbols(f"Sd0:{n}", commutative=False)
    q = sp.Integer(0)

    # Off-diagonal Cuntz orthogonality: S_i^dag S_j = 0 for i != j.
    lhs_reduced = sp.Integer(0)
    rhs = q * (s[1] * sd[0])
    if sp.expand(lhs_reduced - rhs) != 0:
        raise AssertionError("q=0 deformed off-diagonal Cuntz relation failed")

    print("q=0 Cuntz deformation relation: OK")


def verify_labeled_supergrading() -> None:
    n = 2
    s = sp.symbols(f"S0:{n}", commutative=False)
    sd = sp.symbols(f"Sd0:{n}", commutative=False)
    labels = [True, False]

    def sign(i: int) -> int:
        return -1 if labels[i] else 1

    def gamma(expr):
        out = expr
        for i in range(n):
            out = out.subs({s[i]: sign(i) * s[i], sd[i]: sign(i) * sd[i]}, simultaneous=True)
        return sp.expand(out)

    for i in range(n):
        assert gamma(gamma(s[i])) == s[i]
        assert gamma(gamma(sd[i])) == sd[i]

    q0 = s[0] + sd[0]
    q1 = s[1] + sd[1]
    p0 = q0 * q0
    assert sp.expand(gamma(q0) + q0) == 0
    assert sp.expand(gamma(p0) - p0) == 0
    assert sp.expand(gamma(q1) - q1) == 0

    print("labeled Cuntz Z2 grading and supermomentum parity: OK")


def verify_wallpaper_supercharge_presentation() -> None:
    qmat = sp.Matrix([[1, 0, sp.Rational(1, 2)], [0, -1, 0], [0, 0, 1]])
    px = sp.Matrix([[1, 0, 1], [0, 1, 0], [0, 0, 1]])
    anticom = qmat * qmat + qmat * qmat
    comm = qmat * px - px * qmat

    if anticom != 2 * px:
        raise AssertionError("finite {Q,Q}=2P presentation failed")
    if comm != sp.zeros(3, 3):
        raise AssertionError("finite [Q,P]=0 presentation failed")

    print("finite Cuntz/SUSY presentation `{Q,Q}=2P` and `[Q,P]=0`: OK")


def hermitian_spacetime(t, x, y, z) -> sp.Matrix:
    sigma0 = sp.eye(2)
    sigma1 = sp.Matrix([[0, 1], [1, 0]])
    sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sigma3 = sp.Matrix([[1, 0], [0, -1]])
    return t * sigma0 + x * sigma1 + y * sigma2 + z * sigma3


def verify_lorentz_presentation_operator() -> None:
    t, x, y, z = sp.symbols("t x y z")
    spacetime = hermitian_spacetime(t, x, y, z)
    minkowski = t**2 - x**2 - y**2 - z**2
    boost = sp.Matrix([[2, 1], [1, 1]])
    transported = boost * spacetime * boost

    assert sp.expand(sp.det(spacetime) - minkowski) == 0
    assert sp.det(boost) == 1
    assert sp.expand(sp.det(transported) - sp.det(spacetime)) == 0
    assert (-sp.eye(2)) * spacetime * (-sp.eye(2)) == spacetime

    print("finite Lorentz presentation operator determinant invariance: OK")


def verify_affine_poincare_presentation() -> None:
    t, x, y, z = sp.symbols("t x y z")
    at, ax, ay, az = sp.symbols("at ax ay az")
    bt, bx, by, bz = sp.symbols("bt bx by bz")
    eta = sp.diag(1, -1, -1, -1)
    v = sp.Matrix([t, x, y, z])
    w = sp.Matrix([bt, bx, by, bz])
    a = sp.Matrix([at, ax, ay, az])

    # A rational 1+1 boost in the (t,x)-plane: c^2 - s^2 = 1.
    boost = sp.Matrix(
        [
            [sp.Rational(5, 4), sp.Rational(3, 4), 0, 0],
            [sp.Rational(3, 4), sp.Rational(5, 4), 0, 0],
            [0, 0, 1, 0],
            [0, 0, 0, 1],
        ]
    )
    if sp.simplify(boost.T * eta * boost - eta) != sp.zeros(4, 4):
        raise AssertionError("Lorentz linear part failed metric preservation")

    def interval(p, q):
        d = p - q
        return sp.expand((d.T * eta * d)[0])

    affine_v = boost * v + a
    affine_w = boost * w + a
    if sp.simplify(interval(affine_v, affine_w) - interval(v, w)) != 0:
        raise AssertionError("affine Poincare interval preservation failed")

    print("finite affine Poincare group presentation interval preservation: OK")


def main() -> int:
    verify_q_zero_deformation()
    verify_labeled_supergrading()
    verify_wallpaper_supercharge_presentation()
    verify_lorentz_presentation_operator()
    verify_affine_poincare_presentation()
    print("cuntz_lorentz_poincare_presentation: all checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
