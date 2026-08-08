#!/usr/bin/env python3
"""Finite witness for VacuumJonesKleinBirefringence.lean.

Checks the Jones tensor entries, determinant-one optical gates, the projective
Klein half-shift, and the trivial-only Raman selection rule.
"""

from __future__ import annotations

from enum import Enum

import sympy as sp


I = sp.I


class S3Sector(Enum):
    TRIVIAL = "trivial"
    SIGN = "sign"
    STANDARD = "standard"


def vacuum_jones_tensor(eps11: sp.Expr, eps22: sp.Expr, gamma: sp.Expr) -> sp.Matrix:
    return sp.Matrix([[eps11, I * gamma], [-I * gamma, eps22]])


def jones_dichroic_boost(alpha: sp.Expr) -> sp.Matrix:
    return sp.Matrix([[sp.exp(alpha), 0], [0, sp.exp(-alpha)]])


def nonlinear_axial_gate(x: sp.Expr) -> sp.Matrix:
    return sp.Matrix([[sp.exp(x), 0], [0, sp.exp(-x)]])


def affine_m(k: tuple[sp.Rational, sp.Rational]) -> tuple[sp.Rational, sp.Rational]:
    kx, ky = k
    return -kx, ky + sp.Rational(1, 2)


def recip_y(k: tuple[sp.Rational, sp.Rational]) -> tuple[sp.Rational, sp.Rational]:
    kx, ky = k
    return kx, ky + 1


def raman_active(sector: S3Sector) -> bool:
    return sector is S3Sector.TRIVIAL


def main() -> None:
    eps11, eps22, gamma, alpha, x = sp.symbols("eps11 eps22 gamma alpha x", real=True)

    eps = vacuum_jones_tensor(eps11, eps22, gamma)
    assert eps[0, 0] - eps[1, 1] == eps11 - eps22
    assert eps[0, 1] == I * gamma
    assert eps[1, 0] == -I * gamma

    assert sp.simplify(jones_dichroic_boost(alpha).det() - 1) == 0
    assert sp.simplify(nonlinear_axial_gate(x).det() - 1) == 0

    mx = sp.Matrix([[0, 1], [1, 0]])
    ly = sp.Matrix([[1, 0], [0, -1]])
    ident = sp.eye(2)
    assert mx * ly == -(ly * mx)
    assert mx * ly * mx * ly == -ident

    samples = [
        (sp.Rational(0), sp.Rational(0)),
        (sp.Rational(1, 3), sp.Rational(2, 5)),
        (sp.Rational(-7, 4), sp.Rational(9, 2)),
    ]
    for point in samples:
        assert affine_m(affine_m(point)) == recip_y(point)

    assert [s.value for s in S3Sector if raman_active(s)] == ["trivial"]

    print("Jones tensor delta =", eps[0, 0] - eps[1, 1])
    print("optical activity entries =", eps[0, 1], eps[1, 0])
    print("dichroic boost det =", sp.simplify(jones_dichroic_boost(alpha).det()))
    print("nonlinear axial det =", sp.simplify(nonlinear_axial_gate(x).det()))
    print("Klein half-shift samples =", [affine_m(affine_m(point)) for point in samples])
    print("Raman active sectors =", [s.value for s in S3Sector if raman_active(s)])
    print("vacuum_jones_klein_birefringence.py: finite audit passed")


if __name__ == "__main__":
    main()
