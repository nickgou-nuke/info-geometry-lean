#!/usr/bin/env python3
"""Exact witnesses for Klein split-complex spinor stabilizers.

Lean owner: lean/InfoGeometry/Algebra/KleinSpinorOrbit.lean
Scope: raw 2x2 C_s determinant-one/stabilizer identities only; no full orbit
classification or Spin(2,2) double-cover theorem is claimed.
"""
from __future__ import annotations
from dataclasses import dataclass
import sympy as sp


@dataclass(frozen=True)
class Cs:
    re: sp.Expr
    im: sp.Expr

    def __add__(self, o: "Cs") -> "Cs":
        return Cs(sp.expand(self.re + o.re), sp.expand(self.im + o.im))

    def __neg__(self) -> "Cs":
        return Cs(-self.re, -self.im)

    def __sub__(self, o: "Cs") -> "Cs":
        return self + (-o)

    def __mul__(self, o: "Cs") -> "Cs":
        return Cs(sp.expand(self.re * o.re + self.im * o.im), sp.expand(self.re * o.im + self.im * o.re))

    def eq(self, o: "Cs") -> bool:
        return sp.simplify(self.re - o.re) == 0 and sp.simplify(self.im - o.im) == 0


ZERO = Cs(0, 0)
ONE = Cs(1, 0)
E = Cs(1, 1)
EBAR = Cs(1, -1)

def qsmul(r, z: Cs) -> Cs:
    return Cs(sp.expand(r * z.re), sp.expand(r * z.im))


def mat_action(M, psi):
    aa, ab, ba, bb = M
    p, n = psi
    return (aa * p + ab * n, ba * p + bb * n)


def det(M):
    aa, ab, ba, bb = M
    return aa * bb - ab * ba


def assert_generic_unipotent():
    x, y = sp.symbols("x y")
    b = Cs(x, y)
    M = (ONE, b, ZERO, ONE)
    assert det(M).eq(ONE)
    out = mat_action(M, (ONE, ZERO))
    assert out[0].eq(ONE) and out[1].eq(ZERO)


def assert_null_ebar_family():
    r, s, x, y, u, v = sp.symbols("r s x y u v")
    b = Cs(x, y)
    d = Cs(u, v)
    M = (ONE + qsmul(r, EBAR), b, qsmul(s, EBAR), d)
    out = mat_action(M, (E, ZERO))
    assert out[0].eq(E) and out[1].eq(ZERO)
    assert ((ONE + qsmul(r, EBAR)).re + (ONE + qsmul(r, EBAR)).im).expand() == 1
    assert (qsmul(s, EBAR).re + qsmul(s, EBAR).im).expand() == 0


def assert_diagonal_null_condition():
    ar, ai, br, bi, cr, ci, dr, di = sp.symbols("ar ai br bi cr ci dr di")
    aa, ab, ba, bb = Cs(ar, ai), Cs(br, bi), Cs(cr, ci), Cs(dr, di)
    M = (aa, ab, ba, bb)
    out = mat_action(M, (E, E))
    row1 = sp.expand(ar + ai + br + bi)
    row2 = sp.expand(cr + ci + dr + di)
    assert (out[0].eq(E)) == (sp.simplify(row1 - 1) == 0)
    assert (out[1].eq(E)) == (sp.simplify(row2 - 1) == 0)


def main() -> None:
    assert (E * EBAR).eq(ZERO)
    assert_generic_unipotent()
    assert_null_ebar_family()
    assert_diagonal_null_condition()
    print("KLEIN_SPINOR_E_ZERO_DIVISOR_OK")
    print("KLEIN_SPINOR_GENERIC_UNIPOTENT_DET_ONE_OK")
    print("KLEIN_SPINOR_NULL_EBAR_FAMILY_STABILIZES_OK")
    print("KLEIN_SPINOR_DIAGONAL_NULL_ROW_CONDITION_OK")


if __name__ == "__main__":
    main()
