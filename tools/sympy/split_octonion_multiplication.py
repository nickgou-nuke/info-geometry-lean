#!/usr/bin/env python3
"""Exact split-octonion multiplication verifier.

Companion to:
  lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean

This is a true multiplication layer: it implements the Zorn vector-matrix
split-octonion product on coordinates

  X = [[a, x], [y, b]],  x,y in Z^3,

with product

  (a,x;y,b)(c,u;v,d) =
    (a c + x·v,
     a u + d x - y×v;
     b v + c y + x×u,
     b d + y·u).

It verifies the concrete basis table, nonassociativity witness, alternativity
on basis elements, and determinant/norm composition on symbolic coordinates.
It does not claim a G2(2) automorphism theorem or a particle-classification theorem.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any
import sympy as sp


Expr = Any
Vec3 = tuple[Expr, Expr, Expr]


def dot(x: Vec3, y: Vec3) -> sp.Expr:
    return sp.expand(sum(x[i] * y[i] for i in range(3)))


def cross(x: Vec3, y: Vec3) -> Vec3:
    return (
        sp.expand(x[1] * y[2] - x[2] * y[1]),
        sp.expand(x[2] * y[0] - x[0] * y[2]),
        sp.expand(x[0] * y[1] - x[1] * y[0]),
    )


def vadd(x: Vec3, y: Vec3) -> Vec3:
    return tuple(sp.expand(x[i] + y[i]) for i in range(3))  # type: ignore[return-value]


def vsub(x: Vec3, y: Vec3) -> Vec3:
    return tuple(sp.expand(x[i] - y[i]) for i in range(3))  # type: ignore[return-value]


def smul(c: sp.Expr, x: Vec3) -> Vec3:
    return tuple(sp.expand(c * x[i]) for i in range(3))  # type: ignore[return-value]


@dataclass(frozen=True)
class Zorn:
    a: sp.Expr
    b: sp.Expr
    x: Vec3
    y: Vec3

    def __add__(self, other: "Zorn") -> "Zorn":
        return Zorn(
            sp.expand(self.a + other.a),
            sp.expand(self.b + other.b),
            vadd(self.x, other.x),
            vadd(self.y, other.y),
        )

    def __sub__(self, other: "Zorn") -> "Zorn":
        return Zorn(
            sp.expand(self.a - other.a),
            sp.expand(self.b - other.b),
            vsub(self.x, other.x),
            vsub(self.y, other.y),
        )

    def __mul__(self, other: "Zorn") -> "Zorn":
        return Zorn(
            sp.expand(self.a * other.a + dot(self.x, other.y)),
            sp.expand(self.b * other.b + dot(self.y, other.x)),
            vsub(vadd(smul(self.a, other.x), smul(other.b, self.x)), cross(self.y, other.y)),
            vadd(vadd(smul(self.b, other.y), smul(other.a, self.y)), cross(self.x, other.x)),
        )

    def det(self) -> sp.Expr:
        return sp.expand(self.a * self.b - dot(self.x, self.y))

    def simplified(self) -> "Zorn":
        return Zorn(
            sp.expand(self.a),
            sp.expand(self.b),
            tuple(sp.expand(t) for t in self.x),  # type: ignore[arg-type]
            tuple(sp.expand(t) for t in self.y),  # type: ignore[arg-type]
        )


ZERO = Zorn(0, 0, (0, 0, 0), (0, 0, 0))
ONE = Zorn(1, 1, (0, 0, 0), (0, 0, 0))
EPLUS = Zorn(1, 0, (0, 0, 0), (0, 0, 0))
EMINUS = Zorn(0, 1, (0, 0, 0), (0, 0, 0))
BASIS_VEC = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
UP = [Zorn(0, 0, e, (0, 0, 0)) for e in BASIS_VEC]
DOWN = [Zorn(0, 0, (0, 0, 0), e) for e in BASIS_VEC]
BASIS = [EPLUS, EMINUS] + UP + DOWN


def assert_eq(left: Zorn, right: Zorn, label: str) -> None:
    if left.simplified() != right.simplified():
        raise AssertionError(f"{label}: {left.simplified()} != {right.simplified()}")


def verify_basis_table() -> None:
    assert_eq(EPLUS * EPLUS, EPLUS, "e+ idempotent")
    assert_eq(EMINUS * EMINUS, EMINUS, "e- idempotent")
    assert_eq(EPLUS * EMINUS, ZERO, "e+e-")
    assert_eq(EMINUS * EPLUS, ZERO, "e-e+")
    for i in range(3):
        assert_eq(EPLUS * UP[i], UP[i], f"e+ u{i}")
        assert_eq(UP[i] * EMINUS, UP[i], f"u{i} e-")
        assert_eq(EMINUS * DOWN[i], DOWN[i], f"e- v{i}")
        assert_eq(DOWN[i] * EPLUS, DOWN[i], f"v{i} e+")
        assert_eq(UP[i] * UP[i], ZERO, f"u{i}^2")
        assert_eq(DOWN[i] * DOWN[i], ZERO, f"v{i}^2")
        assert_eq(UP[i] * DOWN[i], EPLUS, f"u{i}v{i}")
        assert_eq(DOWN[i] * UP[i], EMINUS, f"v{i}u{i}")
    for i, j, k in [(0, 1, 2), (1, 2, 0), (2, 0, 1)]:
        assert_eq(UP[i] * UP[j], DOWN[k], f"u{i}u{j}=v{k}")
        assert_eq(UP[j] * UP[i], Zorn(0, 0, (0, 0, 0), tuple(-c for c in BASIS_VEC[k])), f"u{j}u{i}=-v{k}")
        assert_eq(DOWN[i] * DOWN[j], Zorn(0, 0, tuple(-c for c in BASIS_VEC[k]), (0, 0, 0)), f"v{i}v{j}=-u{k}")
        assert_eq(DOWN[j] * DOWN[i], UP[k], f"v{j}v{i}=u{k}")


def associator(x: Zorn, y: Zorn, z: Zorn) -> Zorn:
    return (x * y) * z - x * (y * z)


def verify_nonassoc_and_alternativity_on_basis() -> None:
    witness = associator(UP[0], UP[1], DOWN[1])
    assert witness != ZERO, "expected a concrete nonzero associator witness"
    for x in BASIS:
        for y in BASIS:
            assert_eq(associator(x, x, y), ZERO, "left alternativity on basis")
            assert_eq(associator(y, x, x), ZERO, "right alternativity on basis")


def verify_symbolic_norm_composition() -> None:
    xs = sp.symbols("a b x0 x1 x2 y0 y1 y2")
    ys = sp.symbols("c d u0 u1 u2 v0 v1 v2")
    X = Zorn(xs[0], xs[1], xs[2:5], xs[5:8])
    Y = Zorn(ys[0], ys[1], ys[2:5], ys[5:8])
    diff = sp.expand((X * Y).det() - X.det() * Y.det())
    assert diff == 0, f"det composition failed: {diff}"


def main() -> None:
    verify_basis_table()
    verify_nonassoc_and_alternativity_on_basis()
    verify_symbolic_norm_composition()
    print("OK split_octonion_multiplication: true Zorn split-octonion product verified")
    print("OK basis table, nonzero associator witness, basis alternativity, symbolic detZ composition")
    print("scope: multiplication/norm layer only; no G2(2), SU(3), or particle classification theorem claimed")


if __name__ == "__main__":
    main()
