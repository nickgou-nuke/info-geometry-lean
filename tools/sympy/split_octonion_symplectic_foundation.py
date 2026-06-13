#!/usr/bin/env python3
"""Exact SymPy twin for the split-octonion symplectic foundation slice.

This verifier extends the Zorn split-octonion multiplication lane with the
smallest foundational identities needed for the Peirce-Witt / hyperbolic
commutator readout:

* ePlus and eMinus are orthogonal idempotents;
* H = ePlus - eMinus satisfies H^2 = 1;
* [up_i, down_i] = H for i = 0,1,2;
* {up_i, down_i} = 1 for i = 0,1,2;
* up_i and down_i are determinant-null.

Honest scope: this is a finite Zorn-coordinate theorem packet. It does not prove
physical helicity, a Cuntz representation, wallpaper/crystallographic symmetry,
parafermion braid coherence, or the global real Lie-group theorem
Aut(O_s)=G_{2(2)}.
"""

from __future__ import annotations

from dataclasses import dataclass
import sympy as sp

Vec3 = tuple[sp.Expr, sp.Expr, sp.Expr]
ZERO3: Vec3 = (sp.Integer(0), sp.Integer(0), sp.Integer(0))


def vadd(x: Vec3, y: Vec3) -> Vec3:
    return tuple(sp.expand(a + b) for a, b in zip(x, y))  # type: ignore[return-value]


def vsub(x: Vec3, y: Vec3) -> Vec3:
    return tuple(sp.expand(a - b) for a, b in zip(x, y))  # type: ignore[return-value]


def vneg(x: Vec3) -> Vec3:
    return tuple(sp.expand(-a) for a in x)  # type: ignore[return-value]


def smul(c: sp.Expr, x: Vec3) -> Vec3:
    return tuple(sp.expand(c * a) for a in x)  # type: ignore[return-value]


def dot(x: Vec3, y: Vec3) -> sp.Expr:
    return sp.expand(sum(a * b for a, b in zip(x, y)))


def cross(x: Vec3, y: Vec3) -> Vec3:
    x0, x1, x2 = x
    y0, y1, y2 = y
    return (
        sp.expand(x1 * y2 - x2 * y1),
        sp.expand(x2 * y0 - x0 * y2),
        sp.expand(x0 * y1 - x1 * y0),
    )


@dataclass(frozen=True)
class Zorn:
    a: sp.Expr
    b: sp.Expr
    x: Vec3
    y: Vec3

    def __add__(self, other: "Zorn") -> "Zorn":
        return Zorn(sp.expand(self.a + other.a), sp.expand(self.b + other.b), vadd(self.x, other.x), vadd(self.y, other.y))

    def __sub__(self, other: "Zorn") -> "Zorn":
        return Zorn(sp.expand(self.a - other.a), sp.expand(self.b - other.b), vsub(self.x, other.x), vsub(self.y, other.y))

    def __neg__(self) -> "Zorn":
        return Zorn(sp.expand(-self.a), sp.expand(-self.b), vneg(self.x), vneg(self.y))

    def __mul__(self, other: "Zorn") -> "Zorn":
        # (a,x;y,b)(c,u;v,d) =
        # (ac + x·v, au + d x - y×v; bv + c y + x×u, bd + y·u)
        a, b, x, y = self.a, self.b, self.x, self.y
        c, d, u, v = other.a, other.b, other.x, other.y
        return Zorn(
            sp.expand(a * c + dot(x, v)),
            sp.expand(b * d + dot(y, u)),
            vsub(vadd(smul(a, u), smul(d, x)), cross(y, v)),
            vadd(vadd(smul(b, v), smul(c, y)), cross(x, u)),
        )


def detZ(z: Zorn) -> sp.Expr:
    return sp.expand(z.a * z.b - dot(z.x, z.y))


def comm(x: Zorn, y: Zorn) -> Zorn:
    return x * y - y * x


def anticomm(x: Zorn, y: Zorn) -> Zorn:
    return x * y + y * x


def basis_vec(i: int) -> Vec3:
    return tuple(sp.Integer(1) if j == i else sp.Integer(0) for j in range(3))  # type: ignore[return-value]


Z0 = sp.Integer(0)
Z1 = sp.Integer(1)

zero = Zorn(Z0, Z0, ZERO3, ZERO3)
one = Zorn(Z1, Z1, ZERO3, ZERO3)
ePlus = Zorn(Z1, Z0, ZERO3, ZERO3)
eMinus = Zorn(Z0, Z1, ZERO3, ZERO3)
H = ePlus - eMinus
up = [Zorn(Z0, Z0, basis_vec(i), ZERO3) for i in range(3)]
down = [Zorn(Z0, Z0, ZERO3, basis_vec(i)) for i in range(3)]


def main() -> None:
    assert ePlus * ePlus == ePlus
    assert eMinus * eMinus == eMinus
    assert ePlus * eMinus == zero
    assert eMinus * ePlus == zero
    assert ePlus + eMinus == one
    assert H == Zorn(Z1, -Z1, ZERO3, ZERO3)
    assert H * H == one
    assert detZ(ePlus) == 0
    assert detZ(eMinus) == 0
    assert detZ(H) == -1
    assert detZ(one) == 1

    for i in range(3):
        assert up[i] * up[i] == zero
        assert down[i] * down[i] == zero
        assert up[i] * down[i] == ePlus
        assert down[i] * up[i] == eMinus
        assert comm(up[i], down[i]) == H
        assert anticomm(up[i], down[i]) == one
        assert detZ(up[i]) == 0
        assert detZ(down[i]) == 0

    # Cross-sector orientation sanity checks retained at finite basis level.
    assert up[0] * up[1] == down[2]
    assert down[0] * down[1] == -up[2]

    print("SPLIT_OCTONION_SYMPLECTIC_FOUNDATION_OK")
    print("scope: finite Zorn Peirce-Witt commutator packet only")


if __name__ == "__main__":
    main()
