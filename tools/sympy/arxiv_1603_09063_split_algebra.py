#!/usr/bin/env python3
"""Exact witnesses for arXiv:1603.09063v2 split-algebra formulas.

Paper: Fioresi--Latini--Marrani, "Klein and Conformal Superspaces,
Split Algebras and Spinor Orbits".

Scope: finite coordinate identities from equations (2.1)--(2.14), (5.4)--(5.8),
and (6.1)--(6.4).  These are witnesses only; Lean remains the proof authority.
No global Spin, conformal-group, symplectic-realization, or spinor-orbit theorem
is claimed by this script.
"""

from __future__ import annotations

from dataclasses import dataclass
import sympy as sp


@dataclass(frozen=True)
class SplitC:
    """Split complex numbers Cs: α + jβ, j² = 1."""
    a: sp.Expr
    b: sp.Expr

    def __add__(self, other: "SplitC") -> "SplitC":
        return SplitC(sp.expand(self.a + other.a), sp.expand(self.b + other.b))

    def __neg__(self) -> "SplitC":
        return SplitC(-self.a, -self.b)

    def __sub__(self, other: "SplitC") -> "SplitC":
        return self + (-other)

    def __mul__(self, other: "SplitC") -> "SplitC":
        return SplitC(
            sp.expand(self.a * other.a + self.b * other.b),
            sp.expand(self.a * other.b + self.b * other.a),
        )

    def conj(self) -> "SplitC":
        return SplitC(self.a, -self.b)

    def norm(self) -> sp.Expr:
        return sp.expand(self.a**2 - self.b**2)


@dataclass(frozen=True)
class SplitH:
    """Split quaternions Hs in the paper basis α + jβ + kγ + (kj)δ."""
    alpha: sp.Expr
    beta: sp.Expr
    gamma: sp.Expr
    delta: sp.Expr

    def __add__(self, other: "SplitH") -> "SplitH":
        return SplitH(
            sp.expand(self.alpha + other.alpha),
            sp.expand(self.beta + other.beta),
            sp.expand(self.gamma + other.gamma),
            sp.expand(self.delta + other.delta),
        )

    def __neg__(self) -> "SplitH":
        return SplitH(-self.alpha, -self.beta, -self.gamma, -self.delta)

    def __sub__(self, other: "SplitH") -> "SplitH":
        return self + (-other)

    def __mul__(self, other: "SplitH") -> "SplitH":
        a, b, c, d = self.alpha, self.beta, self.gamma, self.delta
        e, f, g, h = other.alpha, other.beta, other.gamma, other.delta
        return SplitH(
            sp.expand(a * e - c * g + b * f + d * h),
            sp.expand(a * f - c * h + b * e + d * g),
            sp.expand(a * g + c * e - b * h + d * f),
            sp.expand(a * h + c * f - b * g + d * e),
        )

    def star(self) -> "SplitH":
        """Conjugation h* = α - jβ - kγ - (kj)δ (eqs. 2.12--2.13)."""
        return SplitH(self.alpha, -self.beta, -self.gamma, -self.delta)

    def norm(self) -> sp.Expr:
        """|h|² = α² + γ² - β² - δ² (eq. 2.14)."""
        return sp.expand(self.alpha**2 + self.gamma**2 - self.beta**2 - self.delta**2)

    def to_matrix2x2_cs(self) -> list[list[SplitC]]:
        """Z-map Hs → M₂(Cs) from equation (2.18)."""
        hR = SplitC(self.alpha, self.beta)
        hI = SplitC(self.gamma, self.delta)
        return [[hR, hI], [-hI, hR]]


def assert_split_complex() -> None:
    """Equations (2.1)--(2.9)."""
    a, b = sp.symbols("a b")
    z = SplitC(a, b)
    one = SplitC(1, 0)
    j = SplitC(0, 1)
    E = SplitC(1, 1)
    Eb = SplitC(1, -1)
    assert j * j == one
    assert z * z.conj() == SplitC(z.norm(), 0)
    assert E * E == SplitC(2, 2)
    assert Eb * Eb == SplitC(2, -2)
    assert E * Eb == SplitC(0, 0)
    assert z * E == SplitC(a + b, a + b)
    assert z * Eb == SplitC(a - b, -a + b)
    lhs = SplitC((a + b) / 2, 0) * E + SplitC((a - b) / 2, 0) * Eb
    assert sp.simplify(lhs.a - a) == 0 and sp.simplify(lhs.b - b) == 0


def assert_klein_22_det() -> None:
    """Equation (5.6): det J₂(Cs) = x₁² + x₂² - x₃² - x₄²."""
    x1, x2, x3, x4 = sp.symbols("x1 x2 x3 x4")
    xp, xm = x1 + x4, x1 - x4
    a = SplitC(x3, x2)
    det_x = sp.expand(xp * xm - a.norm())
    assert sp.expand(det_x - (x1**2 + x2**2 - x3**2 - x4**2)) == 0


def assert_split_quaternion() -> None:
    """Equations (2.10)--(2.14) in the paper's basis."""
    one = SplitH(1, 0, 0, 0)
    j = SplitH(0, 1, 0, 0)
    k = SplitH(0, 0, 1, 0)
    kj = SplitH(0, 0, 0, 1)
    assert j * j == one
    assert k * k == SplitH(-1, 0, 0, 0)
    assert kj * kj == one
    assert k * j == kj
    assert j * k == -kj
    assert k * kj == -j
    assert kj * k == j
    assert kj * j == k
    assert j * kj == -k

    a, b, c, d, e, f, g, h, r, s, t, u = sp.symbols("a b c d e f g h r s t u")
    x = SplitH(a, b, c, d)
    y = SplitH(e, f, g, h)
    z = SplitH(r, s, t, u)
    assert (x * y) * z == x * (y * z)
    assert x * x.star() == SplitH(x.norm(), 0, 0, 0)
    assert x.to_matrix2x2_cs()[0][0] == SplitC(a, b)
    assert x.to_matrix2x2_cs()[0][1] == SplitC(c, d)


def assert_klein_33_det() -> None:
    """Equation (6.2): det J₂(Hs) = x₁²+x₂²+x₃²-x₄²-x₅²-x₆²."""
    x1, x2, x3, x4, x5, x6 = sp.symbols("x1 x2 x3 x4 x5 x6")
    xhatp, xhatm = x3 + x6, x3 - x6
    z = SplitH(x5, x1, x4, x2)
    det_v = sp.expand(xhatp * xhatm - z.norm())
    assert sp.expand(det_v - (x1**2 + x2**2 + x3**2 - x4**2 - x5**2 - x6**2)) == 0


def assert_clifford_and_galgebra_optional() -> list[str]:
    """Optional Cl(1,1) checks for the split-quaternion basis."""
    messages: list[str] = []
    try:
        from clifford import Cl

        _, blades = Cl(1, 1, firstIdx=1)
        e1, e2 = blades["e1"], blades["e2"]
        assert e1 * e1 == 1
        assert e2 * e2 == -1
        assert (e2 * e1) * (e2 * e1) == 1
        messages.append("CLIFFORD_CL11_OK")
    except Exception as exc:  # optional dependency
        messages.append(f"CLIFFORD_SKIPPED={type(exc).__name__}")

    try:
        from galgebra.ga import Ga

        ga = Ga("e1 e2", g=[1, -1])
        e1, e2 = ga.mv()
        assert str((e1 * e1).simplify()) == "1"
        assert str((e2 * e2).simplify()) == "-1"
        assert str(((e2 * e1) * (e2 * e1)).simplify()) == "1"
        messages.append("GALGEBRA_CL11_OK")
    except Exception as exc:  # optional dependency
        messages.append(f"GALGEBRA_SKIPPED={type(exc).__name__}")
    return messages


def main() -> None:
    assert_split_complex()
    assert_klein_22_det()
    assert_split_quaternion()
    assert_klein_33_det()
    optional = assert_clifford_and_galgebra_optional()
    print("ARXIV_1603_09063_SPLIT_COMPLEX_OK")
    print("ARXIV_1603_09063_KLEIN_22_DET_OK")
    print("ARXIV_1603_09063_SPLIT_QUATERNION_OK")
    print("ARXIV_1603_09063_KLEIN_33_DET_OK")
    for line in optional:
        print(line)


if __name__ == "__main__":
    main()
