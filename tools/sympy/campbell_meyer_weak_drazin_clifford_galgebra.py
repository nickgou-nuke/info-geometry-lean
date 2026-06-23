#!/usr/bin/env python3
"""
Clifford / galgebra certificate for Campbell--Meyer weak Drazin inverses.

The `Cl(1,1)` packet models a regular idempotent lane plus a square-zero null
lane.  The exact rational certificate is performed by a small Fraction-based
Cl(1,1) multiplication table, while the installed `clifford` and `galgebra`
packages are also instantiated and checked.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class Cl11:
    c: tuple[Fraction, Fraction, Fraction, Fraction]

    def __add__(self, other: "Cl11") -> "Cl11":
        return Cl11(tuple(a + b for a, b in zip(self.c, other.c)))

    def __sub__(self, other: "Cl11") -> "Cl11":
        return Cl11(tuple(a - b for a, b in zip(self.c, other.c)))

    def scale(self, q: Fraction) -> "Cl11":
        return Cl11(tuple(q * a for a in self.c))

    def __mul__(self, other: "Cl11") -> "Cl11":
        a0, a1, a2, a12 = self.c
        b0, b1, b2, b12 = other.c
        return Cl11((
            a0*b0 + a1*b1 - a2*b2 + a12*b12,
            a0*b1 + a1*b0 - a2*b12 + a12*b2,
            a0*b2 + a1*b12 + a2*b0 - a12*b1,
            a0*b12 + a1*b2 - a2*b1 + a12*b0,
        ))

    def __pow__(self, n: int) -> "Cl11":
        one = Cl11((Fraction(1), Fraction(0), Fraction(0), Fraction(0)))
        result = one
        for _ in range(n):
            result = result * self
        return result


def assert_weak(a: Cl11, b: Cl11, k: int, label: str) -> None:
    if b * (a ** (k + 1)) != a ** k:
        raise AssertionError(f"{label}: B A^(k+1) = A^k failed")


def main() -> None:
    print("=== Campbell--Meyer weak Drazin Clifford / galgebra certificate ===")

    from clifford import Cl

    layout, _ = Cl(1, 1)
    assert layout.sig[0] == 1
    assert layout.sig[1] == -1

    one = Cl11((Fraction(1), Fraction(0), Fraction(0), Fraction(0)))
    e1 = Cl11((Fraction(0), Fraction(1), Fraction(0), Fraction(0)))
    e2 = Cl11((Fraction(0), Fraction(0), Fraction(1), Fraction(0)))
    n_plus = (e1 + e2).scale(Fraction(1, 2))
    n_minus = (e1 - e2).scale(Fraction(1, 2))
    p_plus = n_plus * n_minus
    p_minus = n_minus * n_plus
    zero = one.scale(Fraction(0))
    assert n_plus * n_plus == zero
    assert p_plus * p_plus == p_plus
    assert p_plus + p_minus == one

    a = p_plus.scale(Fraction(2)) + n_plus
    poly = one.scale(Fraction(1, 2))
    left_annihilator = Cl11((Fraction(-2), Fraction(1), Fraction(1), Fraction(-2)))
    wild = poly + left_annihilator
    assert left_annihilator * (a ** 3) == zero
    assert_weak(a, poly, 2, "polynomial weak lane")
    assert_weak(a, wild, 2, "left-annihilator weak lane")
    assert wild != poly
    print("PASS: clifford-backed exact rational Cl(1,1) weak-Drazin lanes")

    from galgebra.ga import Ga

    built = Ga.build("g1 g2", g=[1, -1])
    if len(built) == 2:
        _, basis = built
        g1, g2 = basis
    else:
        g1, g2 = built[1], built[2]

    m_plus = (g1 + g2) / 2
    m_minus = (g1 - g2) / 2
    q_plus = m_plus * m_minus
    q_minus = m_minus * m_plus
    z = 0 * q_plus
    assert m_plus * m_plus == z
    assert q_plus * q_plus == q_plus
    assert q_plus + q_minus == 1
    ag = 2 * q_plus + m_plus
    polyg = (q_plus + q_minus) / 2
    rg = -2 + g1 + g2 - 2 * (g1 * g2)
    wildg = polyg + rg
    assert rg * (ag ** 3) == z
    assert polyg * (ag ** 3) == ag ** 2
    assert wildg * (ag ** 3) == ag ** 2
    assert wildg != polyg
    print("PASS: galgebra symbolic Cl(1,1) weak-Drazin lanes")

    print("CAMPBELL_MEYER_WEAK_DRAZIN_CLIFFORD_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
