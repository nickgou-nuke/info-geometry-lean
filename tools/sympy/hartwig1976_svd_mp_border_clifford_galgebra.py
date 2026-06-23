#!/usr/bin/env python3
"""
Clifford / galgebra certificate for the rank-one SVD lane in Hartwig 1976.

The exact rational Clifford calculation uses the `Cl(1,1)` idempotent split
`p_+ + p_- = 1`.  The `clifford` package is used to instantiate the same
signature, while the rational certificate is performed with `Fraction`
coefficients to avoid floating arithmetic.  The `galgebra` half performs the
same checks symbolically over SymPy rationals.
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


def assert_mp(a: Cl11, x: Cl11, label: str) -> None:
    zero = Cl11((Fraction(0),) * 4)
    if a * x * a - a != zero:
        raise AssertionError(f"{label}: A X A = A failed")
    if x * a * x - x != zero:
        raise AssertionError(f"{label}: X A X = X failed")


def main() -> None:
    print("=== Hartwig 1976 Clifford / galgebra MP border certificate ===")

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
    assert p_minus * p_minus == p_minus
    assert p_plus * p_minus == zero
    assert p_plus + p_minus == one

    base = p_plus.scale(Fraction(2))
    base_mp = p_plus.scale(Fraction(1, 2))
    assert_mp(base, base_mp, "rank-one SVD Clifford lane")
    schur3 = p_plus.scale(Fraction(2)) - p_minus.scale(Fraction(1, 5))
    schur3_mp = p_plus.scale(Fraction(1, 2)) - p_minus.scale(Fraction(5))
    assert_mp(schur3, schur3_mp, "Case 3 Schur Clifford lane")
    print("PASS: clifford-backed exact Cl(1,1) rational MP lanes")

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
    assert q_minus * q_minus == q_minus
    assert q_plus * q_minus == z
    assert q_minus * q_plus == z
    assert q_plus + q_minus == 1
    b = 2 * q_plus
    bmp = q_plus / 2
    assert b * bmp * b == b
    assert bmp * b * bmp == bmp
    s3 = 2 * q_plus - q_minus / 5
    s3mp = q_plus / 2 - 5 * q_minus
    assert s3 * s3mp * s3 == s3
    assert s3mp * s3 * s3mp == s3mp
    print("PASS: galgebra exact symbolic Cl(1,1) MP lanes")

    print("HARTWIG1976_SVD_MP_BORDER_CLIFFORD_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
