#!/usr/bin/env python3
"""
Clifford / galgebra certificate for the nilpotent lane in Greville 1973.

The exact Greville packet has a square-zero nilpotent zero-root sector.  In
`Cl(1,1)`, the null generator `n_+` models that lane: `n_+^2 = 0`, its Drazin
inverse is zero at index 2, and the complementary idempotents split the regular
and nilpotent sectors.
"""

from __future__ import annotations


def main() -> None:
    print("=== Greville 1973 Clifford / galgebra certificate ===")

    from clifford import Cl

    layout, blades = Cl(1, 1)
    e1, e2 = blades["e1"], blades["e2"]
    n_plus = (e1 + e2) / 2
    n_minus = (e1 - e2) / 2
    zero = 0 * n_plus

    assert n_plus != zero
    assert n_plus * n_plus == zero
    assert n_plus * zero == zero * n_plus
    assert zero * n_plus * zero == zero
    assert (n_plus * n_plus * n_plus) * zero == n_plus * n_plus

    p_plus = n_plus * n_minus
    p_minus = n_minus * n_plus
    assert p_plus * p_plus == p_plus
    assert p_minus * p_minus == p_minus
    assert p_plus * p_minus == zero
    assert p_minus * p_plus == zero
    assert p_plus + p_minus == 1
    print("PASS: clifford Cl(1,1) square-zero lane and projector split")

    from galgebra.ga import Ga

    built = Ga.build("g1 g2", g=[1, -1])
    if len(built) == 2:
        _, basis = built
        g1, g2 = basis
    else:
        g1, g2 = built[1], built[2]

    m_plus = (g1 + g2) / 2
    m_minus = (g1 - g2) / 2
    z = 0 * m_plus
    assert m_plus != z
    assert m_plus * m_plus == z
    assert m_plus * z == z * m_plus
    assert z * m_plus * z == z
    assert (m_plus * m_plus * m_plus) * z == m_plus * m_plus
    q_plus = m_plus * m_minus
    q_minus = m_minus * m_plus
    assert q_plus * q_plus == q_plus
    assert q_minus * q_minus == q_minus
    assert q_plus * q_minus == z
    assert q_minus * q_plus == z
    assert q_plus + q_minus == 1
    print("PASS: galgebra Cl(1,1) square-zero lane and projector split")

    print("GREVILLE1973_CLIFFORD_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
