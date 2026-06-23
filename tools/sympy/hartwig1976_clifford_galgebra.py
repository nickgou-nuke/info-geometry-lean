#!/usr/bin/env python3
"""
Clifford / galgebra certificate for the Hartwig 1976 Drazin split.

The principal idempotent `Z = 1 - A A#` behaves like a spectral Clifford
projector.  In `Cl(1,1)`, the null generators generate complementary
idempotents p_+ = e_+ e_- and p_- = e_- e_+.  This certificate checks the
strict projector algebra in both `clifford` and `galgebra`.
"""

from __future__ import annotations


def main() -> None:
    print("=== Hartwig 1976 Clifford / galgebra projector certificate ===")

    from clifford import Cl

    layout, blades = Cl(1, 1)
    e1, e2 = blades["e1"], blades["e2"]
    n_plus = (e1 + e2) / 2
    n_minus = (e1 - e2) / 2
    assert n_plus * n_plus == 0
    assert n_minus * n_minus == 0
    assert n_plus * n_minus + n_minus * n_plus == 1

    p_plus = n_plus * n_minus
    p_minus = n_minus * n_plus
    assert p_plus * p_plus == p_plus
    assert p_minus * p_minus == p_minus
    assert p_plus * p_minus == 0
    assert p_minus * p_plus == 0
    assert p_plus + p_minus == 1
    print("PASS: clifford Cl(1,1) null generators produce complementary idempotents")

    from galgebra.ga import Ga

    built = Ga.build("g1 g2", g=[1, -1])
    if len(built) == 2:
        _, basis = built
        g1, g2 = basis
    else:
        g1, g2 = built[1], built[2]

    m_plus = (g1 + g2) / 2
    m_minus = (g1 - g2) / 2
    assert m_plus * m_plus == 0
    assert m_minus * m_minus == 0
    assert m_plus * m_minus + m_minus * m_plus == 1
    q_plus = m_plus * m_minus
    q_minus = m_minus * m_plus
    assert q_plus * q_plus == q_plus
    assert q_minus * q_minus == q_minus
    assert q_plus * q_minus == 0
    assert q_minus * q_plus == 0
    assert q_plus + q_minus == 1
    print("PASS: galgebra Cl(1,1) projector algebra matches Hartwig spectral split")

    print("HARTWIG1976_CLIFFORD_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
