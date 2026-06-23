#!/usr/bin/env python3
"""
Clifford / galgebra certificate for the GNSD nilpotent lane.

The GNSD separates a zero-Jordan nilpotent sector from an invertible regular
sector.  Here `Cl(1,1)` supplies the strict square-zero nilpotent support:
`N = e_+ + e_-` with `N^2 = 0`, so unipotent shears truncate exactly.
"""

from __future__ import annotations


def main() -> None:
    print("=== GNSD Clifford / galgebra nilpotent certificate ===")

    from clifford import Cl

    _, blades = Cl(1, 1)
    e1, e2 = blades["e1"], blades["e2"]
    n = e1 + e2
    assert e1 * e1 == 1
    assert e2 * e2 == -1
    assert e1 * e2 + e2 * e1 == 0
    assert n * n == 0
    t = 3
    assert (1 + t * n) * (1 - t * n) == 1
    assert (1 - t * n) * (1 + t * n) == 1
    print("PASS: clifford Cl(1,1) square-zero nilpotent and unipotent inverse")

    from galgebra.ga import Ga

    built = Ga.build("e1 e2", g=[1, -1])
    if len(built) == 2:
        _, basis = built
        g1, g2 = basis
    else:
        g1, g2 = built[1], built[2]
    ng = g1 + g2
    assert (g1 * g1).scalar() == 1
    assert (g2 * g2).scalar() == -1
    assert g1 * g2 + g2 * g1 == 0
    assert ng * ng == 0
    print("PASS: galgebra Cl(1,1) square-zero nilpotent support")

    print("GNSD_CLIFFORD_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
