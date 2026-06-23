#!/usr/bin/env python3
"""
Clifford / galgebra certificate for the Barbaresco 2020 `SO(2,1)` lane.

The paper identifies the `SU(1,1)` coadjoint orbit with the `SO(2,1)`
hyperboloid model.  This script checks the corresponding real Clifford
support in `Cl(2,1)`: the bivectors close with the `so(2,1)` signs.
"""

from __future__ import annotations


def main() -> None:
    print("=== Barbaresco 2020 Clifford / galgebra certificate ===")

    from clifford import Cl

    layout, blades = Cl(2, 1)
    e1, e2, e3 = blades["e1"], blades["e2"], blades["e3"]
    assert e1 * e1 == 1
    assert e2 * e2 == 1
    assert e3 * e3 == -1
    assert e1 * e2 + e2 * e1 == 0
    assert e1 * e3 + e3 * e1 == 0
    assert e2 * e3 + e3 * e2 == 0

    B12 = e1 * e2
    B13 = e1 * e3
    B23 = e2 * e3
    assert B12 * B13 - B13 * B12 == -2 * B23
    assert B12 * B23 - B23 * B12 == 2 * B13
    assert B13 * B23 - B23 * B13 == 2 * B12
    print("PASS: clifford Cl(2,1) bivectors close as so(2,1)")

    from galgebra.ga import Ga

    built = Ga.build("e1 e2 e3", g=[1, 1, -1])
    if len(built) == 2:
        _, basis = built
        g1, g2, g3 = basis
    else:
        g1, g2, g3 = built[1], built[2], built[3]

    assert (g1 * g1).scalar() == 1
    assert (g2 * g2).scalar() == 1
    assert (g3 * g3).scalar() == -1
    assert g1 * g2 + g2 * g1 == 0
    assert g1 * g3 + g3 * g1 == 0
    assert g2 * g3 + g3 * g2 == 0
    print("PASS: galgebra Cl(2,1) metric and anticommutation")

    print("BARBARESCO2020_CLIFFORD_GALGEBRA_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
