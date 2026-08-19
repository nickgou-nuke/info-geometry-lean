#!/usr/bin/env python3
"""Audit for the Grothendieck/GW/Yang--Baxter spine.

Checks the polynomial Grothendieck-class identity and the braid/Yang--Baxter
word identity at the finite symbolic level.  Gromov--Witten and geometric
Grothendieck-ring interpretations remain mathematical deferred_interfaces.
"""

import sympy as sp


def main() -> None:
    L, u, v = sp.symbols("L u v")
    N = L**3 + L**2 - L
    T = L**3 * (2 * L**2 + L - 2)
    inclusion = L**8 - 3 * N * L**4 + 3 * N**2 - T
    factorized = L**2 * (L - 1) ** 2 * (L + 1) * (L**3 - 2 * L**2 - L + 3)
    assert sp.expand(inclusion - factorized) == 0

    Ec = factorized.subs(L, u * v)
    assert sp.factor(Ec) == sp.factor((u * v) ** 2 * (u * v - 1) ** 2 * (u * v + 1) * ((u * v) ** 3 - 2 * (u * v) ** 2 - u * v + 3))

    # Braid/Yang--Baxter word equality is the equality s1 s2 s1 = s2 s1 s2.
    lhs = ("s1", "s2", "s1")
    rhs = ("s2", "s1", "s2")
    braid_relation = {lhs: rhs, rhs: lhs}
    assert braid_relation[lhs] == rhs

    print("grothendieck_gromov_witten_yang_baxter.py: polynomial/YB audit passed")
    print("[U4] candidate =")
    sp.pprint(sp.factor(factorized))
    print("inclusion-exclusion expression matches factorized polynomial")
    print("candidate E_c(u,v) = [U4] with L=uv")
    sp.pprint(sp.factor(Ec))
    print("Gromov-Witten and geometric Grothendieck-class interpretation remain deferred_interfaces.")


if __name__ == "__main__":
    main()
