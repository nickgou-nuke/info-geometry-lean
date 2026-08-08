#!/usr/bin/env python3
"""Conditional E-polynomial algebra for the D=4 point-count fingerprint.

This script performs only the algebraic substitution P(p) -> P(uv).  The
geometric comparison (polynomial count over prime powers + purity/mixed Tate +
trace formula) is not proved here.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    T, u, v = sp.symbols("T u v")
    P = T**2 * (T - 1) ** 2 * (T + 1) * (T**3 - 2 * T**2 - T + 3)
    expanded = T**8 - 3 * T**7 + 7 * T**5 - 4 * T**4 - 4 * T**3 + 3 * T**2
    assert sp.expand(P - expanded) == 0

    Ec = sp.factor(P.subs(T, u * v))
    Ec_expanded = sp.expand(Ec)
    assert Ec.subs({u: 1, v: 1}) == 0

    for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]:
        assert int(P.subs(T, p)) == p**2 * (p - 1) ** 2 * (p + 1) * (p**3 - 2 * p**2 - p + 3)
        assert int(Ec.subs({u: 1, v: p})) == int(P.subs(T, p))

    print("non_iso_conf3_quadric_d4_epolynomial.py: conditional E-polynomial algebra passed")
    print("P(T) =")
    sp.pprint(sp.factor(P))
    print("expanded P(T) =")
    sp.pprint(expanded)
    print("Candidate E_c(u,v) = P(uv) =")
    sp.pprint(Ec)
    print("Expanded candidate E_c(u,v) =")
    sp.pprint(Ec_expanded)
    print("Geometric interpretation remains conditional on purity/comparison.")


if __name__ == "__main__":
    main()
