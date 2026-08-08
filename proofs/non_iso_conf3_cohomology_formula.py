#!/usr/bin/env python3
"""Symbolic formalization of the non-isotropic Conf_3(C^D) candidates.

This script checks the two finite Poincaré-polynomial branches and the arity-3
cooperad edge bookkeeping:

- product/Leray:  (1+t)^3 (1+t^(D-1))^2  (total rank 32)
- OS-alpha:      (1+3t+2t^2)(1+t^(D-1))^2 (total rank 24)

It prints explicit formulas for sample even dimensions and verifies the combinatoric
cooperad split counts for the three arity-3 decompositions.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    t = sp.symbols("t")

    def product_poly(D: int) -> sp.Expr:
        return (1 + t) ** 3 * (1 + t ** (D - 1)) ** 2

    def os_alpha_poly(D: int) -> sp.Expr:
        return (1 + 3 * t + 2 * t**2) * (1 + t ** (D - 1)) ** 2

    def rank_of(poly: sp.Expr) -> int:
        return int(sp.expand(poly).subs(t, 1))

    # Three-point edges and arity-3 block decompositions.
    edges = ["12", "13", "23"]
    decomps = {
        "pair12_3": {"internal": "12", "outer": ["13", "23"]},
        "pair13_2": {"internal": "13", "outer": ["12", "23"]},
        "pair23_1": {"internal": "23", "outer": ["12", "13"]},
    }

    for D in (4, 6, 8, 10):
        p = sp.expand(product_poly(D))
        q = sp.expand(os_alpha_poly(D))
        rp = rank_of(p)
        ro = rank_of(q)
        assert rp == 32
        assert ro == 24
        assert rp - ro == 8
        print(f"D={D}")
        print("  P_product(t) =", p)
        print("  P_osAlpha(t)=", q)
        print("  rank(P)-rank(OS)=", rp - ro)

    print("\nArity-3 cooperad edge split audit:")
    for name, v in decomps.items():
        internal = v["internal"]
        outer = v["outer"]
        assert internal in edges
        assert len(outer) == 2
        assert internal not in outer
        print(f"  {name}: internal = {internal}; outer = {outer}")

    print("cooperad_partition_counts: internal=1, outer=2 for each block decomposition")
    print("non_iso_conf3_cohomology_formula.py: formalization checks passed")


if __name__ == "__main__":
    main()