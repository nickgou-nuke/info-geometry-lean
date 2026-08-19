#!/usr/bin/env python3
"""Finite audit for the 3-point non-isotropic de Rham/cooperad candidates.

This deliberately distinguishes two candidate finite signatures:

* product/Leray candidate: (1+t)^3(1+t^(D-1))^2, total rank 32;
* OS-alpha candidate: (1+3t+2t^2)(1+t^(D-1))^2, total rank 24.

The script does not prove the analytic de Rham theorem; it audits the finite
bookkeeping that the Lean file proves.
"""

import sympy as sp


def coeffs(poly, t):
    expanded = sp.expand(poly)
    return {int(k): int(v) for (k,), v in sp.Poly(expanded, t).terms()}


def main() -> None:
    t = sp.symbols("t")
    for D in (4, 6, 8, 10):
        product = (1 + t) ** 3 * (1 + t ** (D - 1)) ** 2
        os_alpha = (1 + 3 * t + 2 * t**2) * (1 + t ** (D - 1)) ** 2
        assert sp.expand(product.subs(t, 1)) == 32
        assert sp.expand(os_alpha.subs(t, 1)) == 24
        assert sp.expand(product.subs(t, 1) - os_alpha.subs(t, 1)) == 8
        print(f"D={D}")
        print("  product/Leray P(t) =", sp.expand(product))
        print("  OS-alpha    P(t) =", sp.expand(os_alpha))

    edges = ["12", "13", "23"]
    decomps = {"pair12_3": "12", "pair13_2": "13", "pair23_1": "23"}
    for name, internal in decomps.items():
        assert internal in edges
        outer = [e for e in edges if e != internal]
        assert len(outer) == 2

    print("non_iso_conf3_derham_cooperad.py: finite candidate/cooperad audit passed")
    print("Actual de Rham comparison and relation choice remain deferred_interfaces.")


if __name__ == "__main__":
    main()
