#!/usr/bin/env python3
"""Symbolic audit for the KL symmetric/antisymmetric split.

This is a finite algebra witness only.  It verifies the decomposition laws used
by the Lean owner and a local Taylor parity model for the information-geometric
metric/current readout.
"""

import sympy as sp


def check(expr: sp.Expr, label: str) -> None:
    reduced = sp.simplify(expr)
    if reduced != 0:
        raise AssertionError(f"{label} failed: {reduced}")
    print(f"ok: {label}")


def main() -> None:
    d_pq, d_qp = sp.symbols("D_pq D_qp")
    d_sym = (d_pq + d_qp) / 2
    d_anti = (d_pq - d_qp) / 2

    check(d_pq - (d_sym + d_anti), "forward divergence reconstructs")
    check(d_qp - (d_sym - d_anti), "reverse divergence reconstructs")

    swapped_sym = d_sym.xreplace({d_pq: d_qp, d_qp: d_pq})
    swapped_anti = d_anti.xreplace({d_pq: d_qp, d_qp: d_pq})
    check(swapped_sym - d_sym, "symmetric part is swap-invariant")
    check(swapped_anti + d_anti, "antisymmetric part flips sign")
    check(d_anti.subs(d_pq, d_qp), "antisymmetric part vanishes at balance")

    # A local Bregman/KL expansion around a reference point has an even
    # quadratic metric term and an odd cubic skewness/current term.  The
    # half-sum cancels the odd part; the half-difference isolates it.
    eps, g, c, k4 = sp.symbols("eps g c k4")
    forward = g * eps**2 / 2 + c * eps**3 / 6 + k4 * eps**4 / 24
    reverse = g * eps**2 / 2 - c * eps**3 / 6 + k4 * eps**4 / 24
    local_sym = sp.expand((forward + reverse) / 2)
    local_anti = sp.expand((forward - reverse) / 2)

    check(local_sym - (g * eps**2 / 2 + k4 * eps**4 / 24),
          "symmetric local expansion cancels cubic term")
    check(local_anti - c * eps**3 / 6,
          "antisymmetric local expansion is cubic current")

    # Finite two-state KL formulas obey the same purely algebraic split.
    p, q = sp.symbols("p q", positive=True)
    kl_pq = p * sp.log(p / q) + (1 - p) * sp.log((1 - p) / (1 - q))
    kl_qp = q * sp.log(q / p) + (1 - q) * sp.log((1 - q) / (1 - p))
    finite_sym = (kl_pq + kl_qp) / 2
    finite_anti = (kl_pq - kl_qp) / 2
    check(sp.expand(kl_pq - (finite_sym + finite_anti)),
          "two-state KL forward reconstructs")
    check(sp.expand(kl_qp - (finite_sym - finite_anti)),
          "two-state KL reverse reconstructs")


if __name__ == "__main__":
    main()
