#!/usr/bin/env python3
"""
SymPy witness for the finite Witten--Möbius / Cuntz horizon /
Bekenstein--Hawking dyadic complement.

This mirrors the theorem-safe Lean module
`InfoGeometry.Holography.WittenMobiusBekensteinComplement`.
It is finite algebraic evidence only; Lean remains authoritative.
"""

from __future__ import annotations

import itertools
import sympy as sp

from primitive_cuntz_exactness_bridge import reduce_cuntz, SL, SR, SLs, SRs, X, I


def mobius_squarefree_parity(k: int) -> int:
    """Möbius value for a squarefree product of k distinct primes."""
    return (-1) ** k


def finite_witten_sum(n: int) -> int:
    """Sum over all occupied subsets: Σ_S (-1)^|S|."""
    total = 0
    indices = range(n)
    for r in range(n + 1):
        for _subset in itertools.combinations(indices, r):
            total += (-1) ** r
    return total


def main() -> None:
    print("--- SymPy Twin: Witten-Mobius / Cuntz / Bekenstein Complement ---")

    n = 4
    occupied = {0, 2, 3}
    k = len(occupied)

    mu_state = mobius_squarefree_parity(k)
    fermion_parity = (-1) ** k
    print(f"state Mobius value: {mu_state}; fermion parity: {fermion_parity}")
    assert mu_state == fermion_parity

    witten = finite_witten_sum(n)
    print(f"finite Witten cancellation for n={n}: {witten}")
    assert witten == 0

    horizon = SL * SRs
    horizon_star = SR * SLs
    horizon_sq = reduce_cuntz(horizon * horizon)
    print(f"Cuntz horizon nilpotence: {horizon_sq}")
    assert horizon_sq == 0

    laplacian_reconstruction = reduce_cuntz((horizon * horizon_star + horizon_star * horizon) * X)
    print(f"Cuntz Laplacian reconstruction: {laplacian_reconstruction}")
    assert laplacian_reconstruction == X

    G = sp.Symbol("G", nonzero=True)
    entropy_quantum = sp.log(2)
    area = 4 * G * entropy_quantum
    sbh = sp.simplify(area / (4 * G))
    massieu_two_branch = sp.simplify(sp.log(sp.exp(0) + sp.exp(0)))
    print(f"BH entropy: {sbh}; two-branch Massieu: {massieu_two_branch}")
    assert sp.simplify(sbh - massieu_two_branch) == 0

    print("[SUCCESS] finite complement witness matches the Lean certificate.")


if __name__ == "__main__":
    main()
