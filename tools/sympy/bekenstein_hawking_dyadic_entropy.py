#!/usr/bin/env python3
"""
SymPy witness for the Bekenstein--Hawking/dyadic entropy bridge.

This mirrors the theorem-safe Lean file
`InfoGeometry.Holography.BekensteinHawkingDyadicEntropy`:

* S_BH = A / (4G)
* one dyadic/two-branch entropy quantum = log(2)
* if A = 4G log(2), then S_BH = log(2)
* if A_n = 4G n log(2), then S_BH = n log(2)

It is a scalar algebra witness only; it does not prove a full black-hole,
AdS/CFT, or KMS-classification theorem.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    print("--- SymPy Twin: Bekenstein-Hawking Dyadic Entropy ---")

    G = sp.Symbol("G", nonzero=True)
    n = sp.Symbol("n", integer=True, nonnegative=True)
    entropy_quantum = sp.log(2)

    area_one = 4 * G * entropy_quantum
    sbh_one = sp.simplify(area_one / (4 * G))
    print(f"one-bit horizon entropy: {sbh_one}")
    assert sp.simplify(sbh_one - entropy_quantum) == 0

    area_n = 4 * G * n * entropy_quantum
    sbh_n = sp.simplify(area_n / (4 * G))
    print(f"n-bit dyadic horizon entropy: {sbh_n}")
    assert sp.simplify(sbh_n - n * entropy_quantum) == 0

    # Symmetric two-branch Gibbs/Massieu readout: log(exp(0)+exp(0)) = log(2).
    massieu_two_branch = sp.simplify(sp.log(sp.exp(0) + sp.exp(0)))
    print(f"two-branch Massieu readout: {massieu_two_branch}")
    assert sp.simplify(massieu_two_branch - entropy_quantum) == 0

    print("[SUCCESS] scalar Bekenstein-Hawking and dyadic Massieu calibrations match.")


if __name__ == "__main__":
    main()
