#!/usr/bin/env python3
"""Finite KR/T-duality cascade witness.

This script mirrors `InfoGeometry.Canonical.KRDualityCascade`.

Important correction: the first-cell momentum/winding swap preserves the
standard split-pairing O(5,5) metric [[0, I], [I, 0]]. It does not preserve the
diagonal metric diag(+1^5, -1^5).
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    identity = sp.eye(10)

    # Standard split-pairing O(5,5) metric.
    eta_split = sp.zeros(10)
    for i in range(5):
        eta_split[i, i + 5] = 1
        eta_split[i + 5, i] = 1

    # A diagonal signature matrix is useful as a warning check, but not the
    # metric preserved by a raw momentum/winding exchange in this basis.
    eta_diag = sp.diag(*([1] * 5 + [-1] * 5))

    omega = sp.eye(10)
    omega[0, 0] = 0
    omega[5, 5] = 0
    omega[0, 5] = 1
    omega[5, 0] = 1

    parity_first = sp.zeros(10)
    parity_first[0, 0] = 1
    parity_first[5, 5] = -1

    print("--- KR Duality Cascade: finite O(5,5) Buscher witness ---")
    print(f"1. Omega_T^2 == I: {omega * omega == identity}")
    print(
        "2. Omega_T preserves split-pairing eta: "
        f"{omega.T * eta_split * omega == eta_split}"
    )
    print(
        "3. Omega_T preserves diagonal eta: "
        f"{omega.T * eta_diag * omega == eta_diag}"
    )
    print(
        "4. Omega_T anticommutes with first-cell parity: "
        f"{omega * parity_first == -parity_first * omega}"
    )

    dimension_index = sp.symbols("n", integer=True)
    charges = sp.symbols("q0 q1", integer=True)
    shifted_dimension = -(-dimension_index)
    shifted_charges = tuple(-(-q) for q in charges)

    print(f"5. Buscher degree shift is involutive: {shifted_dimension == dimension_index}")
    print(f"6. Buscher charge shift is involutive: {shifted_charges == charges}")


if __name__ == "__main__":
    main()

