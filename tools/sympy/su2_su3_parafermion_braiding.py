#!/usr/bin/env python3
"""SymPy twin for finite parafermion-style Artin braid matrices.

Verified here:
- the explicit 3x3 Burau-style matrices satisfy sigma_1 sigma_2 sigma_1 =
  sigma_2 sigma_1 sigma_2.

Not verified here:
- physical SU(2)/SU(3) representation theory;
- Lorentz covariance;
- parafermionic quantum statistics in a Hilbert-space model.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    print("--- SymPy Twin: Finite Parafermion Artin Braid Relation ---")

    t = sp.Symbol("t")

    sigma_1 = sp.Matrix(
        [
            [1 - t, t, 0],
            [1, 0, 0],
            [0, 0, 1],
        ]
    )
    sigma_2 = sp.Matrix(
        [
            [1, 0, 0],
            [0, 1 - t, t],
            [0, 1, 0],
        ]
    )

    lhs = sp.simplify(sigma_1 * sigma_2 * sigma_1)
    rhs = sp.simplify(sigma_2 * sigma_1 * sigma_2)

    assert lhs == rhs

    print(f"sigma_1:\n{sigma_1}")
    print(f"sigma_2:\n{sigma_2}")
    print("Artin relation sigma_1 sigma_2 sigma_1 = sigma_2 sigma_1 sigma_2: OK")
    print("[SUCCESS] finite Artin braid matrix identity verified.")


if __name__ == "__main__":
    main()
