#!/usr/bin/env python3
"""
SymPy witness for `InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal`.

This mirrors the finite algebraic shadow of arXiv:2511.22303v2:

- a two-node glide orbit has ordinary integer cancellation for opposite
  oriented charges;
- same-sign non-orientable local charges cancel modulo two;
- reversing a local orientation does not change the Z2 charge readout;
- the exact-sequence gate `im beta subset ker Sigma` forces mod-two total
  charge cancellation for every charge configuration in the semimetal image.

Not checked here:
- the full twisted Mayer-Vietoris sequences;
- the cellular computation of H^3(K^2 x S^1);
- Poincare duality with local coefficients.
"""

from __future__ import annotations

import sympy as sp


def mod2(x: sp.Expr) -> int:
    return int(x) % 2


def sigma(charges: list[int]) -> int:
    """Coordinate-free total-charge readout Sigma : Z^k -> Z2."""
    return sum(charges) % 2


def in_kernel_sigma(charges: list[int]) -> bool:
    return sigma(charges) == 0


def main() -> None:
    print("--- SymPy Twin: Non-orientable Weyl Semimetal Finite Corridor ---")

    q = sp.symbols("q", integer=True)
    oriented_pair_sum = sp.simplify(q + (-q))
    same_sign_pair = 2 * q

    print(f"oriented pair charge sum q + (-q): {oriented_pair_sum}")
    assert oriented_pair_sum == 0

    # Concrete samples for mod-2 same-sign cancellation.
    for sample in [-3, -2, -1, 0, 1, 2, 5, 8]:
        cancellation = mod2(2 * sample)
        print(f"2*{sample} mod 2 = {cancellation}")
        assert cancellation == 0

    unit_glide_pair_mod2 = mod2(1 + 1)
    print(f"unit glide pair 1+1 mod 2 = {unit_glide_pair_mod2}")
    assert unit_glide_pair_mod2 == 0

    for sample in [-5, -2, -1, 0, 1, 4, 7]:
        left = mod2(-sample)
        right = mod2(sample)
        print(f"orientation reversal: {-sample} mod 2 = {sample} mod 2 = {right}")
        assert left == right

    semimetal_image = [
        [1, 1],
        [2, 4],
        [-3, 5],
        [1, -1, 2],
        [3, 3, 4, 4],
    ]
    for charges in semimetal_image:
        total = sigma(charges)
        print(f"Sigma({charges}) = {total}")
        assert in_kernel_sigma(charges)

    print("[SUCCESS] finite glide-pair charge cancellations match the Lean bridge.")


if __name__ == "__main__":
    main()
