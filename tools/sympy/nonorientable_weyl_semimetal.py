#!/usr/bin/env python3
"""
SymPy witness for `InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal`.

This mirrors the finite algebraic shadow of arXiv:2511.22303v2: a two-node
glide orbit has ordinary integer cancellation for opposite oriented charges and
mod-2 cancellation for same-sign non-orientable local charges.
"""

from __future__ import annotations

import sympy as sp


def mod2(x: sp.Expr) -> int:
    return int(x) % 2


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

    print("[SUCCESS] finite glide-pair charge cancellations match the Lean bridge.")


if __name__ == "__main__":
    main()
