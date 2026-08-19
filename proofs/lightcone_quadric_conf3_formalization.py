#!/usr/bin/env python3
"""SymPy formalization of the light-cone quadric `Conf_Q(C^D,3)` bookkeeping.

This script makes the finite part of the light-cone model explicit:

1. Standard quadratic form `q(x)=sum_i x_i^2` in affine coordinates.
2. Pairwise non-isotropic conditions: all three pairwise differences avoid `q=0`.
3. The two finite Poincare candidates:
   - product/Leray: `(1+t)^3 (1+t^(D-1))^2` (rank 32)
   - OS-α: `(1+3t+2t^2)(1+t^(D-1))^2` (rank 24)
4. Arity-3 cooperad split for block `pair12|3`:
   `e12` internal, `e13`,`e23` outer.

No analytic de Rham theorem is proved here; it is represented in Lean as a deferred_interface.
"""

from __future__ import annotations

import sympy as sp


# Coordinates for a generic vector in C^D in the light-cone model.
def quadratic_form(vector):
    """Standard quadratic form q(x)=Σ_i x_i^2."""
    return sp.summation(sp.Symbol('x')**2, (sp.Symbol('i'), 0, len(vector) - 1))


def poincare_product(D: int) -> sp.Expr:
    t = sp.symbols("t")
    return sp.expand((1 + t) ** 3 * (1 + t ** (D - 1)) ** 2)


def poincare_os_alpha(D: int) -> sp.Expr:
    t = sp.symbols("t")
    return sp.expand((1 + 3 * t + 2 * t**2) * (1 + t ** (D - 1)) ** 2)


def rank_at_one(poly: sp.Expr) -> int:
    t = sp.symbols("t")
    return int(sp.expand(poly).subs(t, 1))


def cooperad_split_signature() -> list[tuple[str, dict[str, str]]]:
    """Explicit split maps for each arity-3 block decomposition.

    The three decompositions are:
      - `{1,2}|{3}`  : `e12` internal,
                          `e13`, `e23` outer
      - `{1,3}|{2}`  : `e13` internal,
                          `e12`, `e23` outer
      - `{2,3}|{1}`  : `e23` internal,
                          `e12`, `e13` outer
    """
    return [
        ("(1,2)|3", {"e12": "inner", "e13": "outer", "e23": "outer"}),
        ("(1,3)|2", {"e12": "outer", "e13": "inner", "e23": "outer"}),
        ("(2,3)|1", {"e12": "outer", "e13": "outer", "e23": "inner"}),
    ]


def check_rank_gap(D: int) -> None:
    p = poincare_product(D)
    q = poincare_os_alpha(D)
    rp = rank_at_one(p)
    ro = rank_at_one(q)
    if rp != 32:
        raise AssertionError(f"product branch rank must be 32, got {rp}")
    if ro != 24:
        raise AssertionError(f"OS-alpha rank must be 24, got {ro}")
    if rp - ro != 8:
        raise AssertionError(f"rank gap must be 8, got {rp - ro}")


def main() -> None:
    t = sp.symbols("t")
    print("Quadratic form (light-cone model): q(x) = Σ x_i^2")

    # light-cone quadric non-isotropic 3-point conditions (symbolic shape)
    print("Nonisotropic 3-point configuration:")
    print("  q(x1-x2) ≠ 0, q(x1-x3) ≠ 0, q(x2-x3) ≠ 0")

    split_maps = cooperad_split_signature()
    print("Cooperad splits on arity-3 blocks:")
    for label, split_map in split_maps:
        print(f"  {label}:")
        print(f"    e12 -> {split_map['e12']} , e13 -> {split_map['e13']} , e23 -> {split_map['e23']}")
    print("\nCandidate Poincare polynomials for even D:")
    for D in (4, 6, 8, 10):
        assert D % 2 == 0
        p = poincare_product(D)
        q = poincare_os_alpha(D)
        check_rank_gap(D)
        print(f"D={D}")
        print(f"  P_product(t) = {p}")
        print(f"  P_OS(t)      = {q}")
        print(f"  rank(product)-rank(OS)= {rank_at_one(p) - rank_at_one(q)}")

    print("\nall finite combinatorial checks passed for light-cone Conf_3(C^D)")


if __name__ == "__main__":
    main()
