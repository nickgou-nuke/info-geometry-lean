#!/usr/bin/env python3
"""
SymPy witness for the local Araki--Itakura--Saito collapse lane.

This script verifies a concrete scalar/model-side interface for the claims used by
`InfoGeometry.Canonical.ArakiItakuraSaitoCollapse`:

1. Itakura--Saito divergence is scale invariant:
     D_IS(λx || λy) = D_IS(x || y)
2. It vanishes on the diagonal:
     D_IS(x || x) = 0
3. For the Burg/log specialization against the vacuum 1,
     D_IS(exp(K) || 1) = exp(K) - K - 1
4. In the nilpotent parabolic sector N² = 0, exp(tN) = I + tN.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    print("=== SYMPY: ARAKI-ITAKURA-SAITO COLLAPSE WITNESS ===")

    x, y, lam, K, t = sp.symbols("x y lam K t", positive=True, real=True)

    D_is = sp.simplify(x / y - sp.log(x / y) - 1)
    print("\n1. Itakura-Saito divergence D_IS(x || y):")
    sp.pprint(D_is)

    scale_invariant = sp.simplify((lam * x) / (lam * y) - sp.log((lam * x) / (lam * y)) - 1 - D_is)
    print("\n2. Scale invariance residual D_IS(λx || λy) - D_IS(x || y):")
    sp.pprint(scale_invariant)
    assert scale_invariant == 0

    diagonal = sp.simplify(D_is.subs(x, y))
    print("\n3. Diagonal specialization D_IS(x || x):", diagonal)
    assert diagonal == 0

    burg_form = sp.simplify(D_is.subs({x: sp.exp(K), y: 1}))
    expected_burg = sp.simplify(sp.exp(K) - K - 1)
    print("\n4. Burg specialization D_IS(exp(K) || 1):")
    sp.pprint(burg_form)
    print("Expected Burg form:")
    sp.pprint(expected_burg)
    assert sp.simplify(burg_form - expected_burg) == 0

    burg_series = sp.series(expected_burg, K, 0, 4).removeO()
    print("Series at K = 0 up to cubic order:")
    sp.pprint(burg_series)

    a, b = sp.symbols("a b", real=True)
    N = sp.Matrix([[a * b, -a**2], [b**2, -a * b]])
    N_sq = sp.simplify(N * N)
    print("\n5. Nilpotent parabolic generator N:")
    sp.pprint(N)
    print("N^2:")
    sp.pprint(N_sq)
    assert N_sq == sp.zeros(2, 2)

    I = sp.eye(2)
    exp_tN = I + t * N
    print("exp(tN) in the nilpotent sector:")
    sp.pprint(exp_tN)
    det_exp_tN = sp.simplify(exp_tN.det())
    print("det(exp(tN)) =", det_exp_tN)
    assert det_exp_tN == 1

    print("\nCONCLUSION:")
    print("  - D_IS is scale invariant.")
    print("  - D_IS vanishes on the diagonal.")
    print("  - The Burg/log specialization is exp(K) - K - 1.")
    print("  - The parabolic nilpotent sector satisfies exp(tN) = I + tN with determinant 1.")


if __name__ == "__main__":
    main()
