#!/usr/bin/env python3
"""
SymPy witness for the KL / Jeffreys decomposition.

This script checks two conservative facts:

1. any pair of scalar KL readouts splits exactly into symmetric and
   antisymmetric parts;
2. on the balanced binary slice `p = 1/2 + u`, `q = 1/2 - u`, the KL readout
   is even in `u`, so the odd terms vanish and the leading term is quadratic.

The Lean side records the same split as a scalar bridge; the Fisher/Bures
interpretation remains owned by the existing information-geometry modules.
"""

from __future__ import annotations

import sympy as sp


def require_zero(name: str, expr: sp.Expr) -> None:
    simplified = sp.factor(sp.cancel(sp.simplify(expr)))
    if simplified != 0:
        raise AssertionError(f"{name} failed: {simplified}")
    print(f"[ok] {name}")


def main() -> None:
    print("=== SYMPY: KL / JEFFREYS DECOMPOSITION WITNESS ===")

    d_pq, d_qp = sp.symbols("D_pq D_qp", real=True)
    sym_part = sp.simplify((d_pq + d_qp) / 2)
    asym_part = sp.simplify((d_pq - d_qp) / 2)

    require_zero("forward reconstruction", d_pq - (sym_part + asym_part))
    require_zero("backward reconstruction", d_qp - (sym_part - asym_part))
    a, b = sp.symbols("a b", real=True)
    swapped_sym = sym_part.subs({d_pq: a, d_qp: b}).xreplace({a: b, b: a})
    swapped_asym = asym_part.subs({d_pq: a, d_qp: b}).xreplace({a: b, b: a})
    require_zero("Jeffreys swap invariance", swapped_sym - sym_part.subs({d_pq: a, d_qp: b}))
    require_zero(
        "antisymmetric swap parity",
        swapped_asym + asym_part.subs({d_pq: a, d_qp: b}),
    )

    print("\n1. Abstract split")
    print("  D_sym = (D_pq + D_qp)/2")
    print("  D_antisym = (D_pq - D_qp)/2")

    u = sp.symbols("u", real=True)
    p = sp.Rational(1, 2) + u
    q = sp.Rational(1, 2) - u

    kl_pq = sp.simplify(
        p * sp.log(p / q) + (1 - p) * sp.log((1 - p) / (1 - q))
    )
    kl_qp = sp.simplify(
        q * sp.log(q / p) + (1 - q) * sp.log((1 - q) / (1 - p))
    )

    balanced_sym = sp.simplify((kl_pq + kl_qp) / 2)
    balanced_asym = sp.simplify((kl_pq - kl_qp) / 2)

    print("\n2. Balanced binary slice p=1/2+u, q=1/2-u:")
    print("  Jeffreys series =", sp.series(balanced_sym, u, 0, 8).removeO())
    print("  antisymmetric series =", sp.series(balanced_asym, u, 0, 8).removeO())

    series_sym = sp.expand(sp.series(balanced_sym, u, 0, 8).removeO())
    series_asym = sp.expand(sp.series(balanced_asym, u, 0, 8).removeO())

    for power in [1, 3, 5, 7]:
        require_zero(f"balanced Jeffreys odd term u^{power}", series_sym.coeff(u, power))
        require_zero(f"balanced antisym odd term u^{power}", series_asym.coeff(u, power))

    print("[ok] balanced Jeffreys leading quadratic coefficient =", series_sym.coeff(u, 2))
    require_zero("balanced antisymmetric part vanishes", balanced_asym)

    print("\nCONCLUSION:")
    print("  - The exact KL split into symmetric and antisymmetric parts holds.")
    print("  - On the balanced slice, the Jeffreys part is even and starts quadratically.")
    print("  - The antisymmetric current vanishes on the balanced slice, matching")
    print("    the detailed-balance/equilibrium limit used by the Lean bridges.")


if __name__ == "__main__":
    main()
