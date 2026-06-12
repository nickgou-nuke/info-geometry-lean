#!/usr/bin/env python3
"""
SymPy witness for `InfoGeometry.Canonical.DrazinModularPersistence`.

Lean now defines positivity of a real expectation state as the genuine predicate
`∀ A, 0 ≤ φ(A* A)`.  This script gives a finite real-matrix witness using the
trace state `φ(X) = tr(X) / n`, where `A*` is transpose.
"""

from __future__ import annotations

import sympy as sp


def phi(x: sp.Matrix) -> sp.Expr:
    """Normalized finite trace state."""
    return sp.simplify(sp.trace(x) / x.rows)


def main() -> None:
    print("--- SymPy Twin: Drazin Modular Persistence Positivity ---")

    a, b, c, d = sp.symbols("a b c d", real=True)
    A = sp.Matrix([[a, b], [c, d]])
    positive_readout = sp.expand(phi(A.T * A))

    l1, l2 = sp.symbols("lambda_1 lambda_2", real=True)
    Lambda = sp.Matrix([[l1, 0], [0, l2]])
    leakage_energy = sp.expand(phi(Lambda.T * Lambda))

    print(f"φ(A^T A) = {positive_readout}")
    print(f"leakage energy φ(Λ^T Λ) = {leakage_energy}")

    assert positive_readout == (a**2 + b**2 + c**2 + d**2) / 2
    assert leakage_energy == (l1**2 + l2**2) / 2

    # Concrete nonnegative sample points.
    sample = positive_readout.subs({a: 1, b: -2, c: 3, d: 4})
    sample_energy = leakage_energy.subs({l1: -5, l2: 7})
    print(f"sample positivity readout: {sample}")
    print(f"sample leakage energy: {sample_energy}")
    assert sample >= 0
    assert sample_energy >= 0

    print("[SUCCESS] finite positive expectation witness matches the Lean predicate.")


if __name__ == "__main__":
    main()
