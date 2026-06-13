#!/usr/bin/env python3
"""Exact symbolic check for a cubic-to-tripotent polynomial reduction.

This script verifies only the formal substitution
`T1 = 0`, `T2 = -1`, `T3 = 0` in `X^3 - T1 X^2 + T2 X - T3`.
It is not evidence for OP², E₆, topology, or a concrete Albert algebra model.
"""

import sympy as sp


def verify_freudenthal_cubic_reduction():
    print("=== FREUDENTHAL CUBIC POLYNOMIAL REDUCTION ===")

    # Define an abstract polynomial variable and invariant coefficients.
    X = sp.Symbol('X')
    T1, T2, T3 = sp.symbols('T_1 T_2 T_3')

    # Construct the generic cubic characteristic polynomial.
    cubic_poly = X**3 - T1*X**2 + T2*X - T3

    # Apply the trace-zero/tripotent coefficient specialization: T1=0, T2=-1, T3=0.
    tripotent_poly = cubic_poly.subs({T1: 0, T2: -1, T3: 0})

    # Verify algebraic identity matches X^3 - X.
    expected_poly = X**3 - X
    is_identical = sp.simplify(tripotent_poly - expected_poly) == 0

    print(f"1. Generic Freudenthal Cubic Polynomial:  {cubic_poly} = 0")
    print(f"2. Reduced Polynomial at Vacuum Locus:    {tripotent_poly} = 0")
    print(f"3. Strict equivalence to X^3 - X:       {is_identical}")
    if not is_identical:
        raise AssertionError("cubic specialization did not reduce to X^3 - X")
    print("\n[SUCCESS] Exact polynomial reduction verified.")


if __name__ == '__main__':
    verify_freudenthal_cubic_reduction()
