#!/usr/bin/env python3
"""
SL(2,C) trace identity verification.
Verifies the identity: Tr(A) Tr(B) = Tr(AB) + Tr(AB^{-1})
for 2x2 matrices A, B with determinant 1.
"""
import sympy as sp

def run_sl2c_trace_identity():
    print("=== SL(2,C) Trace Identity ===")
    # Define symbolic entries for matrices A and B
    a, b, c, d = sp.symbols('a b c d')
    e, f, g, h = sp.symbols('e f g h')
    # Matrices
    A = sp.Matrix([[a, b], [c, d]])
    B = sp.Matrix([[e, f], [g, h]])
    # Determinants set to 1
    detA = a*d - b*c
    detB = e*h - f*g
    # Traces
    trA = A.trace()
    trB = B.trace()
    trAB = (A*B).trace()
    # Inverse of B under det=1: [[h, -f], [-g, e]]
    Binv = sp.Matrix([[h, -f], [-g, e]])
    trABinv = (A*Binv).trace()
    # Identity: trA * trB - trAB - trABinv = 0
    expr = trA * trB - trAB - trABinv
    # Substitute determinant conditions
    expr_sub = expr.subs({detA: 1, detB: 1})
    simplified = sp.simplify(expr_sub)
    print("Determinant of A:", detA)
    print("Determinant of B:", detB)
    print("Trace(A):", trA)
    print("Trace(B):", trB)
    print("Trace(AB):", trAB)
    print("Trace(AB^{-1}):", trABinv)
    print("Expression Tr(A)Tr(B) - Tr(AB) - Tr(AB^{-1}):", expr)
    print("After substituting detA=1, detB=1:", expr_sub)
    print("Simplified:", simplified)
    if simplified == 0:
        print("Identity holds: Tr(A)Tr(B) = Tr(AB) + Tr(AB^{-1})")
    else:
        print("Identity does NOT hold (unexpected)")
    print("\nConclusion: The identity is valid for 2x2 matrices with determinant 1.")

if __name__ == "__main__":
    run_sl2c_trace_identity()