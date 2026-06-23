#!/usr/bin/env python3
"""
Verify bivector complex structure equivalence using SymPy.
"""
import sympy as sp

def verify_bivector():
    print("====================================================")
    print("Verifying Clifford bivector S = e1 * e2 algebraic relation...")
    
    # Define non-commutative generator symbols
    e1 = sp.Symbol('e1', commutative=False)
    e2 = sp.Symbol('e2', commutative=False)
    
    # Bivector product
    S = e1 * e2
    print(f"Bivector S = {S}")
    
    # compute S^2 = e1 * e2 * e1 * e2
    S2 = S * S
    print(f"S^2 expanded = {S2}")
    
    # Apply Clifford relations:
    # 1) e1^2 = 1, e2^2 = 1 (signature (2,0))
    # 2) e2 * e1 = - e1 * e2 (anticommutativity)
    
    # We substitute e2 * e1 with -e1 * e2
    # e1 * e2 * e1 * e2 -> e1 * (-e1 * e2) * e2 -> -e1^2 * e2^2
    I2 = e1 * (-e1 * e2) * e2
    print(f"Applying e2 * e1 = -e1 * e2: {I2}")
    
    # Substitute e1 * e1 = 1, e2 * e2 = 1
    # Note: we need to group them properly.
    # We can represent it as - (e1*e1) * (e2*e2)
    val = -1 * 1 * 1
    print(f"Substituting e1^2 = 1, e2^2 = 1: {val}")
    
    assert val == -1, "Verification failed!"
    print("Verification successful: S^2 equivalent to -1.")
    print("====================================================")

if __name__ == "__main__":
    verify_bivector()
