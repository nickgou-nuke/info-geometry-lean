#!/usr/bin/env python3
"""
Verify tripotent/projector relations and the Zorn matrix sandwich formula using SymPy.
"""
import sympy as sp

def verify_tripotent_projector():
    print("====================================================")
    print("Verifying tripotent/projector isomorphism and sandwich formulas...")
    
    # 1. Projectors
    OP1 = sp.Matrix([[1, 0], [0, 0]])
    OP2 = sp.Matrix([[0, 0], [0, 1]])
    I = sp.Matrix([[1, 0], [0, 1]])
    
    # Projector properties
    assert OP1 * OP1 == OP1
    assert OP2 * OP2 == OP2
    assert OP1 * OP2 == sp.zeros(2, 2)
    
    # Tripotent
    T = OP1 - OP2
    T2 = T * T
    T3 = T2 * T
    assert T3 == T, "Failed T^3 = T"
    print("1. Tripotency holds: T^3 = T")
    
    # Projector reconstruction from T
    P_plus = (T2 + T) / 2
    P_minus = (T2 - T) / 2
    P_zero = I - T2
    
    assert P_plus == OP1
    assert P_minus == OP2
    assert P_zero == sp.zeros(2, 2)
    print("2. Projectors reconstructed from T verified.")
    
    # 3. Sandwich formula verification
    a, b, x, y = sp.symbols('a b x y')
    X = sp.Matrix([[a, x], [y, b]])
    
    sandwich_12 = OP1 * X * OP2
    sandwich_21 = OP2 * X * OP1
    
    assert sandwich_12 == sp.Matrix([[0, x], [0, 0]])
    assert sandwich_21 == sp.Matrix([[0, 0], [y, 0]])
    print(f"3. Sandwich OP1 * X * OP2 = {sandwich_12}")
    print(f"   Sandwich OP2 * X * OP1 = {sandwich_21}")
    print("SymPy: Zorn matrix sandwich verification successful.")
    print("====================================================")

if __name__ == "__main__":
    verify_tripotent_projector()
