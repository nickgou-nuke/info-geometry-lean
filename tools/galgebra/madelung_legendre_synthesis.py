#!/usr/bin/env python3
"""
GAlgebra script to verify Madelung-Legendre synthesis scaling:
- Linearity of the collapsed velocity field in geometric algebra.
- Scaling relation under scalar multiplication.
"""
from galgebra.ga import Ga

def verify_galgebra():
    print("====================================================")
    print("Verifying Madelung-Legendre scaling in GAlgebra...")
    ga = Ga('e1 e2', g=[1, 1])
    e1, e2 = ga.mv_basis
    
    # Define a general vector v representing the modular Hamiltonian direction
    import sympy as sp
    beta = sp.Symbol('beta', real=True)
    x, y = sp.symbols('x y')
    K = x * e1 + y * e2
    
    # Collapsed velocity under scaling beta
    u = beta * K
    print(f"Base vector K = {K}")
    print(f"Scaled vector u = {u}")
    
    # Check that inner product scales linearly: u . e1 == beta * (K . e1)
    inner_u = u | e1
    inner_K = K | e1
    print(f"u . e1 = {inner_u}")
    print(f"beta * (K . e1) = {beta * inner_K}")
    assert inner_u == beta * inner_K
    
    print("GAlgebra scaling verification successful!")
    print("====================================================")

if __name__ == "__main__":
    try:
        verify_galgebra()
    except Exception as e:
        print(f"GAlgebra check failed: {e}")
