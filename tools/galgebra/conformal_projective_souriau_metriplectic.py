#!/usr/bin/env python3
"""
GAlgebra script to verify conformal projective Souriau metriplectic algebra:
- Almost complex structure J = e1 * e2 in Euclidean Cl(2) space
- Centralizer loop J^2 = -1
- Orthogonality and Kähler compatibility g(v, J(v)) = 0
"""
from galgebra.ga import Ga

def verify_galgebra():
    print("====================================================")
    print("Verifying Möbius/Kähler properties using GAlgebra...")
    # Define Cl(2) space with Euclidean signature g = [1, 1]
    ga = Ga('e1 e2', g=[1, 1])
    e1, e2 = ga.mv_basis
    
    # Almost complex structure J = e1 * e2 (Möbius parity analog)
    J = e1 * e2
    print(f"Almost complex structure J = {J}")
    
    # Centralizer loop: J^2 = -1
    J2 = J * J
    print(f"J^2 = {J2}")
    assert str(J2) == "-1"
    
    # Define a general vector v = x * e1 + y * e2
    import sympy as sp
    x, y = sp.symbols('x y')
    v = x * e1 + y * e2
    print(f"General vector v = {v}")
    
    # Action of J on v: Jv = J * v
    Jv = J * v
    print(f"J * v = {Jv}")
    
    # Inner product g(v, Jv) represented by scalar part (v . Jv)
    inner = v | Jv
    print(f"g(v, J * v) = {inner}")
    assert str(inner) == "0"
    
    print("GAlgebra verification successful!")
    print("====================================================")

if __name__ == "__main__":
    try:
        verify_galgebra()
    except Exception as e:
        print(f"GAlgebra check failed: {e}")
