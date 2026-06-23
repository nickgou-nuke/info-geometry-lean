#!/usr/bin/env python3
"""
Verify LogCFT nilpotent shear N^2 = 0 using clifford and galgebra.
We represent the nilpotent shear as a null vector u in Cl(1,1).
"""
import clifford
from galgebra.ga import Ga

def verify_with_clifford():
    print("====================================================")
    print("Verifying LogCFT nilpotent shear N with clifford...")
    
    # Define Cl(1,1)
    layout, blades = clifford.Cl(1, 1)
    e1 = blades['e1']
    e2 = blades['e2']
    
    # Null generator u = 0.5 * (e1 + e2)
    # e1^2 = 1, e2^2 = -1 (signature (1,1))
    u = 0.5 * (e1 + e2)
    print(f"Null vector u = {u}")
    
    # Check u^2 = 0
    u2 = u * u
    print(f"u^2 = {u2}")
    
    # Convert scalar part to float
    u2_scalar = float(u2(0))
    assert abs(u2_scalar) < 1e-10, "u^2 is not zero in clifford!"
    print("clifford: Null vector u^2 = 0 verified successfully.")

def verify_with_galgebra():
    print("\nVerifying LogCFT nilpotent shear N with galgebra...")
    
    # Define Cl(1,1) with signature [1, -1]
    ga = Ga('e1 e2', g=[1, -1])
    e1, e2 = ga.mv_basis
    
    # Null generator u = 0.5 * (e1 + e2)
    u = 0.5 * (e1 + e2)
    print(f"Null vector u = {u}")
    
    # Check u^2 = 0
    u2 = u * u
    print(f"u^2 = {u2}")
    
    # Simplify and assert it is 0
    u2_str = str(u2.simplify())
    assert u2_str == "0", "u^2 is not zero in galgebra!"
    print("galgebra: Null vector u^2 = 0 verified successfully.")
    print("====================================================")

if __name__ == "__main__":
    try:
        verify_with_clifford()
    except Exception as e:
        print(f"Clifford check failed: {e}")
        
    try:
        verify_with_galgebra()
    except Exception as e:
        print(f"GAlgebra check failed: {e}")
        
