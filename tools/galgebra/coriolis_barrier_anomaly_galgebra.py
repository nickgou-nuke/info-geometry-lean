#!/usr/bin/env python3
"""
Verify split Clifford Cl(1,1) relations using GAlgebra:
- Timelike generator e1 (e1^2 = 1) and Spacelike generator e2 (e2^2 = -1)
- Bivector e12 = e1 * e2 and its square (e12^2 = 1)
- Anticommutation of e1 and e2
"""
from galgebra.ga import Ga

def verify_galgebra():
    print("====================================================")
    print("Verifying Cl(1,1) relations using GAlgebra...")
    # Define Cl(1,1) with signature g = [1, -1]
    ga = Ga('e1 e2', g=[1, -1])
    e1, e2 = ga.mv_basis
    
    # Check generator squares
    e1_sq = e1 * e1
    e2_sq = e2 * e2
    print(f"e1^2 = {e1_sq}")
    print(f"e2^2 = {e2_sq}")
    assert str(e1_sq) == "1"
    assert str(e2_sq) == "-1"
    
    # Bivector I = e1 * e2
    I = e1 * e2
    print(f"Bivector I = {I}")
    I2 = I * I
    print(f"I^2 = {I2}")
    assert str(I2) == "1", "Split signature bivector square must be 1!"
    
    # Anticommutation check
    anticomm = e1 * e2 + e2 * e1
    print(f"Anticommutator {e1} * {e2} + {e2} * {e1} = {anticomm}")
    assert str(anticomm) == "0"
    
    print("Verification successful: Cl(1,1) split relations hold.")
    print("====================================================")

if __name__ == "__main__":
    try:
        verify_galgebra()
    except Exception as e:
        print(f"GAlgebra check failed: {e}")
