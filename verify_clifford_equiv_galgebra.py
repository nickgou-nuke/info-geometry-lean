#!/usr/bin/env python3
"""
Verify Clifford equivalence using GAlgebra.
"""
from galgebra.ga import Ga

def verify_galgebra():
    print("====================================================")
    print("Verifying Clifford bivector square using GAlgebra...")
    # Define Cl(2,0)
    ga = Ga('e1 e2', g=[1, 1])
    e1, e2 = ga.mv_basis
    # Bivector I = e1 * e2
    I = e1 * e2
    print(f"Bivector I = {I}")
    I2 = I * I
    print(f"I^2 = {I2}")
    assert str(I2) == "-1", "Verification failed!"
    print("Verification successful: I^2 is -1.")
    print("====================================================")

if __name__ == "__main__":
    try:
        verify_galgebra()
    except Exception as e:
        print(f"GAlgebra check failed: {e}")
