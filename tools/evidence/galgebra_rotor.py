#!/usr/bin/env python3
"""
Clifford / galgebra Verification: Krein Space Rotors & Trace-freeness

This script verifies:
1. The Clifford algebra Cl(1,1) representation of the doubled Krein carrier.
2. The trace-free property of the bivector generator.
3. The Krein metric-preserving property (rotor condition) of the exponentiated bivector.
"""

from galgebra.ga import Ga
import sympy as sp

def verify_clifford_krein():
    print("--- Verifying Cl(1,1) Krein Rotors & Bivectors ---")
    
    # Build Cl(1,1) where e1^2 = 1 and e2^2 = -1 (Krein signature)
    ga, e1, e2 = Ga.build("e1 e2", g=[1, -1])
    
    # 1. Verify metric properties
    check_e1_sq = (e1 * e1).scalar()
    check_e2_sq = (e2 * e2).scalar()
    print(f"  e1^2 = {check_e1_sq}, e2^2 = {check_e2_sq}")
    assert check_e1_sq == 1, "e1^2 must be 1"
    assert check_e2_sq == -1, "e2^2 must be -1 (Krein metric negative sector)"
    
    # 2. Bivector generator
    B = e1 ^ e2
    print(f"  Bivector generator B = e1 ^ e2: {B}")
    
    # Bivector square
    B_sq = (B * B).scalar()
    print(f"  B^2 = {B_sq}")
    assert B_sq == 1, "B^2 must be 1 in Cl(1,1)"
    
    # 3. Unitary Rotor in Krein Space (preserves the metric)
    theta = sp.symbols('theta', real=True)
    # Exponentiate the bivector: R = cosh(theta) + sinh(theta) * B
    R = sp.cosh(theta) + sp.sinh(theta) * B
    print(f"  Rotor R = exp(theta * B): {R}")
    
    # Reversion of R (conjugate)
    R_rev = R.rev()
    print(f"  Reverted Rotor R~: {R_rev}")
    
    # Verify the rotor condition: R * R~ = 1 (preserves the Krein inner product)
    R_R_rev = (R * R_rev).simplify()
    print(f"  R * R~ = {R_R_rev}")
    assert R_R_rev == 1, "Rotor must preserve the Krein metric (R * R~ = 1)!"
    
    # 4. Trace-freeness
    # In Clifford algebra, any element without a scalar component is trace-free.
    # We verify that B is purely grade 2 (no scalar part).
    assert B.grade(0) == 0, "Bivector must be trace-free (no grade-0 scalar component)!"
    
    print("  ✅ Clifford Cl(1,1) Krein rotor verification passed.")

if __name__ == "__main__":
    print("============================================================")
    print("CLIFFORD GALGEBRA EVIDENCE: KREIN SPACE ROTORS")
    print("============================================================")
    verify_clifford_krein()
    print("============================================================")
