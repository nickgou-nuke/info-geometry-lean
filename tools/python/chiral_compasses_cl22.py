#!/usr/bin/env python3
"""
Verification of Cl(1,1) x Cl(1,1) = Cl(2,2)
Two Chiral Compasses
"""
import numpy as np

def commutator(A, B):
    return A @ B - B @ A

def anticommutator(A, B):
    return A @ B + B @ A

def verify_clifford_isomorphism():
    print("=== Cl(1,1) x Cl(1,1) = Cl(2,2) Isomorphism ===")
    
    # Cl(1,1) is isomorphic to M_2(R)
    # Generators e_1 (square +1) and e_2 (square -1)
    # We can choose:
    # e_1 = sigma_z = [[1, 0], [0, -1]]
    # e_2 = i * sigma_y = [[0, 1], [-1, 0]]
    # Wait, e_2^2 = -I
    
    e1 = np.array([[1, 0], [0, -1]], dtype=float)
    e2 = np.array([[0, 1], [-1, 0]], dtype=float)
    
    # Verify Cl(1,1) rules
    assert np.allclose(e1 @ e1, np.eye(2))
    assert np.allclose(e2 @ e2, -np.eye(2))
    assert np.allclose(anticommutator(e1, e2), np.zeros((2,2)))
    print("  [PASS] Cl(1,1) generators established (left and right compasses)")
    
    # To form Cl(2,2), we tensor two copies of Cl(1,1).
    # We need 4 generators: 2 squaring to +1, 2 squaring to -1.
    # Let E_i be the generators of Cl(2,2)
    # Using the standard graded tensor product construction:
    # Gamma_1 = e1 \otimes I
    # Gamma_2 = e2 \otimes I
    # Gamma_3 = (e1*e2) \otimes e1
    # Gamma_4 = (e1*e2) \otimes e2
    # Let's check this. e1*e2 = [[0, 1], [1, 0]] = sigma_x
    
    e12 = e1 @ e2
    assert np.allclose(e12 @ e12, np.eye(2)) # square is +1 since e1 e2 e1 e2 = -e1 e1 e2 e2 = -(1)(-1) = 1
    
    I2 = np.eye(2)
    
    # Left chiral compass (first sheet)
    G1 = np.kron(e1, I2)
    G2 = np.kron(e2, I2)
    
    # Right chiral compass (second sheet) graded by volume of first
    G3 = np.kron(e12, e1)
    G4 = np.kron(e12, e2)
    
    generators = [G1, G2, G3, G4]
    
    # Verify they anti-commute and have correct squares
    # G1^2 = +1
    # G2^2 = -1
    # G3^2 = (e12)^2 \otimes e1^2 = (+1) * (+1) = +1
    # G4^2 = (e12)^2 \otimes e2^2 = (+1) * (-1) = -1
    # So we have two +1s and two -1s, which is Cl(2,2).
    
    signature = [1, -1, 1, -1]
    
    passed = True
    for i in range(4):
        sq = generators[i] @ generators[i]
        if not np.allclose(sq, signature[i] * np.eye(4)):
            passed = False
            print(f"Generator {i+1} square is wrong.")
            
        for j in range(i+1, 4):
            ac = anticommutator(generators[i], generators[j])
            if not np.allclose(ac, np.zeros((4,4))):
                passed = False
                print(f"Generators {i+1} and {j+1} do not anti-commute.")
                
    if passed:
        print("  [PASS] Cl(2,2) generated via graded tensor product Cl(1,1) \hat{\otimes} Cl(1,1)")
        print("  Signature obtained: (+, -, +, -)")
        print("  The left chiral compass provides (G1, G2)")
        print("  The right chiral compass provides (G3, G4)")
        print("\nConclusion: The decomposition perfectly models the two independent null/chiral")
        print("sheets (left-movers and right-movers) combining into the (2,2) conformal spacetime.")

if __name__ == "__main__":
    verify_clifford_isomorphism()
