"""
GAlgebra/Clifford analysis of split signature Cl(1,1)

This script uses the galgebra package (or clifford package) to analyze
the split Clifford algebra Cl(1,1) with signature (+,-).

Install dependencies:
  pip install galgebra  # or: pip install clifford

Verification targets:
1. Generator relations: e₁²=1, e₂²=-1, {e₁,e₂}=0
2. Bivector structure: e₁₂ = e₁∧e₂, e₁₂²=1
3. Null vectors: v = e₁+e₂ satisfies v²=0
4. Tripotent grading operator
"""

import numpy as np
from typing import Tuple, List

print("="*60)
print("GAlgebra/Cl(1,1) Split Signature Analysis")
print("="*60)

# Method 1: Using clifford package (more modern)
try:
    import clifford as cf
    from clifford import Cl
    
    print("\n[Method 1: clifford package]")
    
    # Create Cl(1,1) with signature [1, -1]
    layout, blades = Cl(1, 1)  # signature (1 positive, 1 negative)
    
    e1 = blades['e1']
    e2 = blades['e2']
    e12 = blades['e12']
    
    print(f"Generated Cl(1,1) with basis: {list(blades.keys())}")
    
    # Verify relations
    print("\n--- Verifying Cl(1,1) Relations ---")
    
    # e₁² = +1
    e1_sq = (e1 * e1).value
    print(f"e₁² = {e1_sq} (expected: +1)")
    assert np.isclose(e1_sq[0], 1.0), f"e₁² should be +1, got {e1_sq}"
    
    # e₂² = -1
    e2_sq = (e2 * e2).value
    print(f"e₂² = {e2_sq} (expected: -1)")
    assert np.isclose(e2_sq[0], -1.0), f"e₂² should be -1, got {e2_sq}"
    
    # Anticommute: {e₁, e₂} = 0
    anticomm = (e1 * e2 + e2 * e1).value
    print(f"{{e₁, e₂}} = {anticomm} (expected: 0)")
    assert np.allclose(anticomm, 0), f"Anticommutator should be 0, got {anticomm}"
    
    # Bivector
    print(f"\ne₁₂ = e₁∧e₂ = {e12}")
    e12_sq = (e12 * e12).value
    print(f"e₁₂² = {e12_sq} (expected: +1)")
    assert np.isclose(e12_sq[0], 1.0), f"e₁₂² should be +1, got {e12_sq}"
    
    # Null vector
    v = e1 + e2
    v_sq = (v * v).value
    print(f"\nNull vector v = e₁ + e₂")
    print(f"v² = {v_sq} (expected: 0)")
    assert np.allclose(v_sq, 0), f"Null vector should square to 0, got {v_sq}"
    
    # Grading/tripotent operator
    chi = e12  # Grading operator
    chi2 = (chi * chi).value
    print(f"\nGrading operator χ = e₁₂")
    print(f"χ² = {chi2} (expected: +1)")
    print(f"χ³ = χ (tripotent property satisfied)")
    
    # Eigenvalues of χ are {+1, -1}
    # In matrix representation, χ = diag(1, -1)
    
    print("\n✓ All Cl(1,1) relations verified!")
    
except ImportError:
    print("clifford package not available, using manual matrix representation")

# Method 2: Explicit matrix representation (always works)
print("\n" + "="*60)
print("[Method 2: Explicit Matrix Representation]")
print("="*60)

# Gamma matrices for Cl(1,1)
gamma1 = np.array([[0, 1],
                   [1, 0]], dtype=float)  # γ₁² = +I

gamma2 = np.array([[0, -1],
                   [1, 0]], dtype=float)  # γ₂² = -I

gamma12 = gamma1 @ gamma2  # Bivector

print("\nGamma matrices:")
print(f"γ₁ = \n{gamma1}")
print(f"γ₂ = \n{gamma2}")
print(f"γ₁₂ = \n{gamma12}")

# Verify relations
print("\n--- Verifying Matrix Relations ---")

# γ₁² = I
g1_sq = gamma1 @ gamma1
print(f"γ₁² = \n{g1_sq}")
assert np.allclose(g1_sq, np.eye(2)), "γ₁² should be I"

# γ₂² = -I
g2_sq = gamma2 @ gamma2
print(f"γ₂² = \n{g2_sq}")
assert np.allclose(g2_sq, -np.eye(2)), "γ₂² should be -I"

# Anticommute
anticomm_mat = gamma1 @ gamma2 + gamma2 @ gamma1
print(f"{{γ₁, γ₂}} = \n{anticomm_mat}")
assert np.allclose(anticomm_mat, np.zeros((2,2))), "Should anticommute"

# γ₁₂² = I
g12_sq = gamma12 @ gamma12
print(f"γ₁₂² = \n{g12_sq}")
assert np.allclose(g12_sq, np.eye(2)), "γ₁₂² should be I"

# Null vector
v_mat = gamma1 + gamma2
v_sq_mat = v_mat @ v_mat
print(f"\nNull vector v = γ₁ + γ₂")
print(f"v² = \n{v_sq_mat}")
assert np.allclose(v_sq_mat, np.zeros((2,2))), "Null vector should square to 0"

# Eigenvalue analysis
print("\n--- Eigenvalue Analysis ---")

# Grading operator eigenvalues
eigenvalues_chi = np.linalg.eigvals(gamma12)
print(f"Eigenvalues of χ = γ₁₂: {eigenvalues_chi}")
print("Expected: [+1, -1]")

# Verify tripotent property χ³ = χ
chi3 = gamma12 @ gamma12 @ gamma12
print(f"\nχ³ = \n{chi3}")
print(f"χ = \n{gamma12}")
assert np.allclose(chi3, gamma12), "Should satisfy χ³ = χ"

# Null vector eigenvalues (should be 0, 0 since v²=0)
eigenvalues_v = np.linalg.eigvals(v_mat)
print(f"\nEigenvalues of null vector v: {eigenvalues_v}")
print("Expected: [0, 0] (nilpotent)")

print("\n" + "="*60)
print("✓ ALL VERIFICATIONS PASSED")
print("="*60)

# Connection to Lean formalization
print("\n[Connection to Lean Formalization]")
print("The matrix representation matches:")
print("  InfoGeometry.Clifford.GammaMatrices.coordinateMatrixEquiv")
print("  InfoGeometry.Clifford.Cl11CoordinateAlgebra")
print("\nSignature: Cl(1,1) split (+, -)")
print("NOT Euclidean Cl(3,0) or Cl(0,3)")