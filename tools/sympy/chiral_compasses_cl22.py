#!/usr/bin/env python3
"""
SymPy Verification: Cl(1,1) ⊗ Cl(1,1) ≅ Cl(2,2)
Symbolic matrix verification.
"""
import sympy as sp

print("=== SymPy: Chiral Compasses ===")

# Left Compass generators (Cl(1,1) as M_2(R))
L1_base = sp.Matrix([[1, 0], [0, -1]])
L2_base = sp.Matrix([[0, 1], [-1, 0]])

assert L1_base**2 == sp.eye(2)
assert L2_base**2 == -sp.eye(2)
assert L1_base*L2_base + L2_base*L1_base == sp.zeros(2)

I2 = sp.eye(2)

# Tensor product to build Cl(2,2)
def kronecker(A, B):
    return sp.matrix_multiply_elementwise(A, B) # Wait, sp doesn't have a simple kronecker product for Matrix. 
    # Let's do it manually.
    pass

def kron(A, B):
    # A is 2x2, B is 2x2
    # Returns 4x4
    import numpy as np
    # Convert to numpy, use np.kron, convert back to sympy
    A_np = np.array(A.tolist(), dtype=object)
    B_np = np.array(B.tolist(), dtype=object)
    return sp.Matrix(np.kron(A_np, B_np))

E1 = kron(L1_base, I2)
E2 = kron(L2_base, I2)

vol_L = L1_base * L2_base
E3 = kron(vol_L, L1_base)
E4 = kron(vol_L, L2_base)

generators = [E1, E2, E3, E4]
squares = [sp.eye(4), -sp.eye(4), sp.eye(4), -sp.eye(4)]

passed = True
for i in range(4):
    if generators[i]**2 != squares[i]:
        passed = False
    for j in range(i+1, 4):
        if generators[i]*generators[j] + generators[j]*generators[i] != sp.zeros(4):
            passed = False

if passed:
    print("  [PASS] SymPy symbolic Kronecker product verifies Cl(2,2) generation.")
else:
    print("  [FAIL] Matrix relations failed.")
