#!/usr/bin/env python3
"""
GAlgebra Verification: Cl(1,1) ⊗ Cl(1,1) ≅ Cl(2,2)
"""
from sympy import symbols
from galgebra.ga import Ga

print("=== GAlgebra: Chiral Compasses ===")

# Define Cl(2,2) geometric algebra
# Signature: e1^2 = 1, e2^2 = -1, e3^2 = 1, e4^2 = -1
coords = symbols('x y z w')
ga22 = Ga('e_1 e_2 e_3 e_4', g=[1, -1, 1, -1], coords=coords)
e1, e2, e3, e4 = ga22.mv()

# Verify base properties
assert (e1*e1).obj == 1
assert (e2*e2).obj == -1
assert (e3*e3).obj == 1
assert (e4*e4).obj == -1

# Left Compass
L1 = e1
L2 = e2

# Right Compass (graded by left volume)
vol_L = e1 * e2
R1 = vol_L * e3
R2 = vol_L * e4

# Check Right Compass signature (should be 1, -1)
assert (R1*R1).obj == 1
assert (R2*R2).obj == -1

# Check anti-commutation of Right Compass
assert (R1*R2 + R2*R1).obj == 0

# Check that Left and Right compasses anti-commute
assert (L1*R1 + R1*L1).obj == 0
assert (L1*R2 + R2*L1).obj == 0
assert (L2*R1 + R1*L2).obj == 0
assert (L2*R2 + R2*L2).obj == 0

print("  [PASS] Cl(2,2) splits geometrically into two Cl(1,1) chiral compasses.")
