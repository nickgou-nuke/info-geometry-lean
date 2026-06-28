#!/usr/bin/env sage
# -*- coding: utf-8 -*-
"""
SageMath Verification: Cl(1,1) ⊗ Cl(1,1) ≅ Cl(2,2)
"""
from sage.all import *

print("=== SageMath: Chiral Compasses Cl(1,1) x Cl(1,1) ===")

# 1. Define the quadratic forms
# Cl(1,1) signature (+, -)
Q11 = DiagonalQuadraticForm(QQ, [1, -1])

# Cl(2,2) signature (+, -, +, -)
Q22 = DiagonalQuadraticForm(QQ, [1, -1, 1, -1])

# 2. Build the Clifford algebras
C11.<e1, e2> = CliffordAlgebra(Q11)
C22.<E1, E2, E3, E4> = CliffordAlgebra(Q22)

# Verify single compass generator squares
assert e1^2 == 1
assert e2^2 == -1
assert e1*e2 == -e2*e1

# 3. Graded Tensor Product Mapping
# Left compass -> E1, E2
# Right compass -> graded by volume of left (E1*E2) -> E1*E2*E3, E1*E2*E4

# Define the images of the right compass generators:
G3 = E1 * E2 * E3
G4 = E1 * E2 * E4

# Verify the right compass generators satisfy Cl(1,1) relations
assert G3^2 == 1   # (E1 E2 E3)^2 = E1 E2 E3 E1 E2 E3 = - E1^2 E2^2 E3^2 = -(1)(-1)(1) = 1
assert G4^2 == -1  # (E1 E2 E4)^2 = E1 E2 E4 E1 E2 E4 = - E1^2 E2^2 E4^2 = -(1)(-1)(-1) = -1
assert G3*G4 == -G4*G3

# Verify left and right compasses commute (in the graded sense, meaning the mapped elements anti-commute?)
# Actually, the generators of the two tensor factors must anti-commute in the Clifford algebra!
# Let's check anti-commutation:
assert E1 * G3 == -G3 * E1
assert E1 * G4 == -G4 * E1
assert E2 * G3 == -G3 * E2
assert E2 * G4 == -G4 * E2

print("  [PASS] Cl(1,1) x Cl(1,1) graded tensor maps to Cl(2,2)")
print("  [PASS] Left compass: (E1, E2)")
print("  [PASS] Right compass: (E1*E2*E3, E1*E2*E4)")
