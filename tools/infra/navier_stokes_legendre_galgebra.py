#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
GAlgebra/Clifford sketch for the Navier–Stokes–Legendre theorem.
We illustrate the algebraic structure that underlies the geometric‑algebra
interpretation of the complex structure used in the MH‑formulation:
the bivector e1^e2 squares to -1, providing a geometric imaginary unit.
"""

from galgebra.ga import Ga

# Build a 2‑dimensional Euclidean geometric algebra
# Basis vectors e1, e2 with metric g = [[1,0],[0,1]]
ga = Ga('e1 e2', g=[1, 1])
e1, e2 = ga.mv()

# The unit bivector (plane element)
B = e1 ^ e2   # wedge product

# In 2‑D Euclidean GA, (e1^e2)^2 = -1
B_sq = B * B

print("Bivector B = e1^e2")
print("B =", B)
print("B^2 =", B_sq)
print("Expected: -1")
# Extract the scalar part (should be -1)
if hasattr(B_sq, 'scalar'):
    print("Scalar part of B^2:", B_sq.scalar)
else:
    # If it's already a scalar:
    print("B^2 as scalar:", B_sq)

# Optional: show that exp(B) = cos(1) + B*sin(1) (Taylor series truncated)
# We leave this as a comment; full verification would require series expansion.
print("\nRemark: In this algebra, exp(B) = cos(1) + B*sin(1) encodes a unit rotor.")
print("This geometric imaginary unit underlies the MH‑formulation's complex structure.")
print("The rotor R = exp(-B*theta/2) generates rotations that correspond to")
print("the phase factor e^{theta I/2} appearing in the modular Hamiltonian.")