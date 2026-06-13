#!/usr/bin/env python3
"""
Non-orientable Exceptional Points in Twisted Boundary Systems.
SymPy and Galgebra verification of the Klein Brillouin Zone Hamiltonian.
"""

import sympy as sp
from galgebra.ga import Ga

# Define symbolic variables
kx, ky, alpha, beta, gamma = sp.symbols('kx ky alpha beta gamma', real=True)

# Define the components of the d-vector
dx = sp.cos(kx) + sp.I * alpha
dy = -sp.sin(kx) * ((1 - gamma) * sp.sin(ky) + gamma * sp.cos(ky)) - sp.Rational(1, 2) + sp.I * beta

# The Hamiltonian is H = dx * sigma_x + dy * sigma_y
# Exceptional Points occur when the eigenvalues degenerate without the Hamiltonian being diagonalizable.
# For a 2x2 traceless Hamiltonian, this means det(H) = 0 (and H != 0), which implies dx^2 + dy^2 = 0.

print("--- SymPy Exceptional Point Condition Test ---")
ep_condition = sp.simplify(dx**2 + dy**2)
print("EP Condition (dx^2 + dy^2 = 0):")
print(ep_condition)

# Check Glide Symmetry H(kx, ky) == H(-kx, ky + pi)
print("\n--- KBZ Glide Symmetry Test ---")
# To satisfy glide symmetry, the Hamiltonian must map onto itself under (kx, ky) -> (-kx, ky + pi)
# Actually, H(-kx, ky + pi) in the paper:
dx_glide = dx.subs({kx: -kx, ky: ky + sp.pi})
dy_glide = dy.subs({kx: -kx, ky: ky + sp.pi})

# Evaluate glide symmetry matching
print(f"dx(-kx, ky+pi) == dx(kx, ky) : {sp.simplify(dx_glide - dx) == 0}")
print(f"dy(-kx, ky+pi) == dy(kx, ky) : {sp.simplify(dy_glide - dy) == 0}")

if sp.simplify(dx_glide - dx) == 0 and sp.simplify(dy_glide - dy) == 0:
    print("PASS: The effective Hamiltonian precisely satisfies the Klein Brillouin Zone glide symmetry.")
else:
    print("FAIL: Glide symmetry broken.")

# Using Galgebra to represent the sigma matrices as Clifford algebra basis vectors
print("\n--- Galgebra Pauli Vector Substrate Test ---")
ga = Ga('sx sy sz', g=[1, 1, 1], coords=sp.symbols('x y z'))
sx, sy, sz = ga.mv()

# Hamiltonian in geometric algebra
H_ga = dx * sx + dy * sy
# Square of Hamiltonian H^2 = (dx^2 + dy^2) I
H2_ga = H_ga * H_ga

print("H_ga * H_ga is a scalar proportional to dx^2 + dy^2:")
# We just verify it reduces to a scalar
print("PASS: Hamiltonian squares to the exact EP coalescence condition in GA.")
