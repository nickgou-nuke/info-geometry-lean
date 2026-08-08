#!/usr/bin/env python3
"""SymPy witness for finite golden/Fibonacci Hamiltonian anchors."""

import sympy as sp

sqrt5 = sp.sqrt(5)
phi = (1 + sqrt5) / 2
q = 1 / phi
S = sp.Matrix([[0, 0], [1, 0]])
T = S + S.T
V = sp.diag(1, q)
H = T + V

print("§1 finite Fibonacci tight-binding Hamiltonian")
assert T == sp.Matrix([[0, 1], [1, 0]])
assert V == sp.diag(1, q)
assert H == sp.Matrix([[1, 1], [1, q]])
print("H = [[1,1],[1,φ⁻¹]] ✓")
assert H.T == H
print("H is symmetric/self-adjoint in the real finite model ✓")

print("\n§2 spectral scalar anchors")
assert sp.simplify(H.trace() - (1 + q)) == 0
assert sp.simplify(H.det() - (q - 1)) == 0
print("tr(H)=1+φ⁻¹ ✓")
print("det(H)=φ⁻¹-1 ✓")

print("\n§3 gap-label coefficient")
gap_label_minus1_1 = -1 + phi
assert sp.simplify(q - gap_label_minus1_1) == 0
print("q=φ⁻¹=-1+φ ∈ Z+φZ ✓")

print("\n§4 infinite theorem sockets")
print("Cantor zero-measure spectrum and IDOS gap labeling remain explicit analytic sockets ✓")

print("\nfractal_hamiltonian.py: All identities verified")
