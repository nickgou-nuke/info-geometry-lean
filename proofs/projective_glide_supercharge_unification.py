"""SymPy witness: projective glide as spatial supercharge.

Both structures are square roots of translations:
  g^2 = reciprocal translation,
  Q^2 = Hamiltonian/even translation,
  q^2 = 0 in the boundary nilpotent degeneration.
"""

import sympy as sp

print("§1  Projective momentum glide square")
kx, ky = sp.symbols("kx ky")
def g(k):
    x, y = k
    return (-x, y + sp.Rational(1, 2))
def T(k):
    x, y = k
    return (x, y + 1)
assert g(g((kx, ky))) == T((kx, ky))
print("   g²=T_rec ✓")

print("§2  Supercharge square")
Q = sp.Matrix([[0, 1], [1, 0]])
H = sp.eye(2)
assert Q**2 == H
assert Q*Q + Q*Q == 2*H
print("   Q²=H and {Q,Q}=2H ✓")

print("§3  Boundary nilpotent degeneration")
q = sp.Matrix([[0, 1], [0, 0]])
assert q**2 == sp.zeros(2)
print("   q²=0 ✓")

print()
print("projective_glide_supercharge_unification.py: All identities verified")
