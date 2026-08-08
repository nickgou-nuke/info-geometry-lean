"""SymPy witness: modular conjugation J as glide/CPT reflection.

Checks:
- J K J = -K for a boost/modular Hamiltonian K;
- J exp(tK) J = exp(-tK) on the diagonal boost flow;
- the same matrix J implements the Klein glide word J Δ J Δ=1.
"""

import sympy as sp

print("§1  J flips modular Hamiltonian")
v, t = sp.symbols("v t", real=True)
J = sp.Matrix([[0, 1], [1, 0]])
K = v * sp.Matrix([[1, 0], [0, -1]])
assert J**2 == sp.eye(2)
assert sp.simplify(J * K * J + K) == sp.zeros(2)
print("   J²=1 and J K J=-K ✓")

print("§2  J reverses modular flow")
Delta_t = sp.diag(sp.exp(t*v), sp.exp(-t*v))
Delta_minus_t = sp.diag(sp.exp(-t*v), sp.exp(t*v))
assert sp.simplify(J * Delta_t * J - Delta_minus_t) == sp.zeros(2)
print("   J exp(tK) J = exp(-tK) ✓")

print("§3  CPT/glide Klein word")
assert sp.simplify(J * Delta_t * J * Delta_t - sp.eye(2)) == sp.zeros(2)
print("   J Δ J Δ=1: modular CPT equals orientation-reversing glide skeleton ✓")

print()
print("modular_glide_cpt_identity.py: All identities verified")
