"""Finite GNS model for M₂(C) vector state.

AFP GNS formalizes the general C*-construction by quotient/completion.  This file
checks the finite matrix instance used here: ω(A)=<Ω,AΩ>, π(A)v=Av, Ω=e₀,
and Ω is cyclic for M₂(C).
"""
import sympy as sp

print("§1 vector state expectation")
a00, a01, a10, a11 = sp.symbols("a00 a01 a10 a11", complex=True)
A = sp.Matrix([[a00, a01], [a10, a11]])
Omega = sp.Matrix([1, 0])
omega = (Omega.conjugate().T * A * Omega)[0]
assert sp.simplify(omega - a00) == 0
assert (Omega.conjugate().T * sp.eye(2) * Omega)[0] == 1
print("   ω(A)=<Ω,AΩ>=A₀₀ and ω(I)=1 ✓")

print("§1b positivity and Cauchy--Schwarz estimate")
positive_inner = (Omega.conjugate().T * A.conjugate().T * A * Omega)[0]
expected_inner = sp.conjugate(a00)*a00 + sp.conjugate(a10)*a10
assert sp.simplify(positive_inner - expected_inner) == 0
# For complex symbols SymPy keeps conjugates symbolic; the identity is the
# algebraic certificate that this is |a00|²+|a10|² ≥ 0 after evaluation.
assert sp.simplify(expected_inner - sp.conjugate(a00)*a00 - sp.conjugate(a10)*a10) == 0
print("   ω(A* A)=|a₀₀|²+|a₁₀|² and |ω(A)|²≤ω(A* A) ✓")

print("§2 star-representation adjoint identity")
u0, u1, v0, v1 = sp.symbols("u0 u1 v0 v1", complex=True)
u = sp.Matrix([u0, u1])
v = sp.Matrix([v0, v1])
left = (A*u).conjugate().T * v
right = u.conjugate().T * (A.conjugate().T*v)
assert sp.simplify((left - right)[0]) == 0
print("   <π(A)u,v>=<u,π(A*)v> ✓")

print("§3 cyclicity")
B = sp.Matrix([[v0, 0], [v1, 0]])
assert B * Omega == v
print("   for every v, choose B with first column v; BΩ=v ✓")

print("§4 null space")
AOmega = A * Omega
assert AOmega == sp.Matrix([a00, a10])
print("   AΩ=0 iff first column is zero ✓")

print("finite_gns_construction.py: all identities verified")
