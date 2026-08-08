"""Abelian-group arithmetic behind the Cuntz K0 torsion relation.

If [1] = (N+1)[1], then N[1] = 0.  This is only the algebraic torsion
consequence of the projection partition, not a computation of the full K-group.
"""
import sympy as sp

N, u = sp.symbols("N u", integer=True)

print("§1 torsion relation")
expr = sp.expand((N + 1) * u - u)
assert sp.simplify(expr - N * u) == 0
print("   (N+1)u=u implies Nu=0 by cancellation ✓")

print("§2 O2 special case")
expr_o2 = sp.expand(2 * u - u)
assert expr_o2 == u
print("   u=2u implies u=0 by cancellation ✓")

print("cuntz_k0_torsion_relation.py: all identities verified")
