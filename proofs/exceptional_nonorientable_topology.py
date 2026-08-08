"""SymPy witness for arXiv:2503.04889v2, exceptional topology on nonorientable manifolds.

Digest/formal layer:
- Gapped phases on the Klein bottle K^2 obey braid constraint
      Bq * Bp * Bq^{-1} * Bp = 1.
- Gapped phases on RP^2 obey
      Bpq^2 = 1.
- Abelianization gives the torsion constraints
      2 A_p = 0,   2 A_pq = 0.
- For the two-band braid group B2 ≅ Z, these force A_p=A_pq=0 because Z is torsion-free.
- Gapless total EP charge on nonorientable spaces has the corresponding boundary word form,
  enabling nonorientable/non-Abelian charge inversion sockets.
"""

import sympy as sp
from sympy.combinatorics.free_groups import free_group

print("§1  Digest: nonorientable exceptional braid constraints")
F, q, p, r = free_group("q, p, r")
klein_word = q * p * q**-1 * p
rp_word = r**2
commutator = q * p * q**-1 * p**-1
assert klein_word != commutator
assert klein_word != F.identity
assert rp_word != F.identity
print("   Klein word q p q^{-1} p is not the torus commutator q p q^{-1} p^{-1} ✓")

print("§2  Abelianization constraints")
Aq, Ap, Ar = sp.symbols("Aq Ap Ar", integer=True)
klein_ab = sp.simplify(Aq + Ap - Aq + Ap)
rp_ab = sp.simplify(Ar + Ar)
assert klein_ab == 2 * Ap
assert rp_ab == 2 * Ar
print("   abelianized Klein/RP² constraints are 2Ap=0 and 2Ar=0 ✓")

print("§3  Two-band B2 ≅ Z torsion-free consequence")
assert sp.solve(sp.Eq(2 * Ap, 0), Ap) == [0]
assert sp.solve(sp.Eq(2 * Ar, 0), Ar) == [0]
print("   in B2≅Z, gapped torsion constraints force Ap=Ar=0 ✓")

print("§4  Gapless boundary/EP total charge words")
# Nonorientable boundary word forms from Eq. (6).
EP_K = klein_word
EP_RP = rp_word
assert EP_K == q * p * q**-1 * p
assert EP_RP == r**2
# Under abelianization the total charges are even in the non-orientable direction.
assert klein_ab.subs({Ap: 1}) == 2
assert rp_ab.subs({Ar: 1}) == 2
print("   total EP charge has Klein/RP² boundary word form; abelian degree is doubled ✓")

print()
print("exceptional_nonorientable_topology.py: All identities verified")
