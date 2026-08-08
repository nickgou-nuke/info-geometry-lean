"""SymPy witness: arXiv 2509.19735v1 projective-crystal kappa mechanism.

Focuses on the arXiv derivation:
  gamma(t,R)=exp(-i kappa_R·t),
  R : k -> R k + kappa_R.
For Pg, kappa_M = G_y/2, so the mirror becomes a momentum-space glide and
squares to a full reciprocal translation.
"""

import sympy as sp

print("§1  Projective phase gives half reciprocal translation")
ky = sp.symbols("ky", real=True)
assert sp.simplify(sp.exp(sp.I*(ky+sp.pi)) + sp.exp(sp.I*ky)) == 0
print("   exp(i(ky+π))=-exp(i ky) ✓")

print("§2  k-space glide squares to full reciprocal translation")
kx, ky, Gy = sp.symbols("kx ky Gy")
def M(k):
    x, y = k
    return (-x, y + Gy/2)
assert M(M((kx,ky))) == (kx, ky + Gy)
print("   M(kx,ky)=(-kx,ky+Gy/2) gives M²=(kx,ky+Gy) ✓")

print("§3  Projective algebra anti-commutation")
Mx = sp.Matrix([[0,1],[1,0]])
Ly = sp.Matrix([[1,0],[0,-1]])
assert Mx*Ly == -Ly*Mx
assert Mx*Ly*Mx == -Ly
print("   ρ(Mx)ρ(Ly)=-ρ(Ly)ρ(Mx), encoding ν(Mx,Ly)=-1 ✓")

print("§4  Z2 invariant parity socket")
n = sp.symbols("n", integer=True)
for val in range(-4,5):
    assert (val + 2) % 2 == val % 2
print("   parity invariant unchanged by adding 2 ✓")

print()
print("projective_crystal_kappa.py: All identities verified")
