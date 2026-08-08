#!/usr/bin/env python3
"""SymPy/Numpy witness for Super-Berezinian and Klein-glide anchors."""

import sympy as sp

print("§1 trifactor decomposition")
P = sp.symbols("P")
pplus = sp.Rational(1, 2) * (P**2 + P)
pminus = sp.Rational(1, 2) * (P**2 - P)
pzero = 1 - P**2
assert sp.expand(pplus + pminus + pzero - 1) == 0
orth = sp.expand(pplus * pminus)
# Under P^3=P, P^4=P^2, so orth vanishes.
assert sp.expand(orth.subs(P**4, P**2)) == 0
print("P+, P-, P0 partition unity; P+P-=0 under P³=P ✓")

print("\n§2 scalar Super-Berezinian")
A, B, C, D, c = sp.symbols("A B C D c", nonzero=True)
sber = (A - B * (1/D) * C) * (1/D)
assert sp.simplify(sber.subs({B: 0, C: 0}) - A/D) == 0
scaled = sber.subs({A: c*A, B: 0, C: 0, D: c*D})
assert sp.simplify(scaled - A/D) == 0
print("SBer(A,0,0,D)=A/D and even scaling cancels ✓")

print("\n§3 pg glide / Klein relation")
x, y = sp.symbols("x y", integer=True)
def glide(p):
    x, y = p
    return (x + 1, -y)
assert glide(glide((x, y))) == (x + 2, y)
print("glide² = translation by 2 in x ✓")

print("\n§4 palindromic reciprocal polynomial")
t, lam = sp.symbols("t lam", nonzero=True)
pal = lambda z: z**2 - t*z + 1
assert sp.simplify(pal(lam) - lam**2 * pal(1/lam)) == 0
print("P(λ)=λ²P(λ⁻¹), hence P(λ)/P(λ⁻¹)=λ² away from zeros ✓")

print("\nsuper_berezinian_klein.py: All identities verified")
