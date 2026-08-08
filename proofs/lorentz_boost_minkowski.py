"""Lorentz boost preserves Minkowski pairing and Souriau beta-energy pairing."""
import sympy as sp

print("§1 x-boost preserves Minkowski bilinear form")
phi = sp.symbols("phi", real=True)
a0, a1, a2, a3, b0, b1, b2, b3 = sp.symbols("a0 a1 a2 a3 b0 b1 b2 b3", real=True)
c = sp.cosh(phi)
s = sp.sinh(phi)

def pair(u, v):
    return u[0]*v[0] - u[1]*v[1] - u[2]*v[2] - u[3]*v[3]

def boost(u):
    return (c*u[0] + s*u[1], s*u[0] + c*u[1], u[2], u[3])

a = (a0, a1, a2, a3)
b = (b0, b1, b2, b3)
expr = sp.expand(pair(boost(a), boost(b)) - pair(a, b)).subs(sp.cosh(phi)**2 - sp.sinh(phi)**2, 1)
assert sp.simplify(expr) == 0
print("   η(Λa,Λb)=η(a,b) ✓")

print("§2 mass Casimir and beta-energy pairing")
p = a
beta = b
assert sp.simplify(pair(boost(p), boost(p)) - pair(p, p)) == 0
assert sp.simplify(pair(boost(beta), boost(p)) - pair(beta, p)) == 0
print("   p² and β·p are boost invariant ✓")

print("§3 boosted rest inverse temperature vector")
T = sp.symbols("T", nonzero=True, real=True)
beta_rest = (1/T, 0, 0, 0)
assert sp.simplify(pair(boost(beta_rest), boost(beta_rest)) - 1/T**2) == 0
print("   β_rest=(1/T,0,0,0) keeps β²=1/T² under boost ✓")

print("lorentz_boost_minkowski.py: all identities verified")
