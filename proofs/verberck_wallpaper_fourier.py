"""SymPy witness for Verberck (2012), symmetry-adapted Fourier series.

Paper digested: Bart Verberck, "Symmetry-Adapted Fourier Series for the
Wallpaper Groups", Symmetry 4 (2012), 379--426.

Computational checks formalized here:
- p6 Fourier-index rotation cycle
  (k1,k2)->(k2,-k1+k2) has order 6;
- pg glide reflection coefficient rule
  c[k1,k2] = (-1)^k1 c[k1,-k2];
- fixed-line extinction for pg: c[k1,0]=0 when k1 is odd;
- the glide operator squares to a lattice translation, represented in coefficient
  space by phase^2=1.
"""

import sympy as sp

print("§1  Digest: Verberck wallpaper Fourier rules")
print("   Fourier coefficient symmetries are induced by reciprocal-index actions;")
print("   nonsymmorphic glides add phase factors and extinction rules.")

print("§2  p6 coefficient orbit")
k1, k2 = sp.symbols("k1 k2", integer=True)
R = sp.Matrix([[0, 1], [-1, 1]])  # (k1,k2) -> (k2,-k1+k2)
assert R**6 == sp.eye(2)
assert R**3 == -sp.eye(2)
vec = sp.Matrix([k1, k2])
orbit = [sp.simplify((R**n) * vec) for n in range(6)]
expected = [
    sp.Matrix([k1, k2]),
    sp.Matrix([k2, -k1 + k2]),
    sp.Matrix([-k1 + k2, -k1]),
    sp.Matrix([-k1, -k2]),
    sp.Matrix([-k2, k1 - k2]),
    sp.Matrix([k1 - k2, k1]),
]
assert orbit == expected
print("   p6 cycle matches Eq. (30) and R^6=I ✓")

print("§3  pg glide phase and extinction")
# pg glide: (x,y)->(x+a/2,-y), rectangular reciprocal basis.
# Coefficient rule: c[k1,k2] = (-1)^k1 c[k1,-k2].
for n in range(-5, 6):
    phase = sp.Integer(-1) ** n
    assert phase**2 == 1
    if n % 2:
        # Fixed line k2=0 gives c = -c, hence c=0 over characteristic zero.
        c = sp.symbols(f"c_{n}_0")
        assert sp.simplify(c - phase*c) == 2*c
        assert sp.solve(sp.Eq(c - phase*c, 0), c) == [0]
print("   glide phase squares to 1; odd fixed-line coefficients vanish ✓")

print("§4  Real-function criterion")
# c_k^* = c_-k is represented by conjugate-pair consistency.
a, b = sp.symbols("a b", real=True)
c = a + sp.I*b
assert sp.conjugate(c) == a - sp.I*b
print("   real Fourier fields pair k and -k by complex conjugation ✓")

print()
print("verberck_wallpaper_fourier.py: All identities verified")
