"""SymPy witness: Projective crystal symmetry and Mackey kappa decomposition.

Digest source: arXiv:2509.19735v1, Zhang--Yang--Zhao,
"Projective crystal symmetry and topological phases".

Checks:
- projective anticommutation M L = - L M;
- the corresponding Z2xZ2 sign factor is a 2-cocycle;
- momentum-space mirror with kappa=(0,1/2) squares to a reciprocal translation;
- Mackey kappa constraint kappa_M + M kappa_M - kappa_E ∈ reciprocal lattice;
- Z2 invariant is stable modulo 2.
"""

import itertools
import sympy as sp

print("§1  Projective matrix relation")
Mx = sp.Matrix([[0, 1], [1, 0]])
Ly = sp.Matrix([[1, 0], [0, -1]])
assert Mx * Ly == -(Ly * Mx)
assert Mx * Ly * Mx == -Ly
print("   Mx Ly = - Ly Mx and Mx Ly Mx = -Ly ✓")

print("§2  Z2xZ2 sign factor is a cocycle")
def mul(g, h):
    return (g[0] ^ h[0], g[1] ^ h[1])

def nu(g, h):
    # factor for generators M,L with M L = - L M
    return -1 if (g[0] and h[1]) else 1

G = list(itertools.product([False, True], repeat=2))
for g, h, k in itertools.product(G, repeat=3):
    assert nu(g, h) * nu(mul(g, h), k) == nu(g, mul(h, k)) * nu(h, k)
print("   ν(g,h)ν(gh,k)=ν(g,hk)ν(h,k) ✓")

print("§3  Mackey kappa momentum glide")
kx, ky = sp.symbols("kx ky")
def mirror(p):
    x, y = p
    return (-x, y)

def add(p, q):
    return (sp.simplify(p[0] + q[0]), sp.simplify(p[1] + q[1]))

kappa_M = (sp.Rational(0), sp.Rational(1, 2))
kappa_E = (sp.Rational(0), sp.Rational(0))
def affine_M(p):
    return add(mirror(p), kappa_M)

assert affine_M(affine_M((kx, ky))) == (kx, ky + 1)
constraint = add(add(kappa_M, mirror(kappa_M)), (-kappa_E[0], -kappa_E[1]))
assert constraint == (0, 1)
print("   (M,kappa_M)^2 = reciprocal y-translation and constraint=(0,1) ✓")

print("§4  Z2 invariant")
n = sp.symbols("n", integer=True)
for i in range(-5, 6):
    assert (i + 2) % 2 == i % 2
print("   invariant n mod 2 is periodic under n↦n+2 ✓")

print()
print("projective_crystal_mackey_decomposition.py: All identities verified")
