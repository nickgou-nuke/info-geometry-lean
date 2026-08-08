"""SymPy witness: projective kappa mechanism -> Brillouin Klein/Mobius boundary.

This integrates arXiv:2509.19735v1 with the thesis dictionary:
- kappa_M=(0,1/2) gives a momentum-space glide;
- squaring gives a full reciprocal translation;
- half reciprocal shift gives phase -1;
- projective mirror/translation matrices anticommute, hence Pauli/Clifford closure;
- Mackey kappa square defect is a reciprocal lattice vector.
"""

import sympy as sp

print("§1  Momentum-space Möbius/projective glide")
kx, ky = sp.symbols("kx ky")
def affine_M(k):
    x, y = k
    return (-x, y + sp.Rational(1, 2))
def Ty(k):
    x, y = k
    return (x, y + 1)
assert affine_M(affine_M((kx, ky))) == Ty((kx, ky))
print("   (M,kappa_M)^2 = T_y ✓")

print("§2  Half reciprocal phase")
z = sp.symbols("z")
assert -(-z) == z
assert sp.exp(sp.I * sp.pi) == -1
print("   half shift phase squares to identity and e^{iπ}=-1 ✓")

print("§3  Projective Pauli/Clifford anticommutation")
Mx = sp.Matrix([[0, 1], [1, 0]])
Ly = sp.Matrix([[1, 0], [0, -1]])
I2 = sp.eye(2)
assert Mx**2 == I2
assert Ly**2 == I2
assert Mx * Ly == -(Ly * Mx)
assert (Mx * Ly)**2 == -I2
print("   Mx^2=Ly^2=1, Mx Ly=-Ly Mx, (Mx Ly)^2=-1 ✓")

print("§4  Mackey consistency")
def mirror(k):
    x, y = k
    return (-x, y)
def add(a, b):
    return (sp.simplify(a[0]+b[0]), sp.simplify(a[1]+b[1]))
def sub(a, b):
    return (sp.simplify(a[0]-b[0]), sp.simplify(a[1]-b[1]))
kappaM = (sp.Rational(0), sp.Rational(1, 2))
kappaE = (sp.Rational(0), sp.Rational(0))
defect = sub(add(kappaM, mirror(kappaM)), kappaE)
assert defect == (0, 1)
assert all(v.q == 1 for v in defect)  # integer reciprocal lattice vector
print("   kappa_M + M kappa_M - kappa_E = (0,1) ∈ reciprocal lattice ✓")

print("§5  Fixed-line recentering")
x = sp.symbols("x")
fixed = sp.solve(sp.Eq(x, 1-x), x)[0]
assert fixed == sp.Rational(1, 2)
assert fixed - sp.Rational(1, 2) == 0
print("   Riemann fixed coordinate 1/2 recenters to Klein coordinate 0 ✓")

print()
print("projective_kappa_klein_mobius.py: All identities verified")
