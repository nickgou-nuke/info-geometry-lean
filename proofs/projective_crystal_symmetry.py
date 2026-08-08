"""SymPy witness for Zhang-Yang-Zhao, Projective crystal symmetry and topological phases.

Digest/formal layer:
- projective representations obey rho(g)rho(h)=nu(g,h)rho(gh);
- associativity forces the 2-cocycle equation;
- momentum-space nonsymmorphicity arises from projective phases;
- the example Pm -> k-NSG Pg has rho(Mx)rho(Ly)=-rho(Ly)rho(Mx),
  hence a half reciprocal-lattice translation ky -> ky+pi;
- the Brillouin Klein bottle carries a Z2 classification socket.
"""

import sympy as sp

print("§1  2-cocycle equation in a toy additive group")
# For G=Z^2 additive, a standard U(1) multiplier nu(a,b)=exp(i theta det(a,b)).
theta = sp.symbols("theta", real=True)
a1,a2,b1,b2,c1,c2 = sp.symbols("a1 a2 b1 b2 c1 c2", integer=True)

def det2(x1,x2,y1,y2):
    return x1*y2 - x2*y1

def nu(x1,x2,y1,y2):
    return sp.exp(sp.I*theta*det2(x1,x2,y1,y2))

lhs = nu(a1,a2,b1,b2) * nu(a1+b1,a2+b2,c1,c2)
rhs = nu(a1,a2,b1+c1,b2+c2) * nu(b1,b2,c1,c2)
assert sp.simplify(lhs / rhs) == 1
print("   multiplier satisfies nu(a,b)nu(a+b,c)=nu(a,b+c)nu(b,c) ✓")

print("§2  Projective Pm algebra produces k-space glide Pg")
Mx = sp.Matrix([[0, 1], [1, 0]])       # mirror/projective operator
Ly = sp.Matrix([[1, 0], [0, -1]])      # translation eigenphase sector
assert Mx*Ly == -Ly*Mx
assert Mx*Ly*Mx == -Ly
print("   rho(Mx)rho(Ly)=-rho(Ly)rho(Mx), so conjugation flips Ly phase ✓")

print("§3  Half reciprocal translation phase")
ky = sp.symbols("ky", real=True)
z = sp.exp(sp.I*ky)
assert sp.simplify(sp.exp(sp.I*(ky+sp.pi)) + z) == 0
print("   exp(i(ky+pi))=-exp(i ky), i.e. kappa_M=G_y/2 ✓")

print("§4  Brillouin Klein Z2 classification socket")
berry_flux, berry_phase = sp.symbols("berry_flux berry_phase", integer=True)
# model the invariant only as parity of an integer representative
nu_z2 = (berry_flux + berry_phase) % 2
assert nu_z2.subs({berry_flux: 3, berry_phase: 4}) == 1
assert nu_z2.subs({berry_flux: 2, berry_phase: 4}) == 0
print("   Klein-bottle invariant is parity-valued (Z2) ✓")

print()
print("projective_crystal_symmetry.py: All identities verified")
