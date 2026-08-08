"""SymPy witness: Klein paradox and graphene Klein tunneling.

Digest source: /home/goutev/Desktop/symmetry/par/klein1.pdf
Hua Chen, "Klein Paradox and Graphene".

Checks:
- corrected 1D Dirac step-current coefficients have R+T=1 and nonzero
  infinite-barrier transmission T=2p/(E+p);
- graphene massless Dirac/Weyl Hamiltonian has conical dispersion E^2=v_F^2|k|^2;
- barrier transmission formula gives perfect normal-incidence Klein tunneling;
- resonant tunneling D q_x=n pi gives T=1;
- the infinite-barrier graphene expression remains perfectly transmitting at normal incidence.
"""

import sympy as sp

print("§1  Corrected 1D Klein step limit")
E, p = sp.symbols("E p", positive=True)
R_inf = (E - p) / (E + p)
T_inf_step = 2*p / (E + p)
assert sp.simplify(R_inf + T_inf_step - 1) == 0
assert sp.simplify(T_inf_step) != 0
print("   R=(E-p)/(E+p), T=2p/(E+p), R+T=1 and T nonzero ✓")

print("§2  Graphene Weyl/Dirac cone")
kx, ky, vF, lam = sp.symbols("kx ky vF lambda")
sx = sp.Matrix([[0, 1], [1, 0]])
sy = sp.Matrix([[0, -sp.I], [sp.I, 0]])
H = vF * (kx*sx + ky*sy)
char = sp.factor(H.charpoly(lam).as_expr())
assert sp.expand(char - (lam**2 - vF**2*(kx**2 + ky**2))) == 0
print("   det(λI-H)=λ²-vF²(kx²+ky²) ✓")

print("§3  Graphene barrier transmission")
cphi, ctheta, sphi, stheta, C, S = sp.symbols("cphi ctheta sphi stheta C S")
T = (ctheta**2*cphi**2) / (C**2*cphi**2*ctheta**2 + S**2*(1 + sphi*stheta)**2)
# normal incidence: phi=theta=0; with trig identity C^2+S^2=1
T_normal = sp.simplify(T.subs({cphi:1, ctheta:1, sphi:0, stheta:0}))
assert T_normal == 1/(C**2 + S**2)
assert sp.simplify(T_normal.subs(S**2, 1-C**2) - 1) == 0
print("   normal incidence gives T=1: Klein tunneling ✓")

print("§4  Resonant tunneling")
T_res = sp.simplify(T.subs({S:0, C**2:1}))
assert sp.simplify(T_res - 1) == 0
print("   D q_x=nπ resonance gives T=1 ✓")

print("§5  Infinite-barrier graphene expression")
T_inf_graphene = cphi**2 / (1 - C**2*sphi**2)
assert sp.simplify(T_inf_graphene.subs({cphi:1, sphi:0}) - 1) == 0
assert sp.simplify(T_inf_graphene.subs(C**2, 1).subs(cphi**2, 1-sphi**2) - 1) == 0
print("   V0→∞ expression still has perfect normal/resonant transmission ✓")

print()
print("klein_graphene_tunneling.py: All identities verified")
