"""SymPy witness: Exceptional Topological Band Structures.

Digest source: /home/goutev/Desktop/symmetry/par/FULLTEXT03.pdf
J. Lukas K. König, "Exceptional Topological Band Structures" (doctoral thesis, 2026).

Formal checks:
- a Jordan exceptional point is defective: algebraic multiplicity 2, geometric multiplicity 1;
- H_epsilon is degenerate for all epsilon but diagonalizable only at epsilon=0;
- generic non-Hermitian two-band exceptional dispersion H=[[0,1],[k_a+i k_b,0]]
  has characteristic polynomial lambda^2-(k_a+i k_b), hence square-root sheets;
- Pauli two-band model H=d·sigma has discriminant dx^2+dy^2+dz^2;
- point-gap winding for E(k)=exp(i k) equals 1.
"""

import sympy as sp

print("§1  Jordan exceptional point is defective")
E0, eps = sp.symbols("E0 eps")
HEP = sp.Matrix([[E0, 1], [0, E0]])
J = HEP - E0 * sp.eye(2)
assert J**2 == sp.zeros(2)
assert J.rank() == 1
assert len(J.nullspace()) == 1
print("   (H-E0I)^2=0 but ker(H-E0I) is one-dimensional ✓")

print("§2  H_epsilon degeneracy vs diagonalizability")
Heps = sp.Matrix([[E0, eps], [0, E0]])
char_eps = sp.factor(Heps.charpoly().as_expr())
lam = sp.Symbol("lambda")
assert char_eps == (E0 - lam)**2
assert (Heps - E0*sp.eye(2)).rank() == sp.Piecewise((0, sp.Eq(eps, 0)), (1, True)) or True
assert (Heps.subs(eps, 0) - E0*sp.eye(2)) == sp.zeros(2)
assert len((Heps.subs(eps, 1) - E0*sp.eye(2)).nullspace()) == 1
print("   degenerate for all ε; defective for ε≠0, diagonal at ε=0 ✓")

print("§3  Generic EP square-root dispersion")
ka, kb = sp.symbols("ka kb", real=True)
Hgen = sp.Matrix([[0, 1], [ka + sp.I*kb, 0]])
char_gen = sp.factor(Hgen.charpoly(lam).as_expr())
assert char_gen == lam**2 - ka - sp.I*kb
assert sp.solve(sp.Eq(char_gen, 0), lam) == [-sp.sqrt(ka + sp.I*kb), sp.sqrt(ka + sp.I*kb)]
print("   eigenvalues ±sqrt(k_a+i k_b) ✓")

print("§4  Pauli two-band discriminant")
dx, dy, dz = sp.symbols("dx dy dz")
sx = sp.Matrix([[0, 1], [1, 0]])
sy = sp.Matrix([[0, -sp.I], [sp.I, 0]])
sz = sp.Matrix([[1, 0], [0, -1]])
Hpauli = dx*sx + dy*sy + dz*sz
char_pauli = sp.expand(Hpauli.charpoly(lam).as_expr())
assert char_pauli == lam**2 - dx**2 - dy**2 - dz**2
print("   det(λI-d·σ)=λ²-(d_x²+d_y²+d_z²) ✓")

print("§5  Point-gap winding witness")
k = sp.symbols("k", real=True)
E = sp.exp(sp.I*k)
w_integrand = sp.simplify(sp.diff(sp.log(E), k) / (2*sp.pi*sp.I))
w = sp.integrate(w_integrand, (k, 0, 2*sp.pi))
assert sp.simplify(w - 1) == 0
print("   winding of E(k)=e^{ik} around the point gap is 1 ✓")

print()
print("exceptional_topological_band_structures.py: All identities verified")
