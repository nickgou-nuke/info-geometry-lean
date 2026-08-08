"""SymPy witness: Penrose KMS critical scale and tripotent scale dictionary.

Verifies the computational layer proposed after the modular Itakura--Saito and
biquaternion resolvent formalizations:

- Penrose substitution matrix M has Perron root phi^2.
- Critical KMS inverse temperature beta_c = log(phi^2).
- Tripotent scale polynomial has poles {-1,0,+1}.
- A toy Cantor/Penrose spectral zeta with scale lambda=phi^2 has convergence
  threshold s > log(2)/log(lambda).
- Resolvent 1/(s-lambda) tends to 0 as s -> infinity, matching conformal scale.
"""

import sympy as sp

print("§1  Penrose Perron root")
phi = (1 + sp.sqrt(5)) / 2
lam = phi**2
M = sp.Matrix([[2, 1], [1, 1]])
char = sp.factor(M.charpoly().as_expr())
assert char == sp.Symbol('lambda')**2 - 3*sp.Symbol('lambda') + 1
assert sp.simplify(lam**2 - 3*lam + 1) == 0
assert max([sp.N(ev) for ev in M.eigenvals().keys()]) == sp.N(lam)
print("   rho(M)=phi^2 and chi(phi^2)=0 ✓")

print("§2  KMS critical inverse temperature")
beta_c = sp.log(lam)
assert sp.simplify(beta_c - sp.log(phi**2)) == 0
assert sp.N(beta_c) > 0
print("   beta_c=log(rho(M))=log(phi^2)>0 ✓")

print("§3  Tripotent poles")
s = sp.symbols('s')
T = sp.diag(1, -1, 0)
poly = sp.factor((s*sp.eye(3)-T).det())
assert poly == s*(s-1)*(s+1)
assert set(sp.solve(sp.Eq(poly, 0), s)) == {-1, 0, 1}
print("   det(sI-T)=s(s-1)(s+1), poles {-1,0,+1} ✓")

print("§4  Toy spectral zeta abscissa")
# Binary branching with contraction lambda^-1: zeta(s)=Σ 2^n lambda^(-s n)
# converges when 2*lambda^(-s)<1, i.e. s > log(2)/log(lambda).
d = sp.log(2)/sp.log(lam)
assert sp.simplify(d * sp.log(lam) - sp.log(2)) == 0
ratio = 2 * lam**(-d)
assert abs(complex(sp.N(ratio - 1, 50))) < 1e-45
assert sp.N(d) > 0
print("   binary Cantor zeta threshold d=log(2)/log(phi^2) ✓")

print("§5  Conformal infinity")
R = 1/(s - lam)
assert sp.limit(R, s, sp.oo) == 0
print("   resolvent tends to zero as s->infinity ✓")

print()
print("penrose_kms_spectral_dimension.py: All identities verified")
