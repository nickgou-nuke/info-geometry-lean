"""SymPy witness: Minkowski spacetime inside complexified split-octonions.

We model the quaternionic subalgebra of C ⊗ O_s via Pauli matrices:
  e0 -> I,  e_j -> -i sigma_j.
Then the spacetime embedding
  X_oct = t e0 + i x e1 + i y e2 + i z e3
maps to
  X = t I + x sigma1 + y sigma2 + z sigma3,
whose determinant is the Minkowski interval.

The boost generator i e1 maps to sigma1, so
  Lambda = cosh(eta/2) I + sinh(eta/2) sigma1
has determinant one and preserves det(X) under X -> Lambda X Lambda.
"""

import sympy as sp

print("§1  Complexified split-octonion quaternionic subalgebra")
t, x, y, z, eta, v, eps = sp.symbols("t x y z eta v eps", real=True)
I = sp.I
Id = sp.eye(2)
s1 = sp.Matrix([[0, 1], [1, 0]])
s2 = sp.Matrix([[0, -I], [I, 0]])
s3 = sp.Matrix([[1, 0], [0, -1]])

e0 = Id
e1 = -I * s1
e2 = -I * s2
e3 = -I * s3
assert sp.simplify(e1**2 + Id) == sp.zeros(2)
assert sp.simplify(e2**2 + Id) == sp.zeros(2)
assert sp.simplify(e3**2 + Id) == sp.zeros(2)
print("   e1²=e2²=e3²=-1 in the quaternionic subalgebra ✓")

print("§2  Octonionic spacetime embedding gives Minkowski interval")
X_oct = t*e0 + I*x*e1 + I*y*e2 + I*z*e3
X_pauli = t*Id + x*s1 + y*s2 + z*s3
assert sp.simplify(X_oct - X_pauli) == sp.zeros(2)
interval = t**2 - x**2 - y**2 - z**2
assert sp.factor(X_oct.det()) == interval
print("   X_oct=t e0+i x e1+i y e2+i z e3 maps to Pauli X, det(X)=Minkowski ✓")

print("§3  Octonionic boost generator")
K_oct = v * I * e1  # maps to v sigma1
assert sp.simplify(K_oct - v*s1) == sp.zeros(2)
assert sp.simplify(K_oct**2 - v**2*Id) == sp.zeros(2)
boost_closed = sp.cosh(eps*v)*Id + (sp.sinh(eps*v)/v)*K_oct
boost_expected = sp.cosh(eps*v)*Id + sp.sinh(eps*v)*s1
assert sp.simplify(boost_closed - boost_expected) == sp.zeros(2)
print("   K_oct=v i e1 squares to v² and exp closes by cosh/sinh ✓")

print("§4  Lorentz boost determinant invariance")
Lam = sp.cosh(eta/2)*Id + sp.sinh(eta/2)*s1
assert sp.simplify(Lam.det() - 1) == 0
Xp = sp.simplify(Lam * X_oct * Lam)
assert sp.simplify(sp.factor(Xp.det() - X_oct.det())) == 0
print("   det(Lambda)=1 and det(Lambda X Lambda)=det(X) ✓")

print()
print("split_octonion_minkowski.py: All identities verified")
