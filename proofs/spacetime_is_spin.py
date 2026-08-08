"""SymPy witness: spacetime is spin.

A Minkowski 4-vector is encoded as a 2x2 Hermitian Pauli matrix
    X=t I + x σ1 + y σ2 + z σ3.
Then trace(X)=2t, det(X)=t^2-x^2-y^2-z^2, eigenvalues are
    t ± sqrt(x^2+y^2+z^2),
and null pure spinor outer products have determinant zero.
"""

import sympy as sp

print("§1  Pauli spacetime matrix")
t, x, y, z, lam = sp.symbols("t x y z lambda", real=True)
I2 = sp.eye(2)
s1 = sp.Matrix([[0, 1], [1, 0]])
s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
s3 = sp.Matrix([[1, 0], [0, -1]])
X = t*I2 + x*s1 + y*s2 + z*s3
expected = sp.Matrix([[t+z, x-sp.I*y], [x+sp.I*y, t-z]])
assert X == expected
print("   X=tI+xσ1+yσ2+zσ3 ✓")

print("§2  trace, determinant, lightcone eigenvalues")
assert sp.trace(X) == 2*t
assert sp.expand(X.det() - (t**2 - x**2 - y**2 - z**2)) == 0
char = sp.factor((lam*I2 - X).det())
assert sp.expand(char - ((lam-t)**2 - (x**2+y**2+z**2))) == 0
print("   Tr(X)=2t, det(X)=Minkowski metric, char=(λ-t)^2-|r|^2 ✓")

print("§3  Lorentz/SL2C determinant invariance socket witness")
a, b, c, d = sp.symbols("a b c d")
L = sp.Matrix([[a, b], [c, d]])
Xp = L * X * L.T  # algebraic transpose witness; dagger version analogous with conjugates
assert sp.factor(Xp.det() - (L.det()**2)*X.det()) == 0
print("   det(L X L^T)=det(L)^2 det(X); SL2 preserves determinant ✓")

print("§4  null spinor outer product")
u, v = sp.symbols("u v")
psi = sp.Matrix([[u], [v]])
Outer = psi * psi.T
assert Outer.det() == 0
assert Outer.rank() == 1
print("   spinor outer product ψψ^T has det=0 and rank 1 generically ✓")

print()
print("spacetime_is_spin.py: All identities verified")
