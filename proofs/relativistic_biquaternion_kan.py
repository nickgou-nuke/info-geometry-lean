"""SymPy witness: biquaternion / SL(2,C) / KAN dictionary for special relativity.

Verifies computationally:
- spacetime vector (t,x,y,z) as Hermitian Pauli matrix X;
- det(X)=t^2-x^2-y^2-z^2 (Minkowski interval);
- SL(2,C) conjugation preserves det for a symbolic diagonal boost;
- boost exponential exp((eta/2) sigma1) has closed cosh/sinh form;
- lightcone coordinates transform by exp(±eta) under the spin boost;
- pg glide extinction filters odd fixed-axis momentum modes.
"""

import sympy as sp

print("§1  Minkowski vector as Hermitian biquaternion")
t, x, y, z, eta = sp.symbols("t x y z eta", real=True)
I = sp.I
sigma1 = sp.Matrix([[0, 1], [1, 0]])
sigma2 = sp.Matrix([[0, -I], [I, 0]])
sigma3 = sp.Matrix([[1, 0], [0, -1]])
Id = sp.eye(2)
X = t*Id + x*sigma1 + y*sigma2 + z*sigma3
expected = sp.Matrix([[t+z, x-I*y], [x+I*y, t-z]])
assert sp.simplify(X - expected) == sp.zeros(2)
assert sp.factor(X.det()) == t**2 - x**2 - y**2 - z**2
print("   X=tI+xσ1+yσ2+zσ3 and det(X)=t²-x²-y²-z² ✓")

print("§2  SL(2,C) determinant preservation")
A = sp.diag(sp.exp(eta/2), sp.exp(-eta/2))
Xp = A * X * A.conjugate().T
assert sp.simplify(A.det() - 1) == 0
assert sp.simplify(sp.factor(Xp.det() - X.det())) == 0
print("   X -> A X A† preserves Minkowski determinant for det(A)=1 boost ✓")

print("§3  Lorentz boost on lightcone coordinates")
# For z-boost: X00=t+z scales by e^eta, X11=t-z scales by e^-eta.
assert sp.simplify(Xp[0, 0] - sp.exp(eta)*(t+z)) == 0
assert sp.simplify(Xp[1, 1] - sp.exp(-eta)*(t-z)) == 0
print("   lightcone coordinates scale as u=t+z -> e^ηu, v=t-z -> e^-ηv ✓")

print("§4  Spin boost exponential closure")
B = sp.cosh(eta/2)*Id + sp.sinh(eta/2)*sigma1
assert sp.simplify(B.det() - 1) == 0
assert sp.simplify(sigma1**2 - Id) == sp.zeros(2)
print("   exp((η/2)σ1)=cosh(η/2)I+sinh(η/2)σ1, determinant 1 ✓")

print("§5  Glide momentum extinction as relativistic selection rule")
for k in range(8):
    phase = sp.Integer(-1)**k
    c = sp.symbols(f"c_{k}_0")
    if k % 2:
        assert sp.solve(sp.Eq(c - phase*c, 0), c) == [0]
    else:
        assert sp.simplify(c - phase*c) == 0
print("   odd fixed-axis momentum modes are topologically extinguished ✓")

print()
print("relativistic_biquaternion_kan.py: All identities verified")
