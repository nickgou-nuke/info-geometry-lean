"""SymPy witness: squashing/Cayley/Fredholm/Mobius transforms of biquaternions.

The squashing operator is the Cayley/Fredholm transform
    C(z) = (z-1)/(z+1),
which maps exp(K) to tanh(K/2).  Its fixed points solve z=C(z), i.e. z^2=-1.
For a Pauli-biquaternion X=a I + b sigma_1, all rational Mobius transforms
remain in the span {I, sigma_1}; the resolvent (sI-X)^-1 is explicit.
"""

import sympy as sp

print("§1  Scalar Cayley squashing and fixed points")
z, K = sp.symbols("z K")
C = (z - 1) / (z + 1)
fixed_poly = sp.factor(sp.expand(z*(z+1) - (z-1)))
assert fixed_poly == z**2 + 1
assert set(sp.solve(sp.Eq(z, C), z)) == {-sp.I, sp.I}
assert sp.simplify((((sp.exp(K)-1)/(sp.exp(K)+1)) - sp.tanh(K/2)).rewrite(sp.exp)) == 0
print("   C(z)=(z-1)/(z+1), fixed points ±i, C(e^K)=tanh(K/2) ✓")

print("§1b  Cayley/tanh rapidity and two-sheet polarization")
E, kappa = sp.symbols("E kappa")
assert sp.simplify(((E - 1) / (E + 1)).subs(E, (1 + kappa) / (1 - kappa)) - kappa) == 0

eta = sp.symbols("eta")
assert sp.simplify((((sp.exp(eta) - 1) / (sp.exp(eta) + 1)) - sp.tanh(eta / 2)).rewrite(sp.exp)) == 0

# Two-sheet left/right polarization mixing.  The interference term is the
# algebraic seed of the Hestenes/Dirac trembling-motion interpretation.
c, s = sp.symbols("c s")
Bog = sp.Matrix([[c, s], [s, c]])
Krein = sp.diag(1, -1)
assert sp.simplify(Bog.T * Krein * Bog - (c**2 - s**2) * Krein) == sp.zeros(2)
print("   κ=(E-1)/(E+1) invertible to E=(1+κ)/(1-κ), κ=tanh(η/2) ✓")
print("   two-sheet Bogoliubov polarization preserves Krein form after c²-s²=1 ✓")

print("§2  Biquaternion/Pauli resolvent")
a, b, s = sp.symbols("a b s")
I2 = sp.eye(2)
s1 = sp.Matrix([[0, 1], [1, 0]])
X = a*I2 + b*s1
R = ((s-a)*I2 + b*s1) / ((s-a)**2 - b**2)
assert sp.simplify((s*I2 - X) * R - I2) == sp.zeros(2)
assert sp.expand((s*I2 - X).det() - ((s-a)**2 - b**2)) == 0
print("   (sI-X)^-1=((s-a)I+bσ)/((s-a)^2-b^2) ✓")

print("§3  Matrix Cayley squashing closes in biquaternion span")
# C(X)=(X-I)(X+I)^-1.  Use resolvent formula with s=-1 for (X+I)^-1.
Cmat = sp.simplify((X - I2) * (X + I2).inv())
alpha = sp.simplify(sp.trace(Cmat)/2)
beta = sp.simplify(Cmat[0, 1])
assert sp.simplify(Cmat - (alpha*I2 + beta*s1)) == sp.zeros(2)
print(f"   C(X)=alpha I + beta σ with alpha={alpha}, beta={beta} ✓")

print("§4  General Mobius transform preserves Pauli-biquaternion subalgebra")
p, q, r, t = sp.symbols("p q r t")
M = sp.simplify((p*X + q*I2) * (r*X + t*I2).inv())
alphaM = sp.simplify(sp.trace(M)/2)
betaM = sp.simplify(M[0, 1])
assert sp.simplify(M - (alphaM*I2 + betaM*s1)) == sp.zeros(2)
print("   (pX+qI)(rX+tI)^-1 remains alpha I + beta σ ✓")

print()
print("biquaternion_mobius_squashing.py: All identities verified")
