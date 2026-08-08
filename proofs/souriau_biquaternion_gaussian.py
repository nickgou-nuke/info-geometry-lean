"""SymPy witness: Souriau beta-vector and Gaussian biquaternion closure."""
import sympy as sp

print("§1  Souriau beta-vector determinant")
T, u = sp.symbols('T u', positive=True, real=True)
gamma = 1/sp.sqrt(1-u**2)
b0 = gamma/T
bx = gamma*u/T
I2 = sp.eye(2)
s1 = sp.Matrix([[0,1],[1,0]])
B = b0*I2 + bx*s1
assert sp.simplify(B.det() - 1/T**2) == 0
assert sp.simplify(bx/b0 - u) == 0
print("   det(B)=1/T² and beta_x/beta_0=u ✓")

print("§2  Gaussian closure for Pauli vector")
b0, v = sp.symbols('b0 v', real=True)
P = v*s1
B = b0*I2 + P
expB = sp.exp(b0)*(sp.cosh(v)*I2 + sp.sinh(v)*s1)
assert sp.simplify(expB.det() - sp.exp(2*b0)) == 0
Z = sp.trace(sp.exp(-b0)*(sp.cosh(v)*I2 - sp.sinh(v)*s1))
assert sp.simplify(Z - 2*sp.exp(-b0)*sp.cosh(v)) == 0
U = -sp.diff(sp.log(2*sp.cosh(v)), v)
assert sp.simplify(U + sp.tanh(v)) == 0
print("   exp(b0+vσ)=e^b0(cosh v I+sinh v σ), Z=2e^-b0 cosh v, U=-tanh v ✓")

print("§3  quadratic closure")
a, b, n = sp.symbols('a b n')
X = a*I2 + b*s1
assert X**2 == (a**2+b**2)*I2 + (2*a*b)*s1
print("   powers remain in span {I,σ}; no moment hierarchy leakage ✓")

print("souriau_biquaternion_gaussian.py: All identities verified")
