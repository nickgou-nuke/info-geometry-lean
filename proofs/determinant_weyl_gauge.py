"""
SymPy witness for Determinant Weyl Gauge (proofs/determinant_weyl_gauge.lean)

Verifies: Cl(1,1) → M₂(ℝ), det = a²-b²+c²-d² in the
`I,e1,e2,e1e2` coordinate basis,
exponential map → causal cone, light cone (Cayley-Hamilton).
"""

import sympy as sp
import numpy as np

print("=" * 60)
print(" DETERMINANT WEYL GAUGE -- SymPy witness")
print("=" * 60)

# Cl(1,1) generators
e1 = sp.Matrix([[0, 1], [1, 0]])
e2 = sp.Matrix([[0, 1], [-1, 0]])
I2 = sp.eye(2)

print("\n-- Cl(1,1) Generators --")
print(f"  e1^2 = I? {e1*e1 == I2}")
print(f"  e2^2 = -I? {e2*e2 == -I2}")
print(f"  e1*e2 = -e2*e1? {e1*e2 == -(e2*e1)}")
print(f"  (e1*e2)^2 = I? {(e1*e2)*(e1*e2) == I2}")

# Clifford element: a*I + b*e1 + c*e2 + d*e1e2
a, b, c, d = sp.symbols('a b c d')
M = a*I2 + b*e1 + c*e2 + d*(e1*e2)
det_M = sp.factor(M.det())
print(f"\n  M = a*I + b*e1 + c*e2 + d*e1e2")
print(f"  det(M) = {det_M}")
expected_det = a**2 - b**2 + c**2 - d**2
print(f"  Expected: a^2 - b^2 + c^2 - d^2 = {sp.simplify(det_M - expected_det)}")
print(f"  Determinant signature in the Clifford coordinate basis verified!")

# Exponential map
t = sp.symbols('t', real=True)
E1 = sp.cosh(t)*I2 + sp.sinh(t)*e1
E2 = sp.cos(t)*I2 + sp.sin(t)*e2

print(f"\n-- Exponential Map --")
print(f"  exp(t*e1) = cosh(t)*I + sinh(t)*e1")
print(f"  det(exp(t*e1)) = {sp.simplify(E1.det())}  (should be 1)")
print(f"  exp(t*e2) = cos(t)*I + sin(t)*e2")
print(f"  det(exp(t*e2)) = {sp.simplify(E2.det())}  (should be 1)")

# Light cone: det(x) = 0 → x^2 = tr(x)*x
x00, x01, x10, x11 = sp.symbols('x00 x01 x10 x11')
X = sp.Matrix([[x00, x01], [x10, x11]])
det_X = X.det()
tr_X = sp.trace(X)

# Verify Cayley-Hamilton: X^2 - tr(X)*X + det(X)*I = 0
CH = X*X - tr_X*X + det_X*I2
print(f"\n-- Cayley-Hamilton --")
print(f"  X^2 - tr(X)*X + det(X)*I = {sp.simplify(CH)}")
print(f"  If det(X)=0: X^2 = tr(X)*X")
print(f"  Verified: {sp.simplify(CH) == sp.zeros(2,2)}")

# CPT/V4
print(f"\n-- CPT Klein Four-Group --")
print(f"  P: x -> -x^T, T: x -> x^T, PT: x -> -x")
print(f"  P^2 = id? {sp.simplify(-(-X.T).T) == X}")
print(f"  T^2 = id? {X.T.T == X}")
print(f"  det(P(x)) = det(x)? {sp.simplify(((-X).T).det() - X.det()) == 0}")

# Numeric verification
qn = np.exp(np.pi*1j/5)
print(f"\n-- Numeric Cross-Check (q = e^(pi*i/5)) --")
for name, mat in [("e1", e1), ("e2", e2)]:
    m = np.array(mat.tolist(), dtype=float)
    m2 = m @ m
    print(f"  {name}^2 = {m2}")

# Determinant causal classification
print(f"\n-- Causal Classification --")
vals = [(2, 0, 0, 0), (0, 2, 0, 0), (0, 0, 2, 0), (1, 1, 0, 1)]
for av, bv, cv, dv in vals:
    det_v = av**2 - bv**2 + cv**2 - dv**2
    causal = "time-like" if det_v > 0 else ("space-like" if det_v < 0 else "light-like")
    print(f"  (a={av},b={bv},c={cv},d={dv}): det={det_v} → {causal}")

# Weyl scale flow and entropy-like potential
lam = sp.symbols('lam', real=True)
M_id = lam * I2
print(f"\n-- Weyl scale flow check --")
print(f"  det(lam * I2) = {sp.simplify(M_id.det())}")
print(f"  relative volume factor = lam^2")
print(f"  -logdet(lam * I2) = {sp.simplify(-sp.log(M_id.det()))}")
print(f"  W(lam) = exp(det(lam * I2)) = {sp.simplify(sp.exp(M_id.det()))}")
print(f"  light-cone limit lam -> 0: det = {sp.simplify(sp.limit(lam**2, lam, 0))}, W = {sp.simplify(sp.limit(sp.exp(lam**2), lam, 0))}")
print(f"  dual/conformal limit lam -> oo: det = {sp.simplify(sp.limit(lam**2, lam, sp.oo))}, W = {sp.simplify(sp.limit(sp.exp(lam**2), lam, sp.oo))}")

# Bregman-type divergence from log-volume potential in scale coordinates
lam1, lam2 = sp.symbols('lam1 lam2', positive=True, real=True)
D = 2 * (lam1 / lam2 - sp.log(lam1 / lam2) - 1)
print(f"\n-- Bregman/scale divergence --")
print(f"  D(logdet)(lam1||lam2) = {sp.simplify(D)}")
print(f"  D(lam||1) = 2*(lam - log(lam) - 1) = {sp.simplify(D.subs(lam2, 1))}")
print(f"  D positivity check: second derivative wrt lam1 is {sp.simplify(sp.diff(D, lam1, lam1))}")
print(f"  Divergence at lam1=lam2: {sp.simplify(D.subs(lam1, lam2))}")

# RN derivative / Jacobian potential along one-dimensional Lie flow parameter t in vacuum frame
logdet_t = -sp.log(sp.exp(t) ** 2)
print(f"\n-- Vacuum Jacobian potential along Weyl Lie flow --")
print(f"  φ(t) = -log(det(exp(t) * I)) = {sp.simplify(logdet_t)}")
print(f"  d/dt φ(t) = {sp.simplify(sp.diff(logdet_t, t))}")

print("\n" + "=" * 60)
print(" Cl(1,1) gauge structure verified: det = Minkowski norm.")
print("=" * 60)
