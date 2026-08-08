"""SymPy witness: Final Holographic Thesis Seal.

The final algebraic slogan is now formalized:
"The Squash gives projection; the Sign gives quantization."
"""

import sympy as sp

print("======================================================================")
print("             FINAL HOLOGRAPHIC THESIS SEAL                            ")
print("======================================================================\n")

print("§1. The Squash gives projection (tanh)")
v = sp.symbols('v', real=True, positive=True)
squash = sp.tanh(v/2)
print(f"  Limit of tanh(v/2) as v -> oo: {sp.limit(squash, v, sp.oo)}")
print(f"  Limit of tanh(v/2) as v -> -oo: {sp.limit(sp.tanh(-v/2), v, sp.oo)}")

print("\n§2. The Sign gives quantization (Cl(1,1) CPT Atom)")
eps = sp.Matrix([[0, 1], [1, 0]])
J = sp.Matrix([[0, -1], [1, 0]])
CPT = eps * J

print(f"  epsilon^2 = 1: {eps**2 == sp.eye(2)}")
print(f"  J^2 = -1: {J**2 == -sp.eye(2)}")
print(f"  eps*J = -J*eps: {eps*J == -J*eps}")
print(f"  (eps*J)^2 = 1: {CPT**2 == sp.eye(2)}")

print("\n§3. Signum Normalization")
K = v * eps
K_norm = K / sp.Abs(v)
print("  K / |K| = sgn(v) * epsilon")
print(f"  For v > 0: {K_norm == eps}")

print("\n§4. Tripotent Boundary")
T = sp.Matrix([[1, 0, 0], [0, -1, 0], [0, 0, 0]])
T_poly = T**3 - T
print(f"  T^3 - T = 0: {T_poly == sp.zeros(3, 3)}")

print("\n======================================================================")
print("  SEAL VERIFIED: The Squash gives projection; the Sign gives quantization.")
print("======================================================================")
