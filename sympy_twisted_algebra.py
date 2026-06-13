"""
Twisted Group Algebra Representation from Aubert-Plymen (arXiv:2603.03027v1)

The group Γ = (Z ⋊ Z/2) × Z_B with cocycle µ((ε,m),(δ,n)) = (-1)^(εn)

Generators and relations:
  s² = 1
  sX = X⁻¹s
  sY = -Ys  (key anticommutation from cocycle)
  XY = YX

Simple modules M_{w,z} = C² (Theorem 6.1):
  s → [[0,1],[1,0]]
  X → [[z,0],[0,z⁻¹]]
  Y → [[w,0],[0,-w]]

Primitive spectrum: (C× × C×) / (w,z) ∼ (-w, z⁻¹)
Maximal compact real form: Klein bottle S¹×S¹ / (w,z) ∼ (-w, z⁻¹)
"""

import sympy
from sympy import Matrix, Rational, sqrt, eye, zeros, I, simplify, pprint, Symbol

print("=" * 60)
print("TWISTED GROUP ALGEBRA REPRESENTATION")
print("Aubert-Plymen (arXiv:2603.03027v1)")
print("=" * 60)

# ============================================================
# Step 1: Define the 2×2 matrix representation (Theorem 6.1)
# ============================================================

def M_s():
    """s → [[0,1],[1,0]]"""
    return Matrix([[0, 1], [1, 0]])

def M_X(z):
    """X → [[z,0],[0,z⁻¹]]"""
    return Matrix([[z, 0], [0, z**(-1)]])

def M_Y(w):
    """Y → [[w,0],[0,-w]]"""
    return Matrix([[w, 0], [0, -w]])

# ============================================================
# Step 2: Verify the defining relations
# ============================================================

print("\n--- Verifying Defining Relations ---")

w, z = sympy.symbols('w z', nonzero=True)

s = M_s()
X = M_X(z)
Y = M_Y(w)

# Relation 1: s² = 1
s_sq = s * s
print(f"\n1. s² = 1:")
print(f"   s² = {s_sq}")
assert s_sq == eye(2), f"s² ≠ 1: {s_sq}"
print(f"   ✓ VERIFIED")

# Relation 2: sX = X⁻¹s
X_inv = X.inv()
lhs_2 = s * X
rhs_2 = X_inv * s
diff_2 = simplify(lhs_2 - rhs_2)
print(f"\n2. sX = X⁻¹s:")
print(f"   sX = {lhs_2}")
print(f"   X⁻¹s = {rhs_2}")
assert diff_2 == zeros(2), f"sX ≠ X⁻¹s: diff = {diff_2}"
print(f"   ✓ VERIFIED")

# Relation 3: sY = -Ys (KEY ANTICOMMUTATION FROM COCYCLE)
lhs_3 = s * Y
rhs_3 = -Y * s
diff_3 = simplify(lhs_3 - rhs_3)
print(f"\n3. sY = -Ys (cocycle relation):")
print(f"   sY = {lhs_3}")
print(f"   -Ys = {rhs_3}")
assert diff_3 == zeros(2), f"sY ≠ -Ys: diff = {diff_3}"
print(f"   ✓ VERIFIED")

# Relation 4: XY = YX
lhs_4 = X * Y
rhs_4 = Y * X
diff_4 = simplify(lhs_4 - rhs_4)
print(f"\n4. XY = YX:")
print(f"   XY = {lhs_4}")
print(f"   YX = {rhs_4}")
assert diff_4 == zeros(2), f"XY ≠ YX: diff = {diff_4}"
print(f"   ✓ VERIFIED")

print("\n✓ ALL DEFINING RELATIONS VERIFIED")

# ============================================================
# Step 3: Verify module equivalence M_{w,z} ≅ M_{-w,z⁻¹}
# ============================================================

print("\n--- Verifying Module Equivalence M_{w,z} ≅ M_{-w,z⁻¹} ---")

# The equivalence is given by conjugation by s:
# s * M_X(z) * s⁻¹ = M_X(z⁻¹) (since sXs⁻¹ = X⁻¹)
# s * M_Y(w) * s⁻¹ = M_Y(-w) (since sYs⁻¹ = -Y)

sXs = simplify(s * X * s.inv())
X_inv_check = M_X(z**(-1))
print(f"\nsXs⁻¹ = {sXs}")
print(f"X(z⁻¹) = {X_inv_check}")
assert simplify(sXs - X_inv_check) == zeros(2), "sXs⁻¹ ≠ X(z⁻¹)"
print(f"   ✓ sXs⁻¹ = X(z⁻¹)")

sYs = simplify(s * Y * s.inv())
Y_neg = M_Y(-w)
print(f"\nsYs⁻¹ = {sYs}")
print(f"Y(-w) = {Y_neg}")
assert simplify(sYs - Y_neg) == zeros(2), "sYs⁻¹ ≠ Y(-w)"
print(f"   ✓ sYs⁻¹ = Y(-w)")

# So conjugation by s sends (w,z) ↦ (-w,z⁻¹), proving M_{w,z} ≅ M_{-w,z⁻¹}
print(f"\n✓ MODULE EQUIVALENCE VERIFIED: conjugation by s sends (w,z) ↦ (-w,z⁻¹)")

# ============================================================
# Step 4: Verify no 1-dimensional modules
# ============================================================

print("\n--- Verifying No 1-Dimensional Modules ---")

# If M is 1-dim, then Y → λ ∈ C×, and sY = -Ys forces sλ = -λs
# In C (1-dim), this means λ = -λ, so λ = 0, contradicting Y invertible
print("In a 1-dim module: Y → λ ∈ C×")
print("Relation sY = -Ys ⟹ λ = -λ ⟹ λ = 0")
print("But Y is invertible, so λ ≠ 0. Contradiction.")
print("✓ NO 1-DIMENSIONAL MODULES")

# ============================================================
# Step 5: Concrete example with specific values
# ============================================================

print("\n--- Concrete Example: w=2, z=3 ---")

w_val = 2
z_val = 3

s_c = M_s()
X_c = M_X(z_val)
Y_c = M_Y(w_val)

print(f"\ns = {s_c}")
print(f"X = {X_c}")
print(f"Y = {Y_c}")

# Verify all relations
assert s_c * s_c == eye(2)
assert simplify(s_c * X_c - X_c.inv() * s_c) == zeros(2)
assert simplify(s_c * Y_c + Y_c * s_c) == zeros(2)
assert simplify(X_c * Y_c - Y_c * X_c) == zeros(2)
print("All relations verified for w=2, z=3 ✓")

# ============================================================
# Step 6: Connection to Cl(1,1) CPT atom
# ============================================================

print("\n--- Connection to Cl(1,1) CPT Atom ---")

# In Cl(1,1): e₁ = σ₃, e₂ = ε
e1 = Matrix([[1, 0], [0, -1]])
e2 = Matrix([[0, 1], [-1, 0]])

# The CPT phase-flip P(X) = e₁Xe₁
def P(X):
    return e1 * X * e1

print(f"\ne₁ = {e1}")
print(f"e₂ = {e2}")
print(f"P(e₁) = {P(e1)} = e₁ ✓")
print(f"P(e₂) = {P(e2)} = -e₂ ✓")

# The Aubert-Plymen sY = -Ys corresponds to P(e₂) = -e₂
# The Aubert-Plymen sX = X⁻¹s corresponds to P(e₁) = e₁⁻¹ = e₁ (since e₁²=1)

print(f"\nAubert-Plymen sY = -Ys ↔ Cl(1,1) P(e₂) = -e₂")
print(f"Aubert-Plymen sX = X⁻¹s ↔ Cl(1,1) P(e₁) = e₁⁻¹ = e₁")

# ============================================================
# Step 7: Trifactor decomposition
# ============================================================

print("\n--- Trifactor Decomposition ---")

# For T = e₁ = σ₃, T³ = T since T² = 1
T_op = e1
assert T_op * T_op * T_op == T_op
print(f"T³ = T for T = σ₃ ✓")

# Trifactor projectors
P_zero = eye(2) - T_op * T_op  # = 0
P_plus = Rational(1, 2) * (T_op * T_op + T_op)  # = (1+T)/2
P_minus = Rational(1, 2) * (T_op * T_op - T_op)  # = (1-T)/2

print(f"\nP_zero = {P_zero}")
print(f"P_plus = {P_plus}")
print(f"P_minus = {P_minus}")

assert P_zero + P_plus + P_minus == eye(2)
assert P_zero * P_zero == P_zero
assert P_plus * P_plus == P_plus
assert P_minus * P_minus == P_minus
assert P_plus * P_minus == zeros(2)
assert T_op * P_zero == zeros(2)
assert T_op * P_plus == P_plus
assert T_op * P_minus == -P_minus
assert P_plus - P_minus == T_op
assert T_op.det() == -1

print("All trifactor properties verified ✓")

# ============================================================
# Step 8: Basis spanning
# ============================================================

print("\n--- Basis Spanning: Cl(1,1) ≅ M₂(ℝ) ---")

I2 = eye(2)
e1e2 = e1 * e2

a, b, c, d = sympy.symbols('a b c d')
A = Matrix([[a, b], [c, d]])

alpha = (a + d) / 2
beta = (a - d) / 2
gamma = (b - c) / 2
delta = (b + c) / 2

A_reconstructed = alpha * I2 + beta * e1 + gamma * e2 + delta * e1e2
assert simplify(A - A_reconstructed) == zeros(2)
print("Cl(1,1) ≅ M₂(ℝ) via {I, e₁, e₂, e₁e₂} ✓")

# ============================================================
# Summary
# ============================================================

print("\n" + "=" * 60)
print("ALL VERIFICATIONS PASSED")
print("=" * 60)
print("""
Aubert-Plymen Twisted Group Algebra C[Γ,µ]:
  Γ = (Z ⋊ Z/2) × Z_B
  µ((ε,m),(δ,n)) = (-1)^(εn)
  Relations: s²=1, sX=X⁻¹s, sY=-Ys, XY=YX

Simple modules M_{w,z} = C²:
  s → [[0,1],[1,0]]
  X → [[z,0],[0,z⁻¹]]
  Y → [[w,0],[0,-w]]

Primitive spectrum: (C××C×)/(w,z)∼(-w,z⁻¹)
Maximal compact real form: Klein bottle

Connection to Cl(1,1):
  s ↔ P (CPT phase-flip)
  Y ↔ e₂ (negative generator)
  X ↔ e₁ (positive generator)
  sY = -Ys ↔ P(e₂) = -e₂
  sX = X⁻¹s ↔ P(e₁) = e₁⁻¹ = e₁
""")
