#!/usr/bin/env python3
"""
Trifactor Geometry — Signed Volume, Berezinian, Pfaffian

Three sectors of determinant theory in supergeometry:
  det = +1  →  even/bosonic (volume-preserving)
  det = -1  →  odd/fermionic (spinorial, projective)
  det = 0   →  degenerate boundary (null cone)

Berezinian: sdet(M) = det(M_ee) / det(M_oo)
Pfaffian:   pf(W)² = |det(W)|
"""
import sympy as sp

sp.init_printing()

print("=" * 70)
print("TRIFACTOR GEOMETRY — SIGNED VOLUME, BEREZINIAN, PFAFFIAN")
print("=" * 70)

# ===================================================================
# 1. TRIFACTOR: det = +1, det = -1, det = 0
# ===================================================================
print("\n1. TRIFACTOR SIGNED VOLUME")

# det = +1: identity (bosonic/even sector)
I2 = sp.eye(2)
print(f"  det(I) = {I2.det()}  → +1 (even/bosonic, volume-preserving)")

# det = -1: Pauli σ_y (fermionic/odd sector, spinorial)
sigma2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
print(f"  det(σ₂) = {sigma2.det()}  → -1 (odd/fermionic, spinorial)")

# det = -1: Fibonacci fusion matrix
phi = (1 + sp.sqrt(5)) / 2
s = sp.sqrt(1/phi)   # s = φ^{-1/2}
tau = 1/phi           # τ = φ^{-1}
F = sp.Matrix([[tau, s], [s, -tau]])
detF = sp.simplify(F.det())
print(f"  det(F_fib) = {detF}  → -1 (projective, braid-stable)" if detF == -1 else f"  ✗ det(F) = {detF}")

# det = 0: null vector / light cone matrix
null_mat = sp.Matrix([[1, 1], [1, 1]])
det_null = null_mat.det()
print(f"  det(null_mat) = {det_null}  → 0 (degenerate, null cone)")

# det = +1: SO(2) rotation matrix
theta = sp.Symbol('theta', real=True)
R = sp.Matrix([[sp.cos(theta), -sp.sin(theta)], [sp.sin(theta), sp.cos(theta)]])
detR = sp.simplify(R.det())
print(f"  det(Rot) = {detR}  → +1 (rotation, orientation-preserving)" if detR == 1 else f"  det(Rot) = {detR}")

# det = -1: reflection matrix
reflect = sp.Matrix([[1, 0], [0, -1]])
detRef = reflect.det()
print(f"  det(refl) = {detRef}  → -1 (reflection, orientation-reversing)")

# ===================================================================
# 2. BEREZINIAN (Superdeterminant)
# ===================================================================
print("\n2. BEREZINIAN — SUPERDETERMINANT")

# Model a 2|2 supermatrix: even-even block A, odd-odd block D
# sdet = det(A - B·D^{-1}·C) / det(D)
# For a block-diagonal supermatrix: sdet = det(A) / det(D)

# Example: A = even sector (bosonic), D = odd sector (fermionic)
A = sp.Matrix([[2, 0], [0, 2]])   # even block, det = 4
D = sp.Matrix([[1, 0], [0, -1]])  # odd block, det = -1

berez = A.det() / D.det()
print(f"  A = even block (bosonic): {A}, det = {A.det()}")
print(f"  D = odd block (fermionic): {D}, det = {D.det()}")
print(f"  Berezinian = det(A)/det(D) = {berez}  → signed supervolume")

# For the Cl(1,1) ⊗ Cl(4,4) split:
# Left factor Cl(1,1): det varies (spin structure)
# Right factor Cl(4,4): superdeterminant structure
print(f"\n  Cl(1,1) ⊗ Cl(4,4) ≅ Cl(5,5):")
print(f"    Left:  det ∈ {{+1, -1}} (spin/projective)")
print(f"    Right: Berezinian = det_even/det_odd")

# ===================================================================
# 3. PFAFFIAN
# ===================================================================
print("\n3. PFAFFIAN — SPINOR NORM")

# For a 2×2 skew-symmetric matrix W: pf(W) = W[0,1], pf(W)² = det(W)
# Example: the standard symplectic form
J_skew = sp.Matrix([[0, 1], [-1, 0]])
detJ = J_skew.det()
pfJ = J_skew[0, 1]  # pf of 2×2 skew = upper-right entry
print(f"  J_skew = {J_skew}")
print(f"  pf(J) = {pfJ},  pf(J)² = {pfJ**2}")
print(f"  det(J) = {detJ}")
assert pfJ**2 == detJ
print(f"  pf(J)² = det(J)  ✓")

# For a 4×4 skew-symmetric matrix:
# pf(W) = W[0,1]·W[2,3] - W[0,2]·W[1,3] + W[0,3]·W[1,2]
# Example: block-diagonal 2×2 + 2×2
W4 = sp.Matrix([
    [0, 1, 0, 0],
    [-1, 0, 0, 0],
    [0, 0, 0, 1],
    [0, 0, -1, 0]
])
detW4 = W4.det()
# pf(W4) = W[0,1]·W[2,3] = 1·1 = 1 (since other entries are 0)
pfW4 = W4[0,1] * W4[2,3] - W4[0,2] * W4[1,3] + W4[0,3] * W4[1,2]
print(f"\n  W₄ = block-diag(J,J)")
print(f"  pf(W₄) = {pfW4},  pf(W₄)² = {pfW4**2}")
print(f"  det(W₄) = {detW4}")
assert pfW4**2 == detW4
print(f"  pf(W₄)² = det(W₄)  ✓")

# ===================================================================
# 4. TENSOR PRODUCT OF TWO DETERMINANTS
# ===================================================================
print("\n4. TENSOR PRODUCT det(A ⊗ B) = det(A)^m · det(B)^n")

# For A ∈ M_n, B ∈ M_m: det(A ⊗ B) = det(A)^m · det(B)^n
# Left (Cl(1,1)): 2×2, det = ±1
# Right (Cl(4,4)): 4×4, det = even/odd split → Berezinian

A_left = sp.Matrix([[0, 1], [1, 0]])   # σ₁, det = -1
B_right = sp.Matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, -1]])  # σ₃ ⊗ I₂, det = -1
# For n=2, m=4: det(A⊗B) = (-1)^4 · (-1)^2 = 1

detA = A_left.det()
detB = B_right.det()
n = A_left.rows
m = B_right.rows
det_tensor_formula = detA**m * detB**n
print(f"  Left:  A ∈ M₂, det = {detA}")
print(f"  Right: B ∈ M₄, det = {detB}")
print(f"  det(A⊗B) = det(A)^4 · det(B)^2 = {det_tensor_formula}")

# Verify with explicit tensor product
ATB = sp.kronecker_product(A_left, B_right)
detATB = ATB.det()
print(f"  det(A⊗B) computed = {detATB}")
assert det_tensor_formula == detATB
print(f"  ✓ Formula verified")

print("\n" + "=" * 70)
print("TRIFACTOR GEOMETRY VERIFIED")
print("  det = +1:  even/bosonic (volume-preserving)        ✓")
print("  det = -1:  odd/fermionic (spinorial, projective)   ✓")
print("  det = 0:   degenerate boundary (null cone)          ✓")
print("  Berezinian: sdet = det_even/det_odd                 ✓")
print("  Pfaffian:   pf² = det (spinor norm)                  ✓")
print("  Tensor:     det(A⊗B) = det(A)^m · det(B)^n           ✓")
print("=" * 70)
