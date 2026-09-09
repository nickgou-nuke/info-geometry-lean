import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge

/-!
# InfoGeometry.Canonical.ToeplitzCuntzThreeZ3GradingBridge

Z₃-grading operator Γ = P₁ + ω² P₂ + ω P₃ + P₀ and cubic grading covariance
Γ Q Γ⁻¹ = ω Q in 3-ary Toeplitz-Cuntz ℰ₃ over a non-commutative algebra A with scalar commutative ring K.

This formalizes cubic fractional supersymmetry grading over a non-commutative K-algebra A
where ω ∈ K is a 3rd root of unity (ω³ = 1).

Key Architectural & Audit Guarantees:
1. **Separated Scalar/Operator Context**: [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A].
2. **Order-3 Operator Identities**: Γ Γ⁻¹ = 1, Γ⁻¹ Γ = 1, Γ² = Γ⁻¹, Γ³ = 1.
3. **Cubic Covariance**: Γ Q Γ⁻¹ = ω Q.
4. **Star-Unitarity**: Γ* = Γ⁻¹ when star(ω) = ω².
5. **Exact Nontrivial Grading Certificate**: Proves `z3GradingOperator_ne_one_of_sector_scale`, establishing Γ ≠ 1 whenever (ω² • P₂ ≠ P₂).
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeZ3GradingBridge

open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge
open ToeplitzCuntzThreeGenerators

variable {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
variable (g : ToeplitzCuntzThreeGenerators A)
variable (w : K)

/-- Orthogonality lemma P₁ P₀ = 0. -/
theorem p1_p0_ortho : g.P1 * g.P0 = 0 := by
  dsimp [P0, P1, P2, P3]
  have h11 := g.V1_isometry
  have h12 := g.V1_V2_ortho
  have h13 := g.V1_V3_ortho
  have h : g.V1 * star g.V1 * (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) =
           g.V1 * star g.V1 - g.V1 * (star g.V1 * g.V1) * star g.V1 - g.V1 * (star g.V1 * g.V2) * star g.V2 - g.V1 * (star g.V1 * g.V3) * star g.V3 := by noncomm_ring
  rw [h, h11, h12, h13]
  noncomm_ring

/-- Orthogonality lemma P₂ P₀ = 0. -/
theorem p2_p0_ortho : g.P2 * g.P0 = 0 := by
  dsimp [P0, P1, P2, P3]
  have h21 := g.V2_V1_ortho
  have h22 := g.V2_isometry
  have h23 := g.V2_V3_ortho
  have h : g.V2 * star g.V2 * (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) =
           g.V2 * star g.V2 - g.V2 * (star g.V2 * g.V1) * star g.V1 - g.V2 * (star g.V2 * g.V2) * star g.V2 - g.V2 * (star g.V2 * g.V3) * star g.V3 := by noncomm_ring
  rw [h, h21, h22, h23]
  noncomm_ring

/-- Orthogonality lemma P₃ P₀ = 0. -/
theorem p3_p0_ortho : g.P3 * g.P0 = 0 := by
  dsimp [P0, P1, P2, P3]
  have h31 := g.V3_V1_ortho
  have h32 := g.V3_V2_ortho
  have h33 := g.V3_isometry
  have h : g.V3 * star g.V3 * (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) =
           g.V3 * star g.V3 - g.V3 * (star g.V3 * g.V1) * star g.V1 - g.V3 * (star g.V3 * g.V2) * star g.V2 - g.V3 * (star g.V3 * g.V3) * star g.V3 := by noncomm_ring
  rw [h, h31, h32, h33]
  noncomm_ring

/-- Orthogonality lemma P₀ P₁ = 0. -/
theorem p0_p1_ortho : g.P0 * g.P1 = 0 := by
  dsimp [P0, P1, P2, P3]
  have h11 := g.V1_isometry
  have h21 := g.V2_V1_ortho
  have h31 := g.V3_V1_ortho
  have h : (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) * (g.V1 * star g.V1) =
           g.V1 * star g.V1 - g.V1 * (star g.V1 * g.V1) * star g.V1 - g.V2 * (star g.V2 * g.V1) * star g.V1 - g.V3 * (star g.V3 * g.V1) * star g.V1 := by noncomm_ring
  rw [h, h11, h21, h31]
  noncomm_ring

/-- Orthogonality lemma P₀ P₂ = 0. -/
theorem p0_p2_ortho : g.P0 * g.P2 = 0 := by
  dsimp [P0, P1, P2, P3]
  have h12 := g.V1_V2_ortho
  have h22 := g.V2_isometry
  have h32 := g.V3_V2_ortho
  have h : (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) * (g.V2 * star g.V2) =
           g.V2 * star g.V2 - g.V1 * (star g.V1 * g.V2) * star g.V2 - g.V2 * (star g.V2 * g.V2) * star g.V2 - g.V3 * (star g.V3 * g.V2) * star g.V2 := by noncomm_ring
  rw [h, h12, h22, h32]
  noncomm_ring

/-- Orthogonality lemma P₀ P₃ = 0. -/
theorem p0_p3_ortho : g.P0 * g.P3 = 0 := by
  dsimp [P0, P1, P2, P3]
  have h13 := g.V1_V3_ortho
  have h23 := g.V2_V3_ortho
  have h33 := g.V3_isometry
  have h : (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) * (g.V3 * star g.V3) =
           g.V3 * star g.V3 - g.V1 * (star g.V1 * g.V3) * star g.V3 - g.V2 * (star g.V2 * g.V3) * star g.V3 - g.V3 * (star g.V3 * g.V3) * star g.V3 := by noncomm_ring
  rw [h, h13, h23, h33]
  noncomm_ring

/-- Z₃ Grading Operator Γ = P₁ + ω² P₂ + ω P₃ + P₀. -/
def z3GradingOperator : A :=
  g.P1 + (w * w) • g.P2 + w • g.P3 + g.P0

/-- Inverse Z₃ Grading Operator Γ⁻¹ = P₁ + ω P₂ + ω² P₃ + P₀. -/
def z3GradingOperatorInv : A :=
  g.P1 + w • g.P2 + (w * w) • g.P3 + g.P0

/-- Action of Z₃ grading operator on P₂ sector: Γ P₂ = ω² P₂. -/
theorem z3GradingOperator_apply_p2 :
    z3GradingOperator g w * g.P2 = (w * w) • g.P2 := by
  dsimp [z3GradingOperator]
  simp [add_mul, p1_p2_ortho g, p3_p2_ortho g, p0_p2_ortho g, p2_idempotent g]

/-- **Non-triviality Certificate (Exact Order-3 Qualification)**: Proves Γ ≠ 1 provided (ω² • P₂ ≠ P₂). -/
theorem z3GradingOperator_ne_one_of_sector_scale (h_ne : (w * w) • g.P2 ≠ g.P2) :
    z3GradingOperator g w ≠ 1 := by
  intro h_eq
  have h_mul := congr_arg (fun (x : A) => x * g.P2) h_eq
  dsimp at h_mul
  rw [z3GradingOperator_apply_p2 g w, one_mul] at h_mul
  exact h_ne h_mul

/-- **Theorem**: Γ Γ⁻¹ = 1. -/
theorem z3GradingOperator_mul_inv (hw3 : w * w * w = 1) :
    z3GradingOperator g w * z3GradingOperatorInv g w = 1 := by
  have hp1 := p1_idempotent g
  have hp2 := p2_idempotent g
  have hp3 := p3_idempotent g
  have hp0 := defectProjection_sq g
  have h12 := p1_p2_ortho g
  have h21 := p2_p1_ortho g
  have h23 := p2_p3_ortho g
  have h32 := p3_p2_ortho g
  have h13 := p1_p3_ortho g
  have h31 := p3_p1_ortho g
  have h_res := toeplitzCuntz3_resolution g
  have h10 := p1_p0_ortho g
  have h20 := p2_p0_ortho g
  have h30 := p3_p0_ortho g
  have h01 := p0_p1_ortho g
  have h02 := p0_p2_ortho g
  have h03 := p0_p3_ortho g
  have hw3_alt : w * (w * w) = 1 := by
    calc w * (w * w) = w * w * w := by ring
      _ = 1 := hw3
  have hw3_alt2 : (w * w) * w = 1 := hw3
  dsimp [z3GradingOperator, z3GradingOperatorInv]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul, hp1, hp2, hp3, hp0,
             h12, h21, h23, h32, h13, h31, h10, h20, h30, h01, h02, h03,
             smul_zero, add_zero, zero_add]
  rw [hw3_alt, hw3_alt2]
  simp only [one_smul]
  exact h_res

/-- **Theorem**: Γ⁻¹ Γ = 1. -/
theorem z3GradingOperator_inv_mul (hw3 : w * w * w = 1) :
    z3GradingOperatorInv g w * z3GradingOperator g w = 1 := by
  have hp1 := p1_idempotent g
  have hp2 := p2_idempotent g
  have hp3 := p3_idempotent g
  have hp0 := defectProjection_sq g
  have h12 := p1_p2_ortho g
  have h21 := p2_p1_ortho g
  have h23 := p2_p3_ortho g
  have h32 := p3_p2_ortho g
  have h13 := p1_p3_ortho g
  have h31 := p3_p1_ortho g
  have h_res := toeplitzCuntz3_resolution g
  have h10 := p1_p0_ortho g
  have h20 := p2_p0_ortho g
  have h30 := p3_p0_ortho g
  have h01 := p0_p1_ortho g
  have h02 := p0_p2_ortho g
  have h03 := p0_p3_ortho g
  have hw3_alt : w * (w * w) = 1 := by
    calc w * (w * w) = w * w * w := by ring
      _ = 1 := hw3
  have hw3_alt2 : (w * w) * w = 1 := hw3
  dsimp [z3GradingOperator, z3GradingOperatorInv]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul, hp1, hp2, hp3, hp0,
             h12, h21, h23, h32, h13, h31, h10, h20, h30, h01, h02, h03,
             smul_zero, add_zero, zero_add]
  rw [hw3_alt, hw3_alt2]
  simp only [one_smul]
  exact h_res

/-- **Theorem**: Z₃ Square Identity Γ² = Γ⁻¹. -/
theorem z3GradingOperator_sq (hw3 : w * w * w = 1) :
    z3GradingOperator g w * z3GradingOperator g w = z3GradingOperatorInv g w := by
  have hp1 := p1_idempotent g
  have hp2 := p2_idempotent g
  have hp3 := p3_idempotent g
  have hp0 := defectProjection_sq g
  have h12 := p1_p2_ortho g
  have h21 := p2_p1_ortho g
  have h23 := p2_p3_ortho g
  have h32 := p3_p2_ortho g
  have h13 := p1_p3_ortho g
  have h31 := p3_p1_ortho g
  have h10 := p1_p0_ortho g
  have h20 := p2_p0_ortho g
  have h30 := p3_p0_ortho g
  have h01 := p0_p1_ortho g
  have h02 := p0_p2_ortho g
  have h03 := p0_p3_ortho g
  have hw4 : (w * w) * (w * w) = w := by
    calc (w * w) * (w * w) = (w * w * w) * w := by ring
      _ = 1 * w := by rw [hw3]
      _ = w := by ring
  dsimp [z3GradingOperator, z3GradingOperatorInv]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul, hp1, hp2, hp3, hp0,
             h12, h21, h23, h32, h13, h31, h10, h20, h30, h01, h02, h03,
             smul_zero, add_zero, zero_add]
  rw [hw4]

/-- **Theorem**: Z₃ Cube Identity Γ³ = 1. -/
theorem z3GradingOperator_cube (hw3 : w * w * w = 1) :
    z3GradingOperator g w * z3GradingOperator g w * z3GradingOperator g w = 1 := by
  have h_sq := z3GradingOperator_sq g w hw3
  calc z3GradingOperator g w * z3GradingOperator g w * z3GradingOperator g w
      = z3GradingOperator g w * (z3GradingOperator g w * z3GradingOperator g w) := by noncomm_ring
    _ = z3GradingOperator g w * z3GradingOperatorInv g w := by rw [h_sq]
    _ = 1 := z3GradingOperator_mul_inv g w hw3

/-- **Theorem**: Z₃ Automorphism Covariance Law Γ Q Γ⁻¹ = ω Q. -/
theorem cyclicSupercharge_z3_covariance (hw3 : w * w * w = 1) :
    z3GradingOperator g w * cyclicSupercharge g * z3GradingOperatorInv g w =
    w • cyclicSupercharge g := by
  have hw4 : (w * w) * (w * w) = w := by
    calc (w * w) * (w * w) = (w * w * w) * w := by ring
      _ = 1 * w := by rw [hw3]
      _ = w := by ring
  have hp1_def : g.P1 = g.V1 * star g.V1 := rfl
  have hp2_def : g.P2 = g.V2 * star g.V2 := rfl
  have hp3_def : g.P3 = g.V3 * star g.V3 := rfl
  have h1_sub : g.V1 * star g.V1 * (g.V1 * star g.V2) = g.V1 * star g.V2 := by
    have h : g.V1 * star g.V1 * (g.V1 * star g.V2) = g.V1 * (star g.V1 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V1_isometry, mul_one]
  have h2_sub : g.V2 * star g.V2 * (g.V2 * star g.V3) = g.V2 * star g.V3 := by
    have h : g.V2 * star g.V2 * (g.V2 * star g.V3) = g.V2 * (star g.V2 * g.V2) * star g.V3 := by noncomm_ring
    rw [h, g.V2_isometry, mul_one]
  have h3_sub : g.V3 * star g.V3 * (g.V3 * star g.V1) = g.V3 * star g.V1 := by
    have h : g.V3 * star g.V3 * (g.V3 * star g.V1) = g.V3 * (star g.V3 * g.V3) * star g.V1 := by noncomm_ring
    rw [h, g.V3_isometry, mul_one]
  have h1_sub_r : g.V1 * star g.V2 * (g.V2 * star g.V2) = g.V1 * star g.V2 := by
    have h : g.V1 * star g.V2 * (g.V2 * star g.V2) = g.V1 * (star g.V2 * g.V2) * star g.V2 := by noncomm_ring
    rw [h, g.V2_isometry, mul_one]
  have h2_sub_r : g.V2 * star g.V3 * (g.V3 * star g.V3) = g.V2 * star g.V3 := by
    have h : g.V2 * star g.V3 * (g.V3 * star g.V3) = g.V2 * (star g.V3 * g.V3) * star g.V3 := by noncomm_ring
    rw [h, g.V3_isometry, mul_one]
  have h3_sub_r : g.V3 * star g.V1 * (g.V1 * star g.V1) = g.V3 * star g.V1 := by
    have h : g.V3 * star g.V1 * (g.V1 * star g.V1) = g.V3 * (star g.V1 * g.V1) * star g.V1 := by noncomm_ring
    rw [h, g.V1_isometry, mul_one]
  have h12_o1 : g.V1 * star g.V1 * (g.V2 * star g.V3) = 0 := by
    have h : g.V1 * star g.V1 * (g.V2 * star g.V3) = g.V1 * (star g.V1 * g.V2) * star g.V3 := by noncomm_ring
    rw [h, g.V1_V2_ortho, mul_zero, zero_mul]
  have h12_o2 : g.V1 * star g.V1 * (g.V3 * star g.V1) = 0 := by
    have h : g.V1 * star g.V1 * (g.V3 * star g.V1) = g.V1 * (star g.V1 * g.V3) * star g.V1 := by noncomm_ring
    rw [h, g.V1_V3_ortho, mul_zero, zero_mul]
  have h23_o1 : g.V2 * star g.V2 * (g.V1 * star g.V2) = 0 := by
    have h : g.V2 * star g.V2 * (g.V1 * star g.V2) = g.V2 * (star g.V2 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V2_V1_ortho, mul_zero, zero_mul]
  have h23_o2 : g.V2 * star g.V2 * (g.V3 * star g.V1) = 0 := by
    have h : g.V2 * star g.V2 * (g.V3 * star g.V1) = g.V2 * (star g.V2 * g.V3) * star g.V1 := by noncomm_ring
    rw [h, g.V2_V3_ortho, mul_zero, zero_mul]
  have h31_o1 : g.V3 * star g.V3 * (g.V1 * star g.V2) = 0 := by
    have h : g.V3 * star g.V3 * (g.V1 * star g.V2) = g.V3 * (star g.V3 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V3_V1_ortho, mul_zero, zero_mul]
  have h31_o2 : g.V3 * star g.V3 * (g.V2 * star g.V3) = 0 := by
    have h : g.V3 * star g.V3 * (g.V2 * star g.V3) = g.V3 * (star g.V3 * g.V2) * star g.V3 := by noncomm_ring
    rw [h, g.V3_V2_ortho, mul_zero, zero_mul]
  have h12_or1 : g.V1 * star g.V2 * (g.V1 * star g.V1) = 0 := by
    have h : g.V1 * star g.V2 * (g.V1 * star g.V1) = g.V1 * (star g.V2 * g.V1) * star g.V1 := by noncomm_ring
    rw [h, g.V2_V1_ortho, mul_zero, zero_mul]
  have h12_or3 : g.V1 * star g.V2 * (g.V3 * star g.V3) = 0 := by
    have h : g.V1 * star g.V2 * (g.V3 * star g.V3) = g.V1 * (star g.V2 * g.V3) * star g.V3 := by noncomm_ring
    rw [h, g.V2_V3_ortho, mul_zero, zero_mul]
  have h23_or1 : g.V2 * star g.V3 * (g.V1 * star g.V1) = 0 := by
    have h : g.V2 * star g.V3 * (g.V1 * star g.V1) = g.V2 * (star g.V3 * g.V1) * star g.V1 := by noncomm_ring
    rw [h, g.V3_V1_ortho, mul_zero, zero_mul]
  have h23_or2 : g.V2 * star g.V3 * (g.V2 * star g.V2) = 0 := by
    have h : g.V2 * star g.V3 * (g.V2 * star g.V2) = g.V2 * (star g.V3 * g.V2) * star g.V2 := by noncomm_ring
    rw [h, g.V3_V2_ortho, mul_zero, zero_mul]
  have h31_or2 : g.V3 * star g.V1 * (g.V2 * star g.V2) = 0 := by
    have h : g.V3 * star g.V1 * (g.V2 * star g.V2) = g.V3 * (star g.V1 * g.V2) * star g.V2 := by noncomm_ring
    rw [h, g.V1_V2_ortho, mul_zero, zero_mul]
  have h31_or3 : g.V3 * star g.V1 * (g.V3 * star g.V3) = 0 := by
    have h : g.V3 * star g.V1 * (g.V3 * star g.V3) = g.V3 * (star g.V1 * g.V3) * star g.V3 := by noncomm_ring
    rw [h, g.V1_V3_ortho, mul_zero, zero_mul]
  have h01_left : g.P0 * (g.V1 * star g.V2) = 0 := by
    dsimp [P0, P1, P2, P3]
    have h11 := g.V1_isometry
    have h21 := g.V2_V1_ortho
    have h31 := g.V3_V1_ortho
    have h : (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) * (g.V1 * star g.V2) =
             g.V1 * star g.V2 - g.V1 * (star g.V1 * g.V1) * star g.V2 - g.V2 * (star g.V2 * g.V1) * star g.V2 - g.V3 * (star g.V3 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, h11, h21, h31]
    noncomm_ring
  have h02_left : g.P0 * (g.V2 * star g.V3) = 0 := by
    dsimp [P0, P1, P2, P3]
    have h12 := g.V1_V2_ortho
    have h22 := g.V2_isometry
    have h32 := g.V3_V2_ortho
    have h : (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) * (g.V2 * star g.V3) =
             g.V2 * star g.V3 - g.V1 * (star g.V1 * g.V2) * star g.V3 - g.V2 * (star g.V2 * g.V2) * star g.V3 - g.V3 * (star g.V3 * g.V2) * star g.V3 := by noncomm_ring
    rw [h, h12, h22, h32]
    noncomm_ring
  have h03_left : g.P0 * (g.V3 * star g.V1) = 0 := by
    dsimp [P0, P1, P2, P3]
    have h13 := g.V1_V3_ortho
    have h23 := g.V2_V3_ortho
    have h33 := g.V3_isometry
    have h : (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) * (g.V3 * star g.V1) =
             g.V3 * star g.V1 - g.V1 * (star g.V1 * g.V3) * star g.V1 - g.V2 * (star g.V2 * g.V3) * star g.V1 - g.V3 * (star g.V3 * g.V3) * star g.V1 := by noncomm_ring
    rw [h, h13, h23, h33]
    noncomm_ring
  have h_left : z3GradingOperator g w * cyclicSupercharge g =
                g.V1 * star g.V2 + (w * w) • (g.V2 * star g.V3) + w • (g.V3 * star g.V1) := by
    dsimp [z3GradingOperator, cyclicSupercharge]
    simp only [add_mul, mul_add, smul_mul_assoc, hp1_def, hp2_def, hp3_def,
               h1_sub, h2_sub, h3_sub, h12_o1, h12_o2, h23_o1, h23_o2, h31_o1, h31_o2,
               h01_left, h02_left, h03_left,
               smul_zero, add_zero, zero_add]
  have hd1 : g.V1 * star g.V2 * (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) = 0 := by
    simp only [mul_sub, mul_one]
    rw [h12_or1, sub_zero, h1_sub_r, sub_self, h12_or3, sub_zero]
  have hd2 : g.V2 * star g.V3 * (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) = 0 := by
    simp only [mul_sub, mul_one]
    rw [h23_or1, sub_zero, h23_or2, sub_zero, h2_sub_r, sub_self]
  have hd3 : g.V3 * star g.V1 * (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) = 0 := by
    simp only [mul_sub, mul_one]
    rw [h3_sub_r, h31_or2, sub_zero, h31_or3, sub_zero, sub_self]
  have h10 : g.V1 * star g.V2 * g.P0 = 0 := hd1
  have h20 : g.V2 * star g.V3 * g.P0 = 0 := hd2
  have h30 : g.V3 * star g.V1 * g.P0 = 0 := hd3
  have h_mid : (g.V1 * star g.V2 + (w * w) • (g.V2 * star g.V3) + w • (g.V3 * star g.V1)) * z3GradingOperatorInv g w =
               w • cyclicSupercharge g := by
    have term1 : g.V1 * star g.V2 * z3GradingOperatorInv g w = w • (g.V1 * star g.V2) := by
      dsimp [z3GradingOperatorInv]
      simp only [mul_add, mul_smul_comm, hp1_def, hp2_def, hp3_def,
                 h12_or1, h12_or3, h1_sub_r, h10, smul_zero, add_zero, zero_add]

    have term2 : (w * w) • (g.V2 * star g.V3) * z3GradingOperatorInv g w = w • (g.V2 * star g.V3) := by
      dsimp [z3GradingOperatorInv]
      simp only [mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, hp1_def, hp2_def, hp3_def,
                 h23_or1, h23_or2, h2_sub_r, h20, smul_zero, add_zero, zero_add]
      rw [hw4]

    have term3 : w • (g.V3 * star g.V1) * z3GradingOperatorInv g w = w • (g.V3 * star g.V1) := by
      dsimp [z3GradingOperatorInv]
      simp only [mul_add, smul_mul_assoc, mul_smul_comm, hp1_def, hp2_def, hp3_def,
                 h3_sub_r, h31_or2, h31_or3, h30, smul_zero, add_zero]

    have h_add : (g.V1 * star g.V2 + (w * w) • (g.V2 * star g.V3) + w • (g.V3 * star g.V1)) * z3GradingOperatorInv g w =
                 g.V1 * star g.V2 * z3GradingOperatorInv g w + (w * w) • (g.V2 * star g.V3) * z3GradingOperatorInv g w + w • (g.V3 * star g.V1) * z3GradingOperatorInv g w := by noncomm_ring
    rw [h_add, term1, term2, term3]
    dsimp [cyclicSupercharge]
    simp only [smul_add]

  rw [h_left, h_mid]

/-- **Theorem**: Star Unitarity Property of Z₃ Grading Operator. -/
theorem z3GradingOperator_star (hwStar : star w = w * w) (hwStar2 : star (w * w) = w) :
    star (z3GradingOperator g w) = z3GradingOperatorInv g w := by
  have hp1_star : star g.P1 = g.P1 := by dsimp [P1]; simp only [star_mul, star_star]
  have hp2_star : star g.P2 = g.P2 := by dsimp [P2]; simp only [star_mul, star_star]
  have hp3_star : star g.P3 = g.P3 := by dsimp [P3]; simp only [star_mul, star_star]
  have hp0_star : star g.P0 = g.P0 := by dsimp [P0, P1, P2, P3]; simp only [star_sub, star_one, star_mul, star_star]
  dsimp [z3GradingOperator, z3GradingOperatorInv]
  simp only [star_add, star_smul, hp1_star, hp2_star, hp3_star, hp0_star]
  rw [hwStar, hwStar2]

/-- **Master Synthesis**: Non-commutative Z₃ Fractional SUSY Grading Automorphism. -/
theorem master_toeplitz_cuntz_three_z3_grading_synthesis (hw3 : w * w * w = 1) :
    z3GradingOperator g w * z3GradingOperatorInv g w = 1 ∧
    z3GradingOperatorInv g w * z3GradingOperator g w = 1 ∧
    z3GradingOperator g w * z3GradingOperator g w * z3GradingOperator g w = 1 ∧
    z3GradingOperator g w * cyclicSupercharge g * z3GradingOperatorInv g w = w • cyclicSupercharge g := ⟨
  z3GradingOperator_mul_inv g w hw3,
  z3GradingOperator_inv_mul g w hw3,
  z3GradingOperator_cube g w hw3,
  cyclicSupercharge_z3_covariance g w hw3
⟩

end InfoGeometry.Canonical.ToeplitzCuntzThreeZ3GradingBridge
