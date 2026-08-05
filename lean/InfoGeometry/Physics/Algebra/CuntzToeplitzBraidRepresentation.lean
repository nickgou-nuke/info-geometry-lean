import Mathlib

/-!
# A projection-level Cuntz--Toeplitz braid adapter

This file records the algebraic calculation available from two orthogonal
isometries.  The coefficients are real scalars, hence central in the target
algebra.  No `star` operation or C*-unitarity claim is introduced here.
-/

namespace InfoGeometry.Physics.Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

structure CuntzTwoAlgebra (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]
    where
  S1 : A
  S2 : A
  S1_star : A
  S2_star : A
  hS1_iso : S1_star * S1 = 1
  hS2_iso : S2_star * S2 = 1
  hS1S2_ortho : S1_star * S2 = 0
  hS2S1_ortho : S2_star * S1 = 0
  h_completeness : S1 * S1_star + S2 * S2_star = 1

def cuntzBraidProjectionOperator
    (O2 : CuntzTwoAlgebra A) (q₁ q₂ : ℝ) : A :=
  q₁ • (O2.S1 * O2.S1_star) +
    q₂ • (O2.S2 * O2.S2_star)

theorem cuntz_braid_projection_square
    (O2 : CuntzTwoAlgebra A) (q₁ q₂ : ℝ)
    (hq₁ : q₁ ^ 2 = 1) (hq₂ : q₂ ^ 2 = 1) :
    cuntzBraidProjectionOperator O2 q₁ q₂ *
        cuntzBraidProjectionOperator O2 q₁ q₂ = 1 := by
  let P₁ : A := O2.S1 * O2.S1_star
  let P₂ : A := O2.S2 * O2.S2_star
  have hP₁ : P₁ * P₁ = P₁ := by
    dsimp [P₁]
    calc
      (O2.S1 * O2.S1_star) * (O2.S1 * O2.S1_star) =
          O2.S1 * (O2.S1_star * O2.S1) * O2.S1_star := by
            noncomm_ring
      _ = P₁ := by rw [O2.hS1_iso]; simp [P₁]
  have hP₂ : P₂ * P₂ = P₂ := by
    dsimp [P₂]
    calc
      (O2.S2 * O2.S2_star) * (O2.S2 * O2.S2_star) =
          O2.S2 * (O2.S2_star * O2.S2) * O2.S2_star := by
            noncomm_ring
      _ = P₂ := by rw [O2.hS2_iso]; simp [P₂]
  have h₁₂ : P₁ * P₂ = 0 := by
    dsimp [P₁, P₂]
    calc
      (O2.S1 * O2.S1_star) * (O2.S2 * O2.S2_star) =
          O2.S1 * (O2.S1_star * O2.S2) * O2.S2_star := by
            noncomm_ring
      _ = 0 := by rw [O2.hS1S2_ortho]; simp
  have h₂₁ : P₂ * P₁ = 0 := by
    dsimp [P₁, P₂]
    calc
      (O2.S2 * O2.S2_star) * (O2.S1 * O2.S1_star) =
          O2.S2 * (O2.S2_star * O2.S1) * O2.S1_star := by
            noncomm_ring
      _ = 0 := by rw [O2.hS2S1_ortho]; simp
  dsimp [cuntzBraidProjectionOperator]
  change (q₁ • P₁ + q₂ • P₂) * (q₁ • P₁ + q₂ • P₂) = 1
  simp only [add_mul, mul_add, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm, smul_smul, hP₁, hP₂, h₁₂, h₂₁,
    smul_zero, add_zero, zero_add]
  rw [← pow_two q₁, ← pow_two q₂, hq₁, hq₂]
  norm_num
  exact O2.h_completeness

@[simp] theorem cuntz_braid_projection_one_one
    (O2 : CuntzTwoAlgebra A) :
    cuntzBraidProjectionOperator O2 1 1 = 1 := by
  simp [cuntzBraidProjectionOperator, O2.h_completeness]

theorem continuous_cuntzBraidProjectionOperator
    (O2 : CuntzTwoAlgebra A) :
    Continuous (fun p : ℝ × ℝ =>
      cuntzBraidProjectionOperator O2 p.1 p.2) := by
  unfold cuntzBraidProjectionOperator
  refine Continuous.add ?_ ?_
  · exact Continuous.smul continuous_fst continuous_const
  · exact Continuous.smul continuous_snd continuous_const

end InfoGeometry.Physics.Algebra
