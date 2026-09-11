import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# A projection-level Cuntz--Toeplitz braid adapter

This file records the algebraic calculation available from two orthogonal
isometries.  The coefficients are real scalars, hence central in the target
algebra.  No `star` operation or C*-unitarity claim is introduced here.
-/

namespace InfoGeometry.Physics.Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

structure CuntzTwoAlgebraData (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]
    where
  S1 : A
  S2 : A
  S1_star : A
  S2_star : A

def CuntzTwoAlgebraLaws (O2 : CuntzTwoAlgebraData A) : Prop :=
  O2.S1_star * O2.S1 = 1 ∧
  O2.S2_star * O2.S2 = 1 ∧
  O2.S1_star * O2.S2 = 0 ∧
  O2.S2_star * O2.S1 = 0 ∧
  O2.S1 * O2.S1_star + O2.S2 * O2.S2_star = 1

def CuntzTwoAlgebra (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] :=
  { O2 : CuntzTwoAlgebraData A // CuntzTwoAlgebraLaws O2 }

namespace CuntzTwoAlgebra

def S1 (O2 : CuntzTwoAlgebra A) : A := O2.1.S1
def S2 (O2 : CuntzTwoAlgebra A) : A := O2.1.S2
def S1_star (O2 : CuntzTwoAlgebra A) : A := O2.1.S1_star
def S2_star (O2 : CuntzTwoAlgebra A) : A := O2.1.S2_star

end CuntzTwoAlgebra

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
  have hO2 : CuntzTwoAlgebraLaws O2.1 := O2.2
  have h11 : O2.S1_star * O2.S1 = 1 := by
    simpa [CuntzTwoAlgebra.S1, CuntzTwoAlgebra.S1_star] using hO2.1
  have h22 : O2.S2_star * O2.S2 = 1 := by
    simpa [CuntzTwoAlgebra.S2, CuntzTwoAlgebra.S2_star] using hO2.2.1
  have h12 : O2.S1_star * O2.S2 = 0 := by
    simpa [CuntzTwoAlgebra.S1, CuntzTwoAlgebra.S1_star,
      CuntzTwoAlgebra.S2] using hO2.2.2.1
  have h21 : O2.S2_star * O2.S1 = 0 := by
    simpa [CuntzTwoAlgebra.S1, CuntzTwoAlgebra.S2,
      CuntzTwoAlgebra.S2_star] using hO2.2.2.2.1
  have hsum : O2.S1 * O2.S1_star + O2.S2 * O2.S2_star = 1 := by
    simpa [CuntzTwoAlgebra.S1, CuntzTwoAlgebra.S2,
      CuntzTwoAlgebra.S1_star, CuntzTwoAlgebra.S2_star] using hO2.2.2.2.2
  have hP₁ : P₁ * P₁ = P₁ := by
    dsimp [P₁]
    calc
      (O2.S1 * O2.S1_star) * (O2.S1 * O2.S1_star) =
          O2.S1 * (O2.S1_star * O2.S1) * O2.S1_star := by
            noncomm_ring
      _ = P₁ := by rw [h11]; simp [P₁]
  have hP₂ : P₂ * P₂ = P₂ := by
    dsimp [P₂]
    calc
      (O2.S2 * O2.S2_star) * (O2.S2 * O2.S2_star) =
          O2.S2 * (O2.S2_star * O2.S2) * O2.S2_star := by
            noncomm_ring
      _ = P₂ := by rw [h22]; simp [P₂]
  have h₁₂ : P₁ * P₂ = 0 := by
    dsimp [P₁, P₂]
    calc
      (O2.S1 * O2.S1_star) * (O2.S2 * O2.S2_star) =
          O2.S1 * (O2.S1_star * O2.S2) * O2.S2_star := by
            noncomm_ring
      _ = 0 := by rw [h12]; simp
  have h₂₁ : P₂ * P₁ = 0 := by
    dsimp [P₁, P₂]
    calc
      (O2.S2 * O2.S2_star) * (O2.S1 * O2.S1_star) =
          O2.S2 * (O2.S2_star * O2.S1) * O2.S1_star := by
            noncomm_ring
      _ = 0 := by rw [h21]; simp
  dsimp [cuntzBraidProjectionOperator]
  change (q₁ • P₁ + q₂ • P₂) * (q₁ • P₁ + q₂ • P₂) = 1
  simp only [add_mul, mul_add, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm, smul_smul, hP₁, hP₂, h₁₂, h₂₁,
    smul_zero, add_zero, zero_add]
  rw [← pow_two q₁, ← pow_two q₂, hq₁, hq₂]
  norm_num
  exact hsum

@[simp] theorem cuntz_braid_projection_one_one
    (O2 : CuntzTwoAlgebra A) :
    cuntzBraidProjectionOperator O2 1 1 = 1 := by
  have hsum : O2.S1 * O2.S1_star + O2.S2 * O2.S2_star = 1 := by
    have hO2 : CuntzTwoAlgebraLaws O2.1 := O2.2
    simpa [CuntzTwoAlgebra.S1, CuntzTwoAlgebra.S2,
      CuntzTwoAlgebra.S1_star, CuntzTwoAlgebra.S2_star] using hO2.2.2.2.2
  simp [cuntzBraidProjectionOperator, hsum]

theorem continuous_cuntzBraidProjectionOperator
    (O2 : CuntzTwoAlgebra A) :
    Continuous (fun p : ℝ × ℝ =>
      cuntzBraidProjectionOperator O2 p.1 p.2) := by
  unfold cuntzBraidProjectionOperator
  refine Continuous.add ?_ ?_
  · exact Continuous.smul continuous_fst continuous_const
  · exact Continuous.smul continuous_snd continuous_const

end InfoGeometry.Physics.Algebra
