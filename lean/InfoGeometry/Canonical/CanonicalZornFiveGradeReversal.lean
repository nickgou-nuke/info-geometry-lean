import InfoGeometry.Canonical.CanonicalZornFiveGradedClosure

/-!
# Concrete reversal of the canonical five-grade matrix carrier

The matrix Lie algebra used by `CanonicalZornFiveGradedClosure` has a native
grade-reversing involution: negative transpose.  It exchanges the two
conformal endpoints, reverses the weight difference, and preserves the Lie
bracket.
-/

noncomputable section

namespace CanonicalZornFiveGradedClosure

open TKKJordanPairData
open TKKJordanPairData.TKKGrade

def gradeNeg : TKKGrade → TKKGrade
  | m2 => p2
  | m1 => p1
  | z0 => z0
  | p1 => m1
  | p2 => m2

@[simp] theorem weight_gradeNeg (g : TKKGrade) :
    weight (gradeNeg g) = -weight g := by
  cases g <;> rfl

def conformalGradeReversal : ConformalMatrix →ₗ[ℝ] ConformalMatrix where
  toFun A := -Matrix.transpose A
  map_add' A B := by
    ext r c
    simp [Matrix.transpose_apply]
    abel
  map_smul' a A := by
    ext r c
    simp [Matrix.transpose_apply]

@[simp] theorem conformalGradeReversal_apply (A : ConformalMatrix) :
    conformalGradeReversal A = -Matrix.transpose A := rfl

theorem conformalGradeReversal_mem_grade_neg
    {g : TKKGrade} {A : ConformalMatrix}
    (hA : A ∈ conformalGrade g) :
    conformalGradeReversal A ∈ conformalGrade (gradeNeg g) := by
  intro r c hrc
  change -A c r = 0
  have hrc' : indexWeight c - indexWeight r ≠ weight g := by
    intro h
    apply hrc
    rw [weight_gradeNeg]
    linarith
  rw [hA c r hrc']
  simp

theorem conformalGradeReversal_involutive (A : ConformalMatrix) :
    conformalGradeReversal (conformalGradeReversal A) = A := by
  ext r c
  simp [conformalGradeReversal, Matrix.transpose_apply]

theorem conformalGradeReversal_bracket (A B : ConformalMatrix) :
    conformalGradeReversal ⁅A, B⁆ =
      ⁅conformalGradeReversal A, conformalGradeReversal B⁆ := by
  change -(A * B - B * A).transpose =
    (-A.transpose) * (-B.transpose) - (-B.transpose) * (-A.transpose)
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
  noncomm_ring

theorem conformalGradeReversal_five_grade_packet
    {g : TKKGrade} {A : ConformalMatrix}
    (hA : A ∈ conformalGrade g) :
    conformalGradeReversal A ∈ conformalGrade (gradeNeg g) ∧
      conformalGradeReversal (conformalGradeReversal A) = A := by
  exact ⟨conformalGradeReversal_mem_grade_neg hA,
    conformalGradeReversal_involutive A⟩

end CanonicalZornFiveGradedClosure
