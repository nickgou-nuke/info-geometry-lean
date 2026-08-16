import InfoGeometry.Canonical.CanonicalZornFiveGradedClosure
import InfoGeometry.Core.SymmetricLie

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

@[simp] theorem gradeNeg_involutive (g : TKKGrade) :
    gradeNeg (gradeNeg g) = g := by
  cases g <;> rfl

theorem gradeNeg_eq_self_iff (g : TKKGrade) :
    gradeNeg g = g ↔ g = z0 := by
  cases g <;> simp [gradeNeg]

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
  simp [conformalGradeReversal]

theorem conformalGradeReversal_bracket (A B : ConformalMatrix) :
    conformalGradeReversal ⁅A, B⁆ =
      ⁅conformalGradeReversal A, conformalGradeReversal B⁆ := by
  change -(A * B - B * A).transpose =
    (-A.transpose) * (-B.transpose) - (-B.transpose) * (-A.transpose)
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
  noncomm_ring

/-! The concrete reversal is now packaged as the repository's native
real Lie-automorphism owner, rather than remaining a bare linear map. -/

noncomputable def conformalGradeReversalLieHom :
    ConformalMatrix →ₗ⁅ℝ⁆ ConformalMatrix where
  toFun := conformalGradeReversal
  map_add' := conformalGradeReversal.map_add'
  map_smul' := conformalGradeReversal.map_smul'
  map_lie' := by
    intro A B
    exact conformalGradeReversal_bracket A B

noncomputable def conformalGradeReversalLieAut :
    InfoGeometry.Core.InvolutiveLieAut ConformalMatrix := by
  let f : ConformalMatrix ≃ₗ⁅ℝ⁆ ConformalMatrix :=
    LieEquiv.ofBijective conformalGradeReversalLieHom (by
      constructor
      · intro A B h
        change conformalGradeReversal A = conformalGradeReversal B at h
        have h' := congrArg conformalGradeReversal h
        simpa [conformalGradeReversal_involutive] using h'
      · intro A
        refine ⟨conformalGradeReversal A, ?_⟩
        exact conformalGradeReversal_involutive A)
  refine ⟨f, ?_⟩
  intro A
  exact conformalGradeReversal_involutive A

@[simp] theorem conformalGradeReversalLieAut_apply (A : ConformalMatrix) :
    conformalGradeReversalLieAut.1 A = conformalGradeReversal A := by
  rfl

/-- The grade-reversing Lie automorphism is an involutive group element. -/
theorem conformalGradeReversalLieAut_mul_self :
    conformalGradeReversalLieAut.1.trans
        conformalGradeReversalLieAut.1 =
      (LieEquiv.refl : ConformalMatrix ≃ₗ⁅ℝ⁆ ConformalMatrix) := by
  apply LieEquiv.ext
  intro A
  simp

/-! The same concrete reversal is now exposed as a native symmetric Lie
algebra, so its even/odd Cartan sectors use the existing Core machinery. -/

noncomputable def conformalGradeReversalSymmetricLie :
    InfoGeometry.Core.SymmetricLieAlgebra ConformalMatrix :=
  InfoGeometry.Core.SymmetricLieAlgebra.ofInvolutiveLieAut
    conformalGradeReversalLieAut

@[simp] theorem conformalGradeReversalSymmetricLie_theta_apply
    (A : ConformalMatrix) :
    (conformalGradeReversalSymmetricLie).θ A =
      conformalGradeReversal A := by
  rfl

theorem conformalGradeReversal_symmetric_pair_properties :
    (∀ {A B},
      A ∈ (conformalGradeReversalSymmetricLie).evenLieSubalgebra →
      B ∈ (conformalGradeReversalSymmetricLie).evenLieSubalgebra →
      ⁅A, B⁆ ∈ (conformalGradeReversalSymmetricLie).evenLieSubalgebra) ∧
    (∀ {A B},
      A ∈ (conformalGradeReversalSymmetricLie).evenLieSubalgebra →
      B ∈ (conformalGradeReversalSymmetricLie).oddSubmodule →
      ⁅A, B⁆ ∈ (conformalGradeReversalSymmetricLie).oddSubmodule) ∧
    (∀ {A B},
      A ∈ (conformalGradeReversalSymmetricLie).oddSubmodule →
      B ∈ (conformalGradeReversalSymmetricLie).oddSubmodule →
      ⁅A, B⁆ ∈ (conformalGradeReversalSymmetricLie).evenLieSubalgebra) :=
  InfoGeometry.Core.SymmetricLieAlgebra.symmetric_pair_properties
    conformalGradeReversalSymmetricLie

theorem conformalGradeReversalLieAut_reverses_grade
    {g : TKKGrade} {A : ConformalMatrix}
    (hA : A ∈ conformalGrade g) :
    conformalGradeReversalLieAut.1 A ∈ conformalGrade (gradeNeg g) := by
  rw [conformalGradeReversalLieAut_apply]
  exact conformalGradeReversal_mem_grade_neg hA

theorem conformalGradeReversal_bracket_mem_grade_neg
    {i j k : TKKGrade}
    (hijk : gradeAdd i j = some k)
    {A B : ConformalMatrix}
    (hA : A ∈ conformalGrade i)
    (hB : B ∈ conformalGrade j) :
    conformalGradeReversal ⁅A, B⁆ ∈ conformalGrade (gradeNeg k) := by
  exact conformalGradeReversal_mem_grade_neg
    (bracket_grade_closed canonicalFiveGradedLieAlgebra hijk hA hB)

theorem conformalGradeReversal_bracket_of_images_mem_grade_neg
    {i j k : TKKGrade}
    (hijk : gradeAdd i j = some k)
    {A B : ConformalMatrix}
    (hA : A ∈ conformalGrade i)
    (hB : B ∈ conformalGrade j) :
    ⁅conformalGradeReversal A, conformalGradeReversal B⁆ ∈
      conformalGrade (gradeNeg k) := by
  rw [← conformalGradeReversal_bracket A B]
  exact conformalGradeReversal_bracket_mem_grade_neg hijk hA hB

theorem conformalGradeReversal_bracket_eq_zero_of_gradeAdd_none
    {i j : TKKGrade}
    (hij : gradeAdd i j = none)
    {A B : ConformalMatrix}
    (hA : A ∈ conformalGrade i)
    (hB : B ∈ conformalGrade j) :
    conformalGradeReversal ⁅A, B⁆ = 0 := by
  rw [bracket_grade_outside_zero canonicalFiveGradedLieAlgebra hij hA hB]
  exact conformalGradeReversal.map_zero

theorem conformalGradeReversal_bracket_of_images_eq_zero_of_gradeAdd_none
    {i j : TKKGrade}
    (hij : gradeAdd i j = none)
    {A B : ConformalMatrix}
    (hA : A ∈ conformalGrade i)
    (hB : B ∈ conformalGrade j) :
    ⁅conformalGradeReversal A, conformalGradeReversal B⁆ = 0 := by
  rw [← conformalGradeReversal_bracket A B]
  exact conformalGradeReversal_bracket_eq_zero_of_gradeAdd_none hij hA hB

theorem conformalGradeReversal_five_grade_packet
    {g : TKKGrade} {A : ConformalMatrix}
    (hA : A ∈ conformalGrade g) :
    conformalGradeReversal A ∈ conformalGrade (gradeNeg g) ∧
      conformalGradeReversal (conformalGradeReversal A) = A := by
  exact ⟨conformalGradeReversal_mem_grade_neg hA,
    conformalGradeReversal_involutive A⟩

end CanonicalZornFiveGradedClosure
