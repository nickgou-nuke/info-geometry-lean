/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceGrading
import InfoGeometry.Core.SuperGrassmannianSusy
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.Physics.Algebra.TripotentFiveGradingDecomposition

/-!
# Tripotent five-grade projectors and zero-mode Peirce parity

For the existing polynomial projector `P₀ = projZero T = 1 - T*T`, the
existing Peirce odd map is the sum of the two adjoint-weight projectors of
weights `-1` and `1`. Its even map is the sum of weights `-2`, `0`, and `2`.
These two regrouping identities are polynomial identities for every `T`.

Under `T*T*T = T`, `projZero_idempotent` supplies the idempotence needed by
the existing Peirce grading owner. Its reflection conjugation acts by the
corresponding sign on every native `fiveGradeRange T k`. The odd sum
satisfies the existing Grassmannian tangent equation, and the even sum
commutes with the zero-mode projector.

All coefficients and inputs remain in an arbitrary associative real algebra.
In particular `T*T` is an operator, not a scalar spectral parameter. For a
nonassociative carrier this module applies to its associative endomorphism
algebra; it does not replace the carrier's own multiplication by composition.
The zero-mode cut differs from the positive/negative eigenspace cut: the
extreme adjoint grades `±2` are even for this cut.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Physics.Algebra
open InfoGeometry.Core.SuperGrassmannianSusy

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The complement of the zero-mode polynomial is the sum of the two
nonzero spectral polynomials. No tripotence assumption is needed. -/
theorem one_sub_projZero_eq_projPos_add_projNeg (T : A) :
    1 - projZero T = projPos T + projNeg T := by
  rw [projPos_add_projNeg]
  unfold projZero
  abel

/-- The two odd adjoint weights are precisely the cross-corners of `P₀`. -/
theorem oddGrade_projZero (T X : A) :
    oddGrade (projZero T) X =
      gradeNegOneProjector T X + gradePosOneProjector T X := by
  simp only [oddGrade, one_sub_projZero_eq_projPos_add_projNeg,
    gradeNegOneProjector, gradePosOneProjector, LinearMap.add_apply,
    jointPeirceProjector_apply, peirceProjector_zero,
    peirceProjector_pos, peirceProjector_neg]
  noncomm_ring

/-- The three even adjoint weights are precisely the diagonal blocks of `P₀`. -/
theorem evenGrade_projZero (T X : A) :
    evenGrade (projZero T) X =
      gradeNegTwoProjector T X + gradeZeroProjector T X +
        gradePosTwoProjector T X := by
  simp only [evenGrade, one_sub_projZero_eq_projPos_add_projNeg,
    gradeNegTwoProjector, gradeZeroProjector, gradePosTwoProjector,
    LinearMap.add_apply, jointPeirceProjector_apply,
    peirceProjector_zero, peirceProjector_pos, peirceProjector_neg]
  noncomm_ring

/-- The zero-mode reflection retains the full square of `T`. -/
theorem invS_projZero_eq (T : A) :
    invS (projZero T) = 1 - (2 : ℤ) • (T * T) := by
  simp only [invS, projZero, two_zsmul]
  noncomm_ring

/-- Reuse the owned zero-projector idempotence to obtain its reflection. -/
theorem invS_projZero_sq {T : A} (hT : T * T * T = T) :
    invS (projZero T) * invS (projZero T) = 1 := by
  have hS : invS (projZero T) =
      InfoGeometry.Core.PeirceGrading.reflection (projZero T) := by
    simp only [invS, InfoGeometry.Core.PeirceGrading.reflection]
    noncomm_ring
  rw [hS]
  exact InfoGeometry.Core.PeirceGrading.reflection_sq (projZero_idempotent hT)

/-- Conjugation is the signed sum of all five native projector components. -/
theorem parityConj_projZero_decomposition (T X : A) :
    parityConj (projZero T) X =
      (gradeNegTwoProjector T X + gradeZeroProjector T X +
          gradePosTwoProjector T X) -
        (gradeNegOneProjector T X + gradePosOneProjector T X) := by
  rw [← evenGrade_projZero, ← oddGrade_projZero]
  have hS : invS (projZero T) =
      InfoGeometry.Core.PeirceGrading.reflection (projZero T) := by
    simp only [invS, InfoGeometry.Core.PeirceGrading.reflection]
    noncomm_ring
  rw [parityConj, hS]
  simpa only [InfoGeometry.Core.PeirceGrading.even_apply,
    InfoGeometry.Core.PeirceGrading.odd_apply, evenGrade, oddGrade] using
    InfoGeometry.Core.PeirceGrading.conjugate_eq (projZero T) X

/-- Every projected component has its grade-modulo-two conjugation sign. -/
theorem parityConj_projZero_fiveGradeProjector {T : A}
    (hT : T * T * T = T) (k : FiveGrade) (X : A) :
    parityConj (projZero T) (fiveGradeProjector T k X) =
      if k = .negOne ∨ k = .posOne then -(fiveGradeProjector T k X)
      else fiveGradeProjector T k X := by
  have hproj (i j : FiveGrade) :
      fiveGradeProjector T i (fiveGradeProjector T j X) =
        if i = j then fiveGradeProjector T j X else 0 := by
    change (fiveGradeProjector T i * fiveGradeProjector T j) X = _
    by_cases hij : i = j
    · subst j
      rw [fiveGradeProjector_idempotent hT]
      simp
    · rw [fiveGradeProjector_mul_eq_zero_of_ne hT hij]
      simp [hij]
  rw [parityConj_projZero_decomposition]
  change
    (fiveGradeProjector T .negTwo (fiveGradeProjector T k X) +
        fiveGradeProjector T .zero (fiveGradeProjector T k X) +
        fiveGradeProjector T .posTwo (fiveGradeProjector T k X)) -
      (fiveGradeProjector T .negOne (fiveGradeProjector T k X) +
        fiveGradeProjector T .posOne (fiveGradeProjector T k X)) = _
  cases k <;> simp only [hproj] <;> simp

/-- The sign law holds for every member of each native grade range. -/
theorem parityConj_projZero_of_mem_fiveGradeRange {T X : A}
    (hT : T * T * T = T) (k : FiveGrade)
    (hX : X ∈ fiveGradeRange T k) :
    parityConj (projZero T) X =
      if k = .negOne ∨ k = .posOne then -X else X := by
  rcases hX with ⟨Y, rfl⟩
  exact parityConj_projZero_fiveGradeProjector hT k Y

/-- The full even five-grade part commutes with the actual zero projector. -/
theorem evenGrades_commute_projZero {T : A}
    (hT : T * T * T = T) (X : A) :
    Commute (projZero T)
      (gradeNegTwoProjector T X + gradeZeroProjector T X +
        gradePosTwoProjector T X) := by
  rw [← evenGrade_projZero]
  exact (InfoGeometry.Core.PeirceGrading.mem_even_iff
    (projZero_idempotent hT)).1 ⟨X, rfl⟩

/-- The complete odd five-grade part is a Grassmannian tangent at `P₀`. -/
theorem oddGrades_isGrassmannianTangent {T : A}
    (hT : T * T * T = T) (X : A) :
    IsGrassmannianTangent (projZero T)
      (gradeNegOneProjector T X + gradePosOneProjector T X) := by
  rw [← oddGrade_projZero]
  exact (InfoGeometry.Core.PeirceGrading.mem_odd_iff
    (projZero_idempotent hT)).1
      ⟨X, InfoGeometry.Core.PeirceGrading.odd_apply (projZero T) X⟩

/-- The Grassmannian tangent equation characterizes the full odd grade sum. -/
theorem isGrassmannianTangent_iff_oddGrades_fixed {T : A}
    (hT : T * T * T = T) (X : A) :
    IsGrassmannianTangent (projZero T) X ↔
      gradeNegOneProjector T X + gradePosOneProjector T X = X := by
  rw [← oddGrade_projZero]
  have hp : IsIdempotentElem (projZero T) := projZero_idempotent hT
  simpa only [IsGrassmannianTangent, jordanProd,
    InfoGeometry.Core.PeirceGrading.odd_apply, oddGrade] using
    (InfoGeometry.Core.PeirceGrading.mem_odd_iff (p := projZero T) (x := X) hp).symm.trans
      (LinearMap.IsIdempotentElem.mem_range_iff
        (InfoGeometry.Core.PeirceGrading.odd_idempotent hp))

end InfoGeometry.OperatorAlgebra.PeirceSpine
