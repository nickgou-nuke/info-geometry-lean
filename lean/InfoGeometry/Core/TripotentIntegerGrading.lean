/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentEigenspaces
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The native integer grading of a tripotent adjoint

The homogeneous submodules are the existing `adGrade S k`. Their direct sum
is internal, and their actual multiplication gives a native `GradedAlgebra`.
The index is all of `ℤ`; components outside the five weights are zero.
No finite-dimensionality or nonzero-occurrence hypothesis is imposed.
-/

noncomputable section

namespace InfoGeometry.Core.TripotentAdjoint

open InfoGeometry.Physics.Algebra
open scoped DirectSum

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The existing integer component agrees with the existing finite label. -/
theorem adGrade_fiveGradeValue {S : A} (hS : S * S * S = S) (k : FiveGrade) :
    adGrade S (fiveGradeValue k) = fiveGradeRange S k := by
  rw [adGrade_eq_eigenspace, fiveGradeRange_eq_eigenspace hS]

/-- Multiplication and the unit on the actual integer eigenspaces. -/
instance adGradeGradedMonoid (S : A) : SetLike.GradedMonoid (adGrade S) where
  one_mem := by
    rw [mem_adGrade_iff]
    simp [adOp]
  mul_mem _ _ _ _ hx hy := mul_mem_adGrade_add hx hy

/-- Distinct integer eigenspaces are independent over the real field. -/
theorem adGrade_iSupIndep (S : A) : iSupIndep (adGrade S) := by
  have hgrades : adGrade S =
      (fun k : ℤ => (LieAlgebra.ad ℝ A S).eigenspace (k : ℝ)) := by
    funext k
    exact adGrade_eq_eigenspace S k
  rw [hgrades]
  exact (LieAlgebra.ad ℝ A S).eigenspaces_iSupIndep.comp
    (show Function.Injective (fun k : ℤ => (k : ℝ)) from Int.cast_injective)

/-- The five existing polynomial components span every element of the algebra. -/
theorem adGrade_iSup_eq_top {S : A} (hS : S * S * S = S) :
    (⨆ k : ℤ, adGrade S k) = ⊤ := by
  apply top_unique
  intro x _
  have hc (k : FiveGrade) :
      fiveGradeProjector S k x ∈ ⨆ n : ℤ, adGrade S n := by
    apply (le_iSup (adGrade S) (fiveGradeValue k))
    rw [adGrade_fiveGradeValue hS]
    exact ⟨x, rfl⟩
  have hr := fiveGrade_recompose_decompose S x
  change fiveGradeProjector S .negTwo x + fiveGradeProjector S .negOne x +
    fiveGradeProjector S .zero x + fiveGradeProjector S .posOne x +
    fiveGradeProjector S .posTwo x = x at hr
  rw [← hr]
  exact add_mem (add_mem (add_mem (add_mem (hc .negTwo) (hc .negOne))
    (hc .zero)) (hc .posOne)) (hc .posTwo)

/-- The integer-indexed eigenspace decomposition is an actual internal direct sum. -/
theorem adGrade_isInternal {S : A} (hS : S * S * S = S) :
    DirectSum.IsInternal (adGrade S) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (adGrade_iSupIndep S) (adGrade_iSup_eq_top hS)

/-- The constructed Mathlib graded algebra, on the original algebra carrier. -/
def tripotentIntegerGradedAlgebra {S : A} (hS : S * S * S = S) :
    GradedAlgebra (adGrade S) :=
  (adGrade_isInternal hS).gradedAlgebra

/-- The native external direct sum is algebra-isomorphic to the original carrier. -/
def tripotentIntegerDirectSumEquiv {S : A} (hS : S * S * S = S) :
    (⨁ k : ℤ, adGrade S k) ≃ₐ[ℝ] A :=
  (adGrade_isInternal hS).coeAlgEquiv

/-- Components outside the five integer weights vanish. -/
theorem adGrade_eq_bot_of_not_mem {S : A} (hS : S * S * S = S)
    {k : ℤ} (hk : k ∉ Set.range fiveGradeValue) : adGrade S k = ⊥ := by
  rw [adGrade_eq_eigenspace]
  apply eigenspace_eq_bot_of_not_mem_fiveGradeValue hS
  rintro ⟨i, hi⟩
  apply hk
  refine ⟨i, ?_⟩
  change (fiveGradeValue i : ℝ) = (k : ℝ) at hi
  exact_mod_cast hi

/-- In particular, the integer grading has support in the interval `[-2,2]`. -/
theorem adGrade_eq_bot_of_outside {S : A} (hS : S * S * S = S)
    {k : ℤ} (hk : k < -2 ∨ 2 < k) : adGrade S k = ⊥ := by
  apply adGrade_eq_bot_of_not_mem hS
  rintro ⟨i, rfl⟩
  cases i <;> norm_num [fiveGradeValue] at hk

/-- Opposite degrees give a degree-zero composite without either factor
being required to centralize the tripotent. -/
theorem opposite_degree_product_commute {S X Y : A} {k : ℤ}
    (hX : X ∈ adGrade S k) (hY : Y ∈ adGrade S (-k)) :
    Commute S (X * Y) := by
  have h := mul_mem_adGrade_add hX hY
  rw [add_neg_cancel, mem_adGrade_iff] at h
  change S * (X * Y) = (X * Y) * S
  simpa only [Int.cast_zero, zero_smul, adOp, sub_eq_zero] using h

end InfoGeometry.Core.TripotentAdjoint
