/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentEigenspaces
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentSuperbracket
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The native integer grading of a tripotent algebra

The existing `adGrade S k` family is a Mathlib internal direct sum and graded
algebra when `S³ = S`. No second grade carrier is introduced. The signed
bracket has a uniform integer formulation, including intermediate weights
outside `[-2,2]`; those components are the zero submodule.
-/

noncomputable section

namespace InfoGeometry.Core.TripotentAdjoint

open InfoGeometry.Physics.Algebra
open InfoGeometry.Algebra.SupergradedBracket
open InfoGeometry.OperatorAlgebra.PeirceSpine

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The existing integer eigenspaces are multiplicatively graded, even without
tripotence. -/
instance adGradeGradedMonoid (S : A) : SetLike.GradedMonoid (adGrade S) where
  one_mem := by simp [mem_adGrade_iff, adOp]
  mul_mem := mul_mem_adGrade_add

/-- Distinct integer adjoint eigenspaces are independent. -/
theorem adGrade_iSupIndep (S : A) : iSupIndep (adGrade S) := by
  simp_rw [adGrade_eq_eigenspace]
  exact (LieAlgebra.ad ℝ A S).eigenspaces_iSupIndep.comp
    (Int.cast_injective (α := ℝ))

/-- An integer outside the five existing labels has zero grade. -/
theorem adGrade_eq_bot_of_not_mem {S : A} (hS : S * S * S = S) {k : ℤ}
    (hk : k ∉ Set.range fiveGradeValue) : adGrade S k = ⊥ := by
  rw [adGrade_eq_eigenspace]
  apply eigenspace_eq_bot_of_not_mem_fiveGradeValue hS
  rintro ⟨j, hj⟩
  apply hk
  exact ⟨j, Int.cast_injective hj⟩

/-- The native integer grading is supported on the closed interval `[-2,2]`. -/
theorem adGrade_eq_bot_of_outside {S : A} (hS : S * S * S = S) {k : ℤ}
    (hk : k < -2 ∨ 2 < k) : adGrade S k = ⊥ := by
  apply adGrade_eq_bot_of_not_mem hS
  rintro ⟨j, rfl⟩
  cases j <;> norm_num [fiveGradeValue] at hk

/-- The old finite projector ranges are exactly the corresponding integer grades. -/
theorem fiveGradeRange_eq_adGrade {S : A} (hS : S * S * S = S) (k : FiveGrade) :
    fiveGradeRange S k = adGrade S (fiveGradeValue k) := by
  rw [fiveGradeRange_eq_eigenspace hS, adGrade_eq_eigenspace]

/-- Five-component reconstruction proves that the integer eigenspaces span
the entire algebra. -/
theorem iSup_adGrade_eq_top {S : A} (hS : S * S * S = S) :
    (⨆ k : ℤ, adGrade S k) = ⊤ := by
  apply top_unique
  intro x _
  have hm (k : FiveGrade) :
      fiveGradeProjector S k x ∈ ⨆ j : ℤ, adGrade S j := by
    apply (le_iSup (adGrade S) (fiveGradeValue k))
    rw [← fiveGradeRange_eq_adGrade hS]
    exact ⟨x, rfl⟩
  have hrec := fiveGrade_recompose_decompose S x
  change fiveGradeProjector S .negTwo x + fiveGradeProjector S .negOne x +
    fiveGradeProjector S .zero x + fiveGradeProjector S .posOne x +
    fiveGradeProjector S .posTwo x = x at hrec
  rw [← hrec]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (hm .negTwo) (hm .negOne)) (hm .zero)) (hm .posOne))
    (hm .posTwo)

/-- The original algebra is the native internal direct sum of its integer grades. -/
theorem adGrade_isInternal {S : A} (hS : S * S * S = S) :
    DirectSum.IsInternal (adGrade S) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (adGrade_iSupIndep S) (iSup_adGrade_eq_top hS)

/-- A genuine Mathlib graded-algebra structure on the existing integer family. -/
def adGradeGradedAlgebra {S : A} (hS : S * S * S = S) : GradedAlgebra (adGrade S) :=
  (adGrade_isInternal hS).gradedAlgebra

/-- Decomposition preserves the original associative multiplication and unit. -/
def adGradeDecomposeAlgEquiv {S : A} (hS : S * S * S = S) :
    A ≃ₐ[ℝ] DirectSum ℤ (fun k => adGrade S k) :=
  (adGrade_isInternal hS).coeAlgEquiv.symm

/-- Integer degree modulo two, with negative odd integers also odd. -/
def integerGradeParity (k : ℤ) : Bool := decide (k % 2 = 1)

theorem integerGradeParity_add (i j : ℤ) :
    integerGradeParity (i + j) = integerGradeParity i ^^ integerGradeParity j := by
  have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
  have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    simp [integerGradeParity, Int.add_emod, hi, hj, Bool.xor]

/-- The integer parity agrees with the existing middle-projector involution. -/
theorem parityConj_projZero_of_mem_adGrade {S X : A}
    (hS : S * S * S = S) {k : ℤ} (hX : X ∈ adGrade S k) :
    parityConj (projZero S) X = if integerGradeParity k then -X else X := by
  by_cases hk : k ∈ Set.range fiveGradeValue
  · obtain ⟨j, rfl⟩ := hk
    rw [← fiveGradeRange_eq_adGrade hS] at hX
    simpa only [integerGradeParity, ← fiveGradeParity_eq_mod_two] using
      parityConj_projZero_eq_fiveGradeParity hS j hX
  · rw [adGrade_eq_bot_of_not_mem hS hk, Submodule.mem_bot] at hX
    simp [hX, parityConj]

/-- The signed associative bracket lands in the summed integer grade. -/
theorem superBracket_mem_adGrade {S X Y : A} {i j : ℤ}
    (hX : X ∈ adGrade S i) (hY : Y ∈ adGrade S j) :
    superBracket (integerGradeParity i) (integerGradeParity j) X Y ∈
      adGrade S (i + j) := by
  have hXY := mul_mem_adGrade_add hX hY
  have hYX : Y * X ∈ adGrade S (i + j) := by
    simpa only [add_comm] using mul_mem_adGrade_add hY hX
  unfold superBracket anticommutator InfoGeometry.Algebra.SupergradedBracket.commutator
  split_ifs
  · exact (adGrade S (i + j)).add_mem hXY hYX
  · exact (adGrade S (i + j)).sub_mem hXY hYX

/-- Homogeneous signed bracket, with no finite-label sum premise. -/
def adGradeSuperBracket {S : A} {i j : ℤ}
    (X : adGrade S i) (Y : adGrade S j) : adGrade S (i + j) :=
  ⟨superBracket (integerGradeParity i) (integerGradeParity j) (X : A) (Y : A),
    superBracket_mem_adGrade X.property Y.property⟩

/-- Uniform signed Jacobi for the integer grading. The equality is in the
ambient algebra so associative reindexing needs no artificial casts. -/
theorem adGradeSuperBracket_jacobi {S : A} {i j k : ℤ}
    (X : adGrade S i) (Y : adGrade S j) (Z : adGrade S k) :
    gradedSign (R := ℝ) (integerGradeParity i) (integerGradeParity k) •
        (adGradeSuperBracket X (adGradeSuperBracket Y Z) : A) +
      gradedSign (R := ℝ) (integerGradeParity j) (integerGradeParity i) •
        (adGradeSuperBracket Y (adGradeSuperBracket Z X) : A) +
      gradedSign (R := ℝ) (integerGradeParity k) (integerGradeParity j) •
        (adGradeSuperBracket Z (adGradeSuperBracket X Y) : A) = 0 := by
  change gradedSign (R := ℝ) _ _ • superBracket _ (integerGradeParity (j + k))
      (X : A) (superBracket _ _ (Y : A) (Z : A)) +
    gradedSign (R := ℝ) _ _ • superBracket _ (integerGradeParity (k + i))
      (Y : A) (superBracket _ _ (Z : A) (X : A)) +
    gradedSign (R := ℝ) _ _ • superBracket _ (integerGradeParity (i + j))
      (Z : A) (superBracket _ _ (X : A) (Y : A)) = 0
  simp only [integerGradeParity_add]
  exact superBracket_superJacobi (R := ℝ) _ _ _ (X : A) (Y : A) (Z : A)

end InfoGeometry.Core.TripotentAdjoint
