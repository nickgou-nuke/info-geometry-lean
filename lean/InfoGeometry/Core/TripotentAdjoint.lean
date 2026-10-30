/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.Algebra.TripotentFiveGradingDecomposition
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Native adjoint calculus for a tripotent

The owned five-range decomposition acts on every element of the associative
algebra. Its five weights annihilate the native adjoint endomorphism by the
polynomial `X⁵ - 5 X³ + 4 X`. This is an annihilating polynomial, with no
claim that all five weights occur in every algebra.
-/

namespace InfoGeometry.Core.TripotentAdjoint

open InfoGeometry.Physics.Algebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The existing left-minus-right operator is the native adjoint map. -/
theorem adLinear_eq_ad (t : A) : adLinear t = LieAlgebra.ad ℝ A t := by
  ext x
  rfl

/-- The repository integer grades are native real eigenspaces. -/
theorem adGrade_eq_eigenspace (t : A) (k : ℤ) :
    adGrade t k = (LieAlgebra.ad ℝ A t).eigenspace (k : ℝ) := by
  ext x
  rw [mem_adGrade_iff, Module.End.mem_eigenspace_iff]
  rfl

/-- Every joint Peirce projector commutes with the native adjoint operator. -/
theorem jointPeirceProjector_commute_ad {t : A} (ht : t * t * t = t)
    (left right : PeirceSign) :
    Commute (jointPeirceProjector t left right) (LieAlgebra.ad ℝ A t) := by
  change _ * _ = _ * _
  apply LinearMap.ext
  intro x
  change peirceProjector t left * ((t * x - x * t) * peirceProjector t right) =
    t * (peirceProjector t left * (x * peirceProjector t right)) -
      (peirceProjector t left * (x * peirceProjector t right)) * t
  have hl : peirceProjector t left * t = t * peirceProjector t left := by
    rw [peirceProjector_mul_e ht, e_mul_peirceProjector ht]
  have hr : t * peirceProjector t right = peirceProjector t right * t := by
    rw [e_mul_peirceProjector ht, peirceProjector_mul_e ht]
  calc
    _ = (peirceProjector t left * t) * (x * peirceProjector t right) -
        peirceProjector t left * (x * (t * peirceProjector t right)) := by
      simp only [sub_mul, mul_sub, mul_assoc]
    _ = (t * peirceProjector t left) * (x * peirceProjector t right) -
        peirceProjector t left * (x * (peirceProjector t right * t)) := by
      rw [hl, hr]
    _ = _ := by simp only [mul_assoc]

/-- The existing grouped projectors also commute with the adjoint. -/
theorem fiveGradeProjector_commute_ad {t : A} (ht : t * t * t = t)
    (k : FiveGrade) :
    Commute (fiveGradeProjector t k) (LieAlgebra.ad ℝ A t) := by
  cases k with
  | negTwo => exact jointPeirceProjector_commute_ad ht .neg .pos
  | negOne =>
      exact (jointPeirceProjector_commute_ad ht .zero .pos).add_left
        (jointPeirceProjector_commute_ad ht .neg .zero)
  | zero =>
      exact ((jointPeirceProjector_commute_ad ht .pos .pos).add_left
        (jointPeirceProjector_commute_ad ht .zero .zero)).add_left
          (jointPeirceProjector_commute_ad ht .neg .neg)
  | posOne =>
      exact (jointPeirceProjector_commute_ad ht .pos .zero).add_left
        (jointPeirceProjector_commute_ad ht .zero .neg)
  | posTwo => exact jointPeirceProjector_commute_ad ht .pos .neg

/-- Native powers act by powers of the weight on an existing grade component. -/
theorem ad_pow_apply_fiveGradeProjector {t : A} (ht : t * t * t = t)
    (k : FiveGrade) (x : A) (n : ℕ) :
    (LieAlgebra.ad ℝ A t ^ n) (fiveGradeProjector t k x) =
      (fiveGradeValue k : ℝ) ^ n • fiveGradeProjector t k x := by
  by_cases hx : fiveGradeProjector t k x = 0
  · simp only [hx, map_zero, smul_zero]
  · have h : (LieAlgebra.ad ℝ A t).HasEigenvector
        (fiveGradeValue k : ℝ) (fiveGradeProjector t k x) :=
      ⟨Module.End.mem_eigenspace_iff.mpr
        (mem_fiveGradeRange_implies_adjoint_eigen ht k ⟨x, rfl⟩), hx⟩
    exact h.pow_apply n

/-- The quintic vanishes on each of the five owned projector ranges. -/
theorem ad_quintic_apply_fiveGradeProjector {t : A} (ht : t * t * t = t)
    (k : FiveGrade) (x : A) :
    (LieAlgebra.ad ℝ A t ^ 5 - (5 : ℝ) • LieAlgebra.ad ℝ A t ^ 3 +
      (4 : ℝ) • LieAlgebra.ad ℝ A t) (fiveGradeProjector t k x) = 0 := by
  have h1 : LieAlgebra.ad ℝ A t (fiveGradeProjector t k x) =
      (fiveGradeValue k : ℝ) • fiveGradeProjector t k x :=
    mem_fiveGradeRange_implies_adjoint_eigen ht k ⟨x, rfl⟩
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    ad_pow_apply_fiveGradeProjector ht k x 5,
    ad_pow_apply_fiveGradeProjector ht k x 3, h1, smul_smul]
  rw [← sub_smul, ← add_smul]
  cases k <;> norm_num [fiveGradeValue]

/-- The native inner derivation of a tripotent satisfies the quintic on the full algebra. -/
theorem ad_quintic {t : A} (ht : t * t * t = t) :
    LieAlgebra.ad ℝ A t ^ 5 - (5 : ℝ) • LieAlgebra.ad ℝ A t ^ 3 +
      (4 : ℝ) • LieAlgebra.ad ℝ A t = 0 := by
  apply LinearMap.ext
  intro x
  have hrec := fiveGrade_recompose_decompose t x
  change fiveGradeProjector t .negTwo x + fiveGradeProjector t .negOne x +
      fiveGradeProjector t .zero x + fiveGradeProjector t .posOne x +
      fiveGradeProjector t .posTwo x = x at hrec
  change (LieAlgebra.ad ℝ A t ^ 5 - (5 : ℝ) • LieAlgebra.ad ℝ A t ^ 3 +
    (4 : ℝ) • LieAlgebra.ad ℝ A t) x = 0
  rw [← hrec]
  simp only [map_add, ad_quintic_apply_fiveGradeProjector ht, add_zero]

end InfoGeometry.Core.TripotentAdjoint
