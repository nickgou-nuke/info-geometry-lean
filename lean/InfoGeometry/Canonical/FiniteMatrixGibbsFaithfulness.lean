/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

/-!
# Faithfulness of the constructed finite Gibbs functional

The density is the existing matrix continuous-functional-calculus exponential.
Its positivity and invertibility prove that the weighted matrix trace detects
every nonzero squared observable.  No separate faithful-state witness is used.
-/

noncomputable section
open scoped MatrixOrder ComplexOrder

namespace InfoGeometry.Canonical.FiniteMatrixGibbsFaithfulness

open FiniteMatrixGibbsFunctional

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- A positive invertible matrix density gives a faithful weighted trace. -/
theorem weightedTrace_star_mul_self_eq_zero_iff
    (D : Matrix n n ℂ) (hD : D.PosSemidef) (hu : IsUnit D)
    (X : Matrix n n ℂ) :
    weightedTrace D (star X * X) = 0 ↔ X = 0 := by
  constructor
  · intro hz
    obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hD.nonneg
    have htrace : Matrix.trace (D * (star X * X)) =
        Matrix.trace (star (X * star S) * (X * star S)) := by
      rw [hS]
      calc
        Matrix.trace (star S * S * (star X * X)) =
            Matrix.trace (S * (star X * X) * star S) :=
          (Matrix.trace_mul_cycle S (star X * X) (star S)).symm
        _ = Matrix.trace (star (X * star S) * (X * star S)) := by
          simp only [star_mul, star_star, mul_assoc]
    have hz' : Matrix.trace (star (X * star S) * (X * star S)) = 0 := by
      rw [← htrace]
      exact hz
    have hXS : X * star S = 0 :=
      Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz'
    apply hu.mul_left_eq_zero.mp
    calc
      X * D = (X * star S) * S := by rw [hS, mul_assoc]
      _ = 0 := by rw [hXS, zero_mul]
  · rintro rfl
    simp only [star_zero, zero_mul, map_zero]

/-- The existing normalized Gibbs functional is faithful for every real β. -/
theorem gibbsFunctional_star_mul_self_eq_zero_iff
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ)
    (X : Matrix n n ℂ) :
    gibbsFunctional H hH β (star X * X) = 0 ↔ X = 0 := by
  rw [gibbsFunctional_apply, mul_eq_zero]
  have hpart : (Matrix.trace (gibbsDensity H hH β))⁻¹ ≠ 0 :=
    inv_ne_zero (gibbsPartition_ne_zero H hH β)
  simp only [hpart, false_or]
  exact weightedTrace_star_mul_self_eq_zero_iff (gibbsDensity H hH β)
    (Matrix.nonneg_iff_posSemidef.mp (gibbsDensity_nonneg H hH β))
    (gibbsDensity_isUnit H hH β) X

end InfoGeometry.Canonical.FiniteMatrixGibbsFaithfulness
