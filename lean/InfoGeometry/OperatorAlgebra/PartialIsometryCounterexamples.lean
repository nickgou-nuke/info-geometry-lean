/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NonCommutativeIsometry
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Basic.Real.Star
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Partial isometries are not closed under arbitrary composition

Two self-adjoint projections in the full real `2 × 2` matrix algebra have a
nonzero product that fails the partial-isometry equation. The calculation
exhibits the nonzero sandwich of the intermediate support commutator from
`Algebra.NonCommutativeIsometry`.

A projection and its nonzero complement provide a separate boundary: two
nonzero partial isometries can have zero product. Matched supports, rather
than nonzeroness alone, are the relevant composition hypothesis.
-/

namespace InfoGeometry.OperatorAlgebra.PartialIsometryCounterexamples

open InfoGeometry.Algebra.NonCommutativity
open scoped Matrix

/-- Orthogonal projection onto the first coordinate axis. -/
def axisProjection : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- Orthogonal projection onto the line spanned by `(1, 1)`. -/
noncomputable def diagonalLineProjection : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

theorem axisProjection_isStarProjection : IsStarProjection axisProjection := by
  constructor
  · change axisProjection * axisProjection = axisProjection
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [axisProjection, Matrix.mul_apply, Fin.sum_univ_two]
  · change star axisProjection = axisProjection
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [axisProjection]

theorem diagonalLineProjection_isStarProjection : IsStarProjection diagonalLineProjection := by
  constructor
  · change diagonalLineProjection * diagonalLineProjection = diagonalLineProjection
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [diagonalLineProjection, Matrix.mul_apply, Fin.sum_univ_two]
  · change star diagonalLineProjection = diagonalLineProjection
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [diagonalLineProjection]

theorem axisProjection_partial_isometry :
    axisProjection * star axisProjection * axisProjection = axisProjection := by
  simp only [axisProjection_isStarProjection.isSelfAdjoint.star_eq,
    axisProjection_isStarProjection.isIdempotentElem.eq]

theorem diagonalLineProjection_partial_isometry :
    diagonalLineProjection * star diagonalLineProjection * diagonalLineProjection =
      diagonalLineProjection := by
  simp only [diagonalLineProjection_isStarProjection.isSelfAdjoint.star_eq,
    diagonalLineProjection_isStarProjection.isIdempotentElem.eq]

theorem ordered_product_ne_zero : axisProjection * diagonalLineProjection ≠ 0 := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [axisProjection, diagonalLineProjection, Matrix.mul_apply, Fin.sum_univ_two] at hentry

theorem projections_not_commute : ¬ Commute axisProjection diagonalLineProjection := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h.eq
  norm_num [axisProjection, diagonalLineProjection, Matrix.mul_apply, Fin.sum_univ_two] at hentry

/-- The composite satisfies a scaled equation, not the partial-isometry equation. -/
theorem ordered_product_cubic :
    (axisProjection * diagonalLineProjection) * star (axisProjection * diagonalLineProjection) *
        (axisProjection * diagonalLineProjection) =
      (1 / 2 : ℝ) • (axisProjection * diagonalLineProjection) := by
  rw [star_mul, axisProjection_isStarProjection.isSelfAdjoint.star_eq,
    diagonalLineProjection_isStarProjection.isSelfAdjoint.star_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axisProjection, diagonalLineProjection, Matrix.mul_apply, Fin.sum_univ_two]

theorem ordered_product_not_partial_isometry :
    (axisProjection * diagonalLineProjection) * star (axisProjection * diagonalLineProjection) *
        (axisProjection * diagonalLineProjection) ≠
      axisProjection * diagonalLineProjection := by
  rw [ordered_product_cubic]
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [axisProjection, diagonalLineProjection, Matrix.mul_apply, Fin.sum_univ_two] at hentry

/-- The failure is exactly the nonzero ordered support residual of the generic owner. -/
theorem support_commutator_sandwich_ne_zero :
    axisProjection *
        (rangeProjection diagonalLineProjection * sourceProjection axisProjection -
          sourceProjection axisProjection * rangeProjection diagonalLineProjection) *
      diagonalLineProjection ≠ 0 := by
  intro h
  exact ordered_product_not_partial_isometry
    ((partial_isometry_mul_iff_sandwich_commutator_eq_zero
      diagonalLineProjection_partial_isometry axisProjection_partial_isometry).mpr h)

theorem axisProjection_ne_zero : axisProjection ≠ 0 := by
  intro h
  exact ordered_product_ne_zero (by rw [h, zero_mul])

theorem diagonalLineProjection_ne_zero : diagonalLineProjection ≠ 0 := by
  intro h
  exact ordered_product_ne_zero (by rw [h, mul_zero])

/-- The complementary nonzero projection is supplied by the native projection API. -/
theorem complement_isStarProjection : IsStarProjection (1 - axisProjection) :=
  axisProjection_isStarProjection.one_sub

theorem complement_ne_zero : 1 - axisProjection ≠ 0 := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) h
  norm_num [axisProjection] at hentry

theorem axisProjection_mul_complement : axisProjection * (1 - axisProjection) = 0 :=
  axisProjection_isStarProjection.mul_one_sub_self

theorem complement_mul_axisProjection : (1 - axisProjection) * axisProjection = 0 :=
  axisProjection_isStarProjection.one_sub_mul_self

end InfoGeometry.OperatorAlgebra.PartialIsometryCounterexamples
