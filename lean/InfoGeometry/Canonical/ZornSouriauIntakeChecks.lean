/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Lie.ZornChiralCircularFourVectorOperators
import InfoGeometry.Algebraic.CartanSouriauActionGroupoid
import InfoGeometry.Algebraic.CotangentBilinearGraph
import InfoGeometry.Analytic.FiniteNegativeLogPartition

/-!
# Nonzero and degenerate cases for the Zorn/Souriau intake

These cases exercise both signs of the nonzero split norm, a nonzero null
phase element, the zero element, genuinely noncommuting regular operators,
and a nontrivial affine cocycle in mathlib's native groupoid. The bilinear
owner separately retains the explicit `3 ≠ -1` graph-sign counterexample,
and the negative-log owner retains the singleton affine degeneracy.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornSouriauIntakeChecks

open CategoryTheory
open InfoGeometry.Lie.ZornChiralCircularFourVectorOperators
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Algebraic.CartanSouriauAffineCocycle

theorem positive_norm_operator_bijective :
    Function.Bijective (leftMultiplication
      (phaseVector ![1, 0, 0, 0] ![1, 0, 0, 0])) := by
  rw [phaseVector_left_bijective_iff]
  norm_num

/-- Negative norm is also invertible; no positive-definiteness is used. -/
theorem negative_norm_operator_bijective :
    Function.Bijective (rightMultiplication
      (phaseVector ![0, 1, 0, 0] ![0, 1, 0, 0])) := by
  rw [phaseVector_right_bijective_iff]
  norm_num

theorem nonzero_null_phase :
    phaseVector ![1, 1, 0, 0] ![2, 2, 0, 0] ≠ 0 := by
  intro h
  have h₀ := congrArg (fun Z => coordinateEquiv Z 0) h
  rw [phaseVector_coordinates, map_zero] at h₀
  norm_num [InfoGeometry.Lie.SplitOctonionCircularWittForm.positiveCircularEmbedding,
    InfoGeometry.Lie.SplitOctonionCircularWittForm.negativeCircularEmbedding] at h₀

theorem nonzero_null_phase_matrix_singular :
    (leftCoordinateOperatorMatrix
      (phaseVector ![1, 1, 0, 0] ![2, 2, 0, 0])).det = 0 := by
  rw [phaseVector_leftMatrix_singular_iff]
  norm_num

theorem zero_phase_matrix_singular :
    (rightCoordinateOperatorMatrix (phaseVector 0 0)).det = 0 := by
  rw [phaseVector_rightMatrix_singular_iff]
  norm_num

/-- The regular operators used above belong to a noncommutative algebra:
the pole and a nonzero root give different composition orders. -/
theorem regular_operators_do_not_commute :
    leftMultiplication uPlus * leftMultiplication (rootPlus 0) ≠
      leftMultiplication (rootPlus 0) * leftMultiplication uPlus := by
  intro h
  have h₁ := congrArg
    (fun T : Module.End ℝ
      InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn => T 1) h
  change uPlus * (rootPlus 0 * 1) = rootPlus 0 * (uPlus * 1) at h₁
  rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_one,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_one,
    uPlus_mul_rootPlus, rootPlus_mul_uPlus] at h₁
  have hroot : rootPlus 0 ≠ 0 := by
    rw [← circularPeirceBasis_one]
    exact circularPeirceBasis_ne_zero 1
  exact hroot h₁

/-- A nonzero translation cocycle with identity linear part. -/
def translationDatum : Datum (G := Multiplicative ℝ) (M := ℝ) where
  dualAction _ := AddMonoidHom.id ℝ
  dualAction_one := rfl
  dualAction_mul _ _ := rfl
  theta := Multiplicative.toAdd
  theta_one := rfl
  theta_mul _ _ := rfl

theorem translation_cocycle_nonzero :
    translationDatum.theta (Multiplicative.ofAdd (2 : ℝ)) ≠ 0 := by
  norm_num [translationDatum]

/-- This witnesses that mathlib resolves the specialized native groupoid. -/
@[instance_reducible]
def translationGroupoid : Groupoid (AffineActionGroupoid translationDatum) :=
  inferInstance

theorem translation_arrow_exists :
    Nonempty (affineActionObject translationDatum (3 : ℝ) ⟶
      affineActionObject translationDatum (5 : ℝ)) := by
  rw [affineActionGroupoid_nonempty_hom_iff]
  refine ⟨Multiplicative.ofAdd (2 : ℝ), ?_⟩
  norm_num [affineAction, translationDatum]

/-- Inverses are actual native categorical inverses, with typed endpoints. -/
theorem translation_arrow_inverse
    (f : affineActionObject translationDatum (3 : ℝ) ⟶
      affineActionObject translationDatum (5 : ℝ)) :
    f ≫ Groupoid.inv f = 𝟙 (affineActionObject translationDatum (3 : ℝ)) :=
  Groupoid.comp_inv f

end InfoGeometry.Canonical.ZornSouriauIntakeChecks
