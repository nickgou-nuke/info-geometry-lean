/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Lie.SplitOctonionRegularInvertibility
import InfoGeometry.Lie.CanonicalZornRegularNorm
import InfoGeometry.Lie.SplitOctonionCircularWittForm
import InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Two four-vectors and regular operators in the native Ell-circular basis

The existing positive and negative circular embeddings package two real
four-vectors. The inverse of the actual Ell-circular coordinate equivalence
puts their sum in `CanonicalZorn`. Its determinant is their Minkowski
pairing, and the existing native left/right regular operators are invertible
exactly when that pairing is nonzero.

The matrix statements use `leftCoordinateOperatorMatrix` and
`rightCoordinateOperatorMatrix` from the same Ell-circular basis. They are
full real `8 × 8` matrices. The zero-determinant criterion follows by algebra
equivalences; no associativity of Zorn multiplication is assumed and no
formula for the numerical value of the matrix determinant is claimed.

The pairing equation includes zero representatives. Its interpretation as
projective point/hyperplane incidence requires nonzero representatives.
-/

noncomputable section

namespace InfoGeometry.Lie.ZornChiralCircularFourVectorOperators

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge (realCrossProduct3)
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllCircularOperatorCoordinates
open InfoGeometry.Lie.SplitOctonionEllCircularQuadraticCoordinates
open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Lie.SplitOctonionRegularInvertibility

local notation "Zorn" =>
  InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn
local notation "N" => ZornMatrix.detZ realCrossProduct3

/-- Two four-vectors on the full native alternative carrier, using the
already constructed Ell-circular basis and its two Witt inclusions. -/
def phaseVector (x p : Fin 4 → ℝ) : Zorn :=
  coordinateEquiv.symm (positiveCircularEmbedding x + negativeCircularEmbedding p)

@[simp] theorem phaseVector_coordinates (x p : Fin 4 → ℝ) :
    coordinateEquiv (phaseVector x p) =
      positiveCircularEmbedding x + negativeCircularEmbedding p :=
  coordinateEquiv.apply_symm_apply _

/-- The split composition norm is the mixed Minkowski pairing. -/
theorem phaseVector_det (x p : Fin 4 → ℝ) :
    N (phaseVector x p) =
      x 0 * p 0 - (x 1 * p 1 + x 2 * p 2 + x 3 * p 3) := by
  rw [← circularPeirceQuadratic_apply, phaseVector_coordinates,
    circularPeirceQuadratic_formula]
  simp [positiveCircularEmbedding, negativeCircularEmbedding]

/-- Restricting to the diagonal gives the Lorentz quadratic form. -/
theorem phaseVector_diagonal_det (x : Fin 4 → ℝ) :
    N (phaseVector x x) = x 0 ^ 2 - (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) := by
  simpa only [pow_two] using phaseVector_det x x

theorem phaseVector_left_bijective_iff (x p : Fin 4 → ℝ) :
    Function.Bijective (leftMultiplication (phaseVector x p)) ↔
      x 0 * p 0 - (x 1 * p 1 + x 2 * p 2 + x 3 * p 3) ≠ 0 := by
  have h : IsUnit (leftMultiplication (phaseVector x p)) ↔
      N (phaseVector x p) ≠ 0 :=
    InfoGeometry.Lie.CanonicalZornRegularNorm.isUnit_leftRegular_iff _
  rw [phaseVector_det] at h
  exact (Module.End.isUnit_iff _).symm.trans h

theorem phaseVector_right_bijective_iff (x p : Fin 4 → ℝ) :
    Function.Bijective (rightMultiplication (phaseVector x p)) ↔
      x 0 * p 0 - (x 1 * p 1 + x 2 * p 2 + x 3 * p 3) ≠ 0 := by
  rw [rightMultiplication_bijective_iff, phaseVector_det]

/-- The actual Ell-circular coordinate operator preserves the regular
invertibility criterion because coordinate transport is an algebra equivalence. -/
theorem leftCoordinateOperator_isUnit_iff (X : Zorn) :
    IsUnit (leftCoordinateOperator X) ↔ N X ≠ 0 := by
  have h : leftCoordinateOperator X =
      (coordinateEquiv.conjAlgEquiv ℝ) (leftMultiplication X) := by
    ext y
    rfl
  rw [h, MulEquiv.isUnit_map]
  exact InfoGeometry.Lie.CanonicalZornRegularNorm.isUnit_leftRegular_iff X

theorem rightCoordinateOperator_isUnit_iff (X : Zorn) :
    IsUnit (rightCoordinateOperator X) ↔ N X ≠ 0 := by
  have h : rightCoordinateOperator X =
      (coordinateEquiv.conjAlgEquiv ℝ) (rightMultiplication X) := by
    ext y
    rfl
  rw [h, MulEquiv.isUnit_map, rightMultiplication_isUnit_iff]

theorem leftCoordinateOperatorMatrix_isUnit_iff (X : Zorn) :
    IsUnit (leftCoordinateOperatorMatrix X) ↔ N X ≠ 0 := by
  change IsUnit ((LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8)))
    (leftCoordinateOperator X)) ↔ _
  rw [MulEquiv.isUnit_map, leftCoordinateOperator_isUnit_iff]

theorem rightCoordinateOperatorMatrix_isUnit_iff (X : Zorn) :
    IsUnit (rightCoordinateOperatorMatrix X) ↔ N X ≠ 0 := by
  change IsUnit ((LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8)))
    (rightCoordinateOperator X)) ↔ _
  rw [MulEquiv.isUnit_map, rightCoordinateOperator_isUnit_iff]

theorem leftCoordinateOperatorMatrix_det_ne_zero_iff (X : Zorn) :
    (leftCoordinateOperatorMatrix X).det ≠ 0 ↔ N X ≠ 0 := by
  calc
    (leftCoordinateOperatorMatrix X).det ≠ 0 ↔
        IsUnit (leftCoordinateOperatorMatrix X).det := isUnit_iff_ne_zero.symm
    _ ↔ IsUnit (leftCoordinateOperatorMatrix X) :=
      (Matrix.isUnit_iff_isUnit_det _).symm
    _ ↔ N X ≠ 0 := leftCoordinateOperatorMatrix_isUnit_iff X

theorem rightCoordinateOperatorMatrix_det_ne_zero_iff (X : Zorn) :
    (rightCoordinateOperatorMatrix X).det ≠ 0 ↔ N X ≠ 0 := by
  calc
    (rightCoordinateOperatorMatrix X).det ≠ 0 ↔
        IsUnit (rightCoordinateOperatorMatrix X).det := isUnit_iff_ne_zero.symm
    _ ↔ IsUnit (rightCoordinateOperatorMatrix X) :=
      (Matrix.isUnit_iff_isUnit_det _).symm
    _ ↔ N X ≠ 0 := rightCoordinateOperatorMatrix_isUnit_iff X

/-- Exact point/dual-hyperplane pairing equation read from the full real
left-operator matrix. Projectivization additionally requires nonzero inputs. -/
theorem phaseVector_leftMatrix_singular_iff (x p : Fin 4 → ℝ) :
    (leftCoordinateOperatorMatrix (phaseVector x p)).det = 0 ↔
      x 0 * p 0 = x 1 * p 1 + x 2 * p 2 + x 3 * p 3 := by
  have h := not_congr (leftCoordinateOperatorMatrix_det_ne_zero_iff (phaseVector x p))
  simpa only [not_not, phaseVector_det, sub_eq_zero] using h

theorem phaseVector_rightMatrix_singular_iff (x p : Fin 4 → ℝ) :
    (rightCoordinateOperatorMatrix (phaseVector x p)).det = 0 ↔
      x 0 * p 0 = x 1 * p 1 + x 2 * p 2 + x 3 * p 3 := by
  have h := not_congr (rightCoordinateOperatorMatrix_det_ne_zero_iff (phaseVector x p))
  simpa only [not_not, phaseVector_det, sub_eq_zero] using h

end InfoGeometry.Lie.ZornChiralCircularFourVectorOperators
