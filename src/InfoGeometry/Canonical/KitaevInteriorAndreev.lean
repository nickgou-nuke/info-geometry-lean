/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
import InfoGeometry.Canonical.KitaevInteriorKrein
import InfoGeometry.Physics.GeneralFermionicAndreevCarrier

/-! Algebraic identification with the existing doubled rotation and its quadratic
form. This is a statement about the native real coefficient matrix, not a
scattering or many-body dynamics theorem. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevInteriorAndreev
open Matrix KitaevChainCoefficients KitaevInteriorPairing KitaevInteriorKrein
open InfoGeometry.Physics.MajoranaKreinPfaffianCarrier
open InfoGeometry.Physics.GeneralFermionicAndreevCarrier
variable {N : ℕ}

theorem chain_interior_eq_andreev (t : ℝ) :
    (chainCoefficientMatrix N t).submatrix interiorIndex interiorIndex =
      -(2 * t) • andreevRotation := by
  rw [chain_interior_eq_offDiagonalPairing]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    by_cases h : i = j <;> simp [offDiagonalPairing, andreevRotation, h]

/-- Scalar covariance of the existing doubled quadratic form. -/
theorem vectorNormSq_smul {V : Type*} [Fintype V] [DecidableEq V]
    (a : ℝ) (w : Sum V V → ℝ) :
    vectorNormSq (a • w) = a^2 * vectorNormSq w := by
  simp only [vectorNormSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem chain_interior_normSq (t : ℝ)
    (v : Sum (Fin (N - 1)) (Fin (N - 1)) → ℝ) :
    vectorNormSq (((chainCoefficientMatrix N t).submatrix
      interiorIndex interiorIndex).mulVec v) = (2 * t)^2 * vectorNormSq v := by
  rw [chain_interior_eq_andreev, Matrix.smul_mulVec]
  rw [vectorNormSq_smul, neg_sq, andreevRotation_preserves_norm]

theorem chain_interior_transpose_mul (t : ℝ) :
    ((chainCoefficientMatrix N t).submatrix interiorIndex interiorIndex).transpose *
      (chainCoefficientMatrix N t).submatrix interiorIndex interiorIndex =
      ((2 * t)^2) • 1 := by
  have hsk : ((chainCoefficientMatrix N t).submatrix interiorIndex interiorIndex).transpose =
      -(chainCoefficientMatrix N t).submatrix interiorIndex interiorIndex := by
    rw [chain_interior_eq_offDiagonalPairing]
    exact offDiagonalPairing_skew _
  rw [hsk, neg_mul, chain_interior_sq, neg_smul, neg_neg]

end InfoGeometry.Canonical.KitaevInteriorAndreev
