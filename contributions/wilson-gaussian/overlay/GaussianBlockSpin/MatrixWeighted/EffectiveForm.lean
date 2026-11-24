/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/- The Apache LICENSE for these contributed files is retained as
`LICENSE-InfoGeometry-Apache-2.0` at the package root, together with
`NOTICE-InfoGeometry`; the upstream root CC0 license is separate. -/
import GaussianBlockSpin.MatrixWeighted.Kernel
import GaussianBlockSpin.MatrixWeighted.Coordinates

/-!
# The effective matrix-weighted Gaussian integral

Integrating the fine Gaussian against the normalized observation kernel
produces the ordered Schur-complement quadratic form. The determinant factor
is computed with the same canonical Euclidean volume as the existing Gaussian
integral theorem. The response is the actual matrix harmonic extension.

Both precision matrices are positive definite. The observation matrix may be
rectangular and need not be invertible or satisfy a coisometry condition.
-/

noncomputable section

open MeasureTheory Real Matrix
open scoped RealInnerProductSpace

namespace GaussianBlockSpin.MatrixWeighted

variable {n m : Type*} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]
variable {A : Matrix n n ℝ} {R : Matrix m m ℝ}

/-- Exact integration of the matrix-weighted block kernel against a fine
Gaussian, with its determinant factor and effective quadratic form. -/
theorem integral_weightedBlockKernel_mul_gaussian (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) (y : EuclideanSpace ℝ m) :
    ∫ x : EuclideanSpace ℝ n,
      weightedBlockKernel R.toEuclideanLin
          (toEuclideanLin_isSymmetric hR) (inner_toEuclideanLin_pos hR)
          Q.toEuclideanLin y x *
        Real.exp (-(1 / 2) * ⟪x, A.toEuclideanLin x⟫) =
      gaussianPrefactor R.toEuclideanLin *
        ((2 * π) ^ ((Fintype.card n : ℝ) / 2) /
          Real.sqrt (finePrecision A R Q).det) *
        Real.exp (-(1 / 2) * ⟪y, (coarsePrecision A R Q).toEuclideanLin y⟫) := by
  have hK := finePrecision_posDef Q hA hR
  have hexponent (x : EuclideanSpace ℝ n) :
      -(1 / 2) * ⟪y - Q.toEuclideanLin x,
          R.toEuclideanLin (y - Q.toEuclideanLin x)⟫ +
        -(1 / 2) * ⟪x, A.toEuclideanLin x⟫ =
      -(1 / 2) * ⟪y, (coarsePrecision A R Q).toEuclideanLin y⟫ +
        -(1 / 2) * ⟪x - (harmonicExtension A R Q).toEuclideanLin y,
          (finePrecision A R Q).toEuclideanLin
            (x - (harmonicExtension A R Q).toEuclideanLin y)⟫ := by
    linarith [euclidean_quadratic_completion Q hA hR y x]
  have hshift :
      ∫ x : EuclideanSpace ℝ n,
        Real.exp (-(1 / 2) * ⟪x - (harmonicExtension A R Q).toEuclideanLin y,
          (finePrecision A R Q).toEuclideanLin
            (x - (harmonicExtension A R Q).toEuclideanLin y)⟫) =
      (2 * π) ^ ((Fintype.card n : ℝ) / 2) /
        Real.sqrt (finePrecision A R Q).det := by
    rw [integral_sub_right_eq_self
      (fun x : EuclideanSpace ℝ n =>
        Real.exp (-(1 / 2) * ⟪x, (finePrecision A R Q).toEuclideanLin x⟫))
      ((harmonicExtension A R Q).toEuclideanLin y)]
    simpa only [finrank_euclideanSpace, det_toEuclideanLin] using
      integral_exp_neg_half_inner (toEuclideanLin_isSymmetric hK)
        (inner_toEuclideanLin_pos hK)
  have hint (x : EuclideanSpace ℝ n) :
      weightedBlockKernel R.toEuclideanLin
          (toEuclideanLin_isSymmetric hR) (inner_toEuclideanLin_pos hR)
          Q.toEuclideanLin y x *
        Real.exp (-(1 / 2) * ⟪x, A.toEuclideanLin x⟫) =
      (gaussianPrefactor R.toEuclideanLin *
          Real.exp (-(1 / 2) * ⟪y, (coarsePrecision A R Q).toEuclideanLin y⟫)) *
        Real.exp (-(1 / 2) * ⟪x - (harmonicExtension A R Q).toEuclideanLin y,
          (finePrecision A R Q).toEuclideanLin
            (x - (harmonicExtension A R Q).toEuclideanLin y)⟫) := by
    unfold weightedBlockKernel normalizedGaussian
    rw [mul_assoc, ← Real.exp_add, hexponent x, Real.exp_add, ← mul_assoc]
  calc
    _ = ∫ x : EuclideanSpace ℝ n,
        (gaussianPrefactor R.toEuclideanLin *
            Real.exp (-(1 / 2) * ⟪y, (coarsePrecision A R Q).toEuclideanLin y⟫)) *
          Real.exp (-(1 / 2) * ⟪x - (harmonicExtension A R Q).toEuclideanLin y,
            (finePrecision A R Q).toEuclideanLin
              (x - (harmonicExtension A R Q).toEuclideanLin y)⟫) :=
      integral_congr_ae (Filter.Eventually.of_forall hint)
    _ = (gaussianPrefactor R.toEuclideanLin *
          Real.exp (-(1 / 2) * ⟪y, (coarsePrecision A R Q).toEuclideanLin y⟫)) *
        ((2 * π) ^ ((Fintype.card n : ℝ) / 2) /
          Real.sqrt (finePrecision A R Q).det) := by
      rw [integral_const_mul, hshift]
    _ = _ := by ring

/-- The kernel-weighted fine Gaussian is genuinely integrable: the exact
integral has a strictly positive finite real value. -/
theorem integrable_weightedBlockKernel_mul_gaussian (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) (y : EuclideanSpace ℝ m) :
    Integrable (fun x : EuclideanSpace ℝ n =>
      weightedBlockKernel R.toEuclideanLin
          (toEuclideanLin_isSymmetric hR) (inner_toEuclideanLin_pos hR)
          Q.toEuclideanLin y x *
        Real.exp (-(1 / 2) * ⟪x, A.toEuclideanLin x⟫)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_weightedBlockKernel_mul_gaussian Q hA hR y]
  have hfactor := gaussianPrefactor_pos R.toEuclideanLin
    (toEuclideanLin_isSymmetric hR) (inner_toEuclideanLin_pos hR)
  have hdet : 0 < Real.sqrt (finePrecision A R Q).det :=
    Real.sqrt_pos.mpr (finePrecision_posDef Q hA hR).det_pos
  exact ne_of_gt (mul_pos
    (mul_pos hfactor (div_pos (Real.rpow_pos_of_pos (by positivity) _) hdet))
    (Real.exp_pos _))

end GaussianBlockSpin.MatrixWeighted
