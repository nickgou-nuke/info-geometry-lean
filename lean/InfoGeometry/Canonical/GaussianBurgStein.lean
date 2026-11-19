/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Jordan.BurgStein
import InfoGeometry.Probability.GaussianTraceLogdet

/-!
# Gaussian measure KL, Burg--Stein loss, and covariance scale/shape

This bridge evaluates Mathlib's KL divergence on the actual centered Gaussian
measures with the existing real SPD matrices as covariances. It connects that
value to the existing `Jordan.steinLoss`, including its exact global scale and
determinant-one shape decomposition. No covariance commutativity is required.

The real trace--logdet expression is proved nonnegative independently of the
`ENNReal.ofReal` formula, so its real-valued evaluation has no clipping gap.
The determinant-one relative matrix need not itself be symmetric; its trace
bound follows by scaling the source SPD covariance and applying the full
relative covariance inequality.
-/

noncomputable section

namespace InfoGeometry.Canonical.GaussianBurgStein

open Matrix MeasureTheory ProbabilityTheory InformationTheory
open InfoGeometry.Jordan
open scoped MatrixOrder

variable {n : ℕ}

/-- Existing Stein loss in the determinant-ratio orientation of Gaussian KL. -/
theorem steinLoss_eq_covariance_expression (X Y : SPD n) :
    steinLoss X Y =
      Real.log Y.mat.det - Real.log X.mat.det + (Y.mat⁻¹ * X.mat).trace - n := by
  unfold steinLoss
  rw [normalizedDistortion_det, Real.log_div X.det_ne_zero Y.det_ne_zero]
  unfold normalizedDistortion
  ring

/-- Full-matrix Stein loss is nonnegative for arbitrary real SPD inputs. -/
theorem steinLoss_nonneg (X Y : SPD n) : 0 ≤ steinLoss X Y := by
  rw [steinLoss_eq_covariance_expression]
  exact Probability.relative_covariance_trace_logdet_nonneg X.mat Y.mat X.pos Y.pos

/-- The actual centered Gaussian measure divergence equals half of Stein loss. -/
theorem klDiv_gaussian_eq_half_steinLoss (X Y : SPD n) :
    klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) X.mat)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) Y.mat) =
      ENNReal.ofReal (2⁻¹ * steinLoss X Y) := by
  rw [Probability.klDiv_multivariateGaussian_zero X.mat Y.mat X.pos Y.pos,
    steinLoss_eq_covariance_expression]

/-- Exact real-valued Gaussian KL, using the proved real nonnegativity. -/
theorem toReal_klDiv_gaussian_eq_half_steinLoss (X Y : SPD n) :
    (klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) X.mat)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) Y.mat)).toReal =
      2⁻¹ * steinLoss X Y := by
  rw [klDiv_gaussian_eq_half_steinLoss,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (steinLoss_nonneg X Y))]

/-- The source covariance after removing its scale relative to `Y` remains SPD. -/
def shapeCovariance (X Y : SPD n) : SPD n where
  mat := (relativeScale X Y)⁻¹ • X.mat
  symm := by
    change ((relativeScale X Y)⁻¹ • X.mat)ᵀ = (relativeScale X Y)⁻¹ • X.mat
    rw [Matrix.transpose_smul, X.transpose_eq_self]
  pos := X.pos.smul (inv_pos.mpr (relativeScale_pos X Y))

/-- The normalized covariance realizes the previously constructed relative shape. -/
theorem normalizedDistortion_shapeCovariance (X Y : SPD n) :
    normalizedDistortion (shapeCovariance X Y) Y = relativeShape X Y := by
  simp only [normalizedDistortion, shapeCovariance, relativeShape, Matrix.mul_smul]

/-- The shape cost is itself a full-matrix Stein loss. -/
theorem steinLoss_shapeCovariance (X Y : SPD n) (hn : n ≠ 0) :
    steinLoss (shapeCovariance X Y) Y = Matrix.trace (relativeShape X Y) - n := by
  unfold steinLoss
  rw [normalizedDistortion_shapeCovariance, det_relativeShape X Y hn,
    Real.log_one, sub_zero]

/-- The determinant-one relative shape has trace at least the dimension. -/
theorem relativeShape_trace_ge_dim (X Y : SPD n) (hn : n ≠ 0) :
    (n : ℝ) ≤ Matrix.trace (relativeShape X Y) := by
  have h := steinLoss_nonneg (shapeCovariance X Y) Y
  rw [steinLoss_shapeCovariance X Y hn] at h
  exact sub_nonneg.mp h

/-- The shape contribution retains its positive relative-scale weight. -/
theorem steinLoss_shape_term_nonneg (X Y : SPD n) (hn : n ≠ 0) :
    0 ≤ relativeScale X Y * (Matrix.trace (relativeShape X Y) - n) :=
  mul_nonneg (relativeScale_pos X Y).le
    (sub_nonneg.mpr (relativeShape_trace_ge_dim X Y hn))

/-- Actual Gaussian KL separates into radial and determinant-one shape costs. -/
theorem toReal_klDiv_gaussian_scale_shape (X Y : SPD n) (hn : n ≠ 0) :
    (klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) X.mat)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) Y.mat)).toReal =
      2⁻¹ * ((n : ℝ) * burgKernel (relativeScale X Y) +
        relativeScale X Y * (Matrix.trace (relativeShape X Y) - n)) := by
  rw [toReal_klDiv_gaussian_eq_half_steinLoss, steinLoss_scale_shape_split X Y hn]

end InfoGeometry.Canonical.GaussianBurgStein
