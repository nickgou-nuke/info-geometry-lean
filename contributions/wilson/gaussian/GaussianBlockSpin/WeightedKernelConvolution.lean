/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
import GaussianBlockSpin.WeightedKernel

/-!
# Composition of matrix-weighted Gaussian kernels

Two applications of the native block determinant formula prove the exact
normalization identity. Together with matrix-weighted Gaussian elimination,
this gives normalized convolution for arbitrary rectangular observation maps
and positive-definite, potentially noncommuting noise precisions.
-/

noncomputable section

namespace GaussianBlockSpin.WeightedCoarseGraining

open Matrix MeasureTheory Real
open scoped RealInnerProductSpace

variable {n m : Type*} [Fintype n] [Fintype m]
variable [DecidableEq n] [DecidableEq m]

/-- The determinants of the fine precision and its Schur complement multiply
to the determinants of the original two precision matrices. -/
theorem det_finePrecision_mul_coarsePrecision
    {A : Matrix n n ℝ} {R : Matrix m m ℝ}
    (Q : Matrix m n ℝ) (hA : A.PosDef) (hR : R.PosDef) :
    (finePrecision A R Q).det * (coarsePrecision A R Q).det = R.det * A.det := by
  let : Invertible R := hR.isUnit.invertible
  let : Invertible (finePrecision A R Q) := (finePrecision_posDef Q hA hR).isUnit.invertible
  have hcancel : (Qᴴ * R) * ⅟R * (R * Q) = Qᴴ * R * Q := by
    rw [Matrix.mul_assoc Qᴴ R (⅟R), mul_invOf_self, Matrix.mul_one]
    exact (Matrix.mul_assoc Qᴴ R Q).symm
  have hschur : R - (R * Q) * ⅟(finePrecision A R Q) * (Qᴴ * R) =
      coarsePrecision A R Q := by
    simp only [coarsePrecision, Matrix.invOf_eq_nonsing_inv, Matrix.mul_assoc]
  have hschurFirst : finePrecision A R Q - (Qᴴ * R) * ⅟R * (R * Q) = A := by
    rw [hcancel]
    exact add_sub_cancel_right A (Qᴴ * R * Q)
  have hfirst := Matrix.det_fromBlocks₁₁ R (R * Q) (Qᴴ * R) (finePrecision A R Q)
  rw [hschurFirst] at hfirst
  have hsecond := Matrix.det_fromBlocks₂₂ R (R * Q) (Qᴴ * R) (finePrecision A R Q)
  rw [hschur] at hsecond
  exact hsecond.symm.trans hfirst

/-- Gaussian normalization constants combine into the Schur-complement density. -/
theorem weightedKernelNormalizer_elimination
    {A : Matrix n n ℝ} {R : Matrix m m ℝ}
    (Q : Matrix m n ℝ) (hA : A.PosDef) (hR : R.PosDef) :
    weightedKernelNormalizer A *
        (weightedKernelNormalizer R *
          ((2 * π) ^ ((Fintype.card n : ℝ) / 2) /
            Real.sqrt (finePrecision A R Q).det)) =
      weightedKernelNormalizer (coarsePrecision A R Q) := by
  have hH := finePrecision_posDef Q hA hR
  have hroot : Real.sqrt (finePrecision A R Q).det *
        Real.sqrt (coarsePrecision A R Q).det =
      Real.sqrt R.det * Real.sqrt A.det := by
    rw [← Real.sqrt_mul hH.det_pos.le, ← Real.sqrt_mul hR.det_pos.le,
      det_finePrecision_mul_coarsePrecision Q hA hR]
  have hπn : (2 * π) ^ ((Fintype.card n : ℝ) / 2) ≠ 0 := by positivity
  have hπm : (2 * π) ^ ((Fintype.card m : ℝ) / 2) ≠ 0 := by positivity
  have hH0 : Real.sqrt (finePrecision A R Q).det ≠ 0 :=
    (Real.sqrt_pos.mpr hH.det_pos).ne'
  unfold weightedKernelNormalizer
  field_simp
  nlinarith [hroot]

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- Normalized two-kernel convolution with general matrix noise precision.
The effective covariance is `R₂⁻¹ + Q₂ * R₁⁻¹ * Q₂ᴴ` by
`coarsePrecision_inv`; neither observation map has a rank restriction. -/
theorem integral_weightedBlockKernel_mul_weightedBlockKernel
    {R₁ : Matrix m m ℝ} {R₂ : Matrix l l ℝ}
    (Q₁ : Matrix m n ℝ) (Q₂ : Matrix l m ℝ)
    (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef)
    (ψ : EuclideanSpace ℝ l) (φ : EuclideanSpace ℝ n) :
    ∫ θ : EuclideanSpace ℝ m,
        weightedBlockKernel R₂ hR₂ Q₂ ψ θ * weightedBlockKernel R₁ hR₁ Q₁ θ φ =
      weightedBlockKernel (coarsePrecision R₁ R₂ Q₂)
        (coarsePrecision_posDef Q₂ hR₁ hR₂) (Q₂ * Q₁) ψ φ := by
  let v := Q₁.toEuclideanLin φ
  let u := ψ - Q₂.toEuclideanLin v
  rw [← integral_add_right_eq_self
    (fun θ : EuclideanSpace ℝ m =>
      weightedBlockKernel R₂ hR₂ Q₂ ψ θ * weightedBlockKernel R₁ hR₁ Q₁ θ φ) v]
  have hpoint (θ : EuclideanSpace ℝ m) :
      weightedBlockKernel R₂ hR₂ Q₂ ψ (θ + v) *
          weightedBlockKernel R₁ hR₁ Q₁ (θ + v) φ =
        weightedKernelNormalizer R₁ *
          (weightedBlockKernel R₂ hR₂ Q₂ u θ *
            Real.exp (-(1 / 2) * ⟪θ, R₁.toEuclideanLin θ⟫)) := by
    have hfirst : ψ - Q₂.toEuclideanLin (θ + v) = u - Q₂.toEuclideanLin θ := by
      dsimp only [u]
      rw [map_add]
      abel
    have hsecond : θ + v - Q₁.toEuclideanLin φ = θ := add_sub_cancel_right θ v
    unfold weightedBlockKernel
    rw [hfirst, hsecond]
    ac_rfl
  simp_rw [hpoint]
  rw [integral_const_mul, integral_weightedBlockKernel_mul_gaussian Q₂ hR₁ hR₂ u,
    ← mul_assoc, weightedKernelNormalizer_elimination Q₂ hR₁ hR₂]
  simp only [weightedBlockKernel, u, v, Matrix.toEuclideanLin,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply]

end GaussianBlockSpin.WeightedCoarseGraining
