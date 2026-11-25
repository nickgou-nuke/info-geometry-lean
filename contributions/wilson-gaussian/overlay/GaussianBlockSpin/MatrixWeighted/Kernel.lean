/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/- The Apache LICENSE for these contributed files is retained as
`LICENSE-InfoGeometry-Apache-2.0` at the package root, together with
`NOTICE-InfoGeometry`; the upstream root CC0 license is separate. -/
import GaussianBlockSpin.Kernel

/-!
# Gaussian block kernels with a positive definite precision operator

The precision is a symmetric, strictly positive real linear endomorphism of
the finite-dimensional block-field inner product space. Its density is

`sqrt (det R) / (2π) ^ (dim F / 2) * exp (-(1/2) ⟪x, R x⟫)`.

All integrals use the same canonical volume as `GaussianBlockSpin.Kernel`.
The kernel translates this density by the existing linear averaging map.
For `R = α • id`, `α > 0`, it is exactly the existing `blockKernel`.
-/

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace GaussianBlockSpin.MatrixWeighted

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The normalizing factor for the canonical inner-product-space volume. -/
noncomputable def gaussianPrefactor (R : F →ₗ[ℝ] F) : ℝ :=
  Real.sqrt (LinearMap.det R) / (2 * π) ^ ((Module.finrank ℝ F : ℝ) / 2)

/-- The normalized centered Gaussian with symmetric positive definite precision.
The two proof arguments retain the domain on which this formula is a density. -/
noncomputable def normalizedGaussian (R : F →ₗ[ℝ] F) (_hR : R.IsSymmetric)
    (_hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫) (x : F) : ℝ :=
  gaussianPrefactor R * Real.exp (-(1 / 2) * ⟪x, R x⟫)

/-- The Gaussian block kernel centered at the averaged fine field. -/
noncomputable def weightedBlockKernel (R : F →ₗ[ℝ] F) (hR : R.IsSymmetric)
    (hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫)
    (Q : E →ₗ[ℝ] F) (ψ : F) (φ : E) : ℝ :=
  normalizedGaussian R hR hRpos (ψ - Q φ)

lemma gaussianPrefactor_pos (R : F →ₗ[ℝ] F) (hR : R.IsSymmetric)
    (hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫) :
    0 < gaussianPrefactor R := by
  exact div_pos (Real.sqrt_pos.mpr (det_pos_of_pos hR hRpos))
    (Real.rpow_pos_of_pos (by positivity) _)

lemma normalizedGaussian_pos (R : F →ₗ[ℝ] F) (hR : R.IsSymmetric)
    (hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫) (x : F) :
    0 < normalizedGaussian R hR hRpos x := by
  exact mul_pos (gaussianPrefactor_pos R hR hRpos) (Real.exp_pos _)

lemma weightedBlockKernel_pos (R : F →ₗ[ℝ] F) (hR : R.IsSymmetric)
    (hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫)
    (Q : E →ₗ[ℝ] F) (ψ : F) (φ : E) :
    0 < weightedBlockKernel R hR hRpos Q ψ φ :=
  normalizedGaussian_pos R hR hRpos (ψ - Q φ)

lemma continuous_normalizedGaussian (R : F →ₗ[ℝ] F) (hR : R.IsSymmetric)
    (hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫) :
    Continuous (normalizedGaussian R hR hRpos) := by
  unfold normalizedGaussian
  exact continuous_const.mul (Real.continuous_exp.comp
    (continuous_const.mul (continuous_id.inner R.continuous_of_finiteDimensional)))

/-- Joint continuity in the block and fine fields. -/
lemma continuous_weightedBlockKernel (R : F →ₗ[ℝ] F) (hR : R.IsSymmetric)
    (hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫) (Q : E →ₗ[ℝ] F) :
    Continuous (fun z : F × E => weightedBlockKernel R hR hRpos Q z.1 z.2) := by
  exact (continuous_normalizedGaussian R hR hRpos).comp
    (continuous_fst.sub (Q.continuous_of_finiteDimensional.comp continuous_snd))

lemma continuous_weightedBlockKernel_left (R : F →ₗ[ℝ] F) (hR : R.IsSymmetric)
    (hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫) (Q : E →ₗ[ℝ] F) (φ : E) :
    Continuous (fun ψ : F => weightedBlockKernel R hR hRpos Q ψ φ) := by
  exact (continuous_normalizedGaussian R hR hRpos).comp
    (continuous_id.sub continuous_const)

/-- The matrix normalizer specializes to the existing scalar normalizer. -/
lemma gaussianPrefactor_smul_id {α : ℝ} (hα : 0 < α) :
    gaussianPrefactor (α • LinearMap.id : F →ₗ[ℝ] F) =
      (α / (2 * π)) ^ ((Module.finrank ℝ F : ℝ) / 2) := by
  have hs : Real.sqrt (α ^ Module.finrank ℝ F) =
      α ^ ((Module.finrank ℝ F : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hα.le]
    congr 1
    simp only [div_eq_mul_inv, one_mul]
  unfold gaussianPrefactor
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, hs,
    Real.div_rpow hα.le (by positivity)]

lemma normalizedGaussian_smul_id {α : ℝ} (hα : 0 < α) (x : F) :
    normalizedGaussian (α • LinearMap.id : F →ₗ[ℝ] F)
        (isSymmetric_smul_id α) (inner_smul_id_pos hα) x =
      (α / (2 * π)) ^ ((Module.finrank ℝ F : ℝ) / 2) *
        Real.exp (-(α / 2) * ‖x‖ ^ 2) := by
  unfold normalizedGaussian
  rw [gaussianPrefactor_smul_id hα]
  congr 1
  congr 1
  simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [← mul_assoc, neg_mul (1 / 2 : ℝ) α, mul_comm (1 / 2 : ℝ) α, mul_one_div]

/-- Exact scalar-precision readback, with the original kernel and volume convention. -/
theorem weightedBlockKernel_smul_id {α : ℝ} (hα : 0 < α)
    (Q : E →ₗ[ℝ] F) (ψ : F) (φ : E) :
    weightedBlockKernel (α • LinearMap.id : F →ₗ[ℝ] F)
        (isSymmetric_smul_id α) (inner_smul_id_pos hα) Q ψ φ =
      blockKernel α hα Q ψ φ := by
  simpa only [weightedBlockKernel, blockKernel] using
    normalizedGaussian_smul_id hα (ψ - Q φ)

variable [MeasurableSpace F] [BorelSpace F]

lemma measurable_normalizedGaussian (R : F →ₗ[ℝ] F) (hR : R.IsSymmetric)
    (hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫) :
    Measurable (normalizedGaussian R hR hRpos) :=
  (continuous_normalizedGaussian R hR hRpos).measurable

lemma measurable_weightedBlockKernel_left (R : F →ₗ[ℝ] F) (hR : R.IsSymmetric)
    (hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫) (Q : E →ₗ[ℝ] F) (φ : E) :
    Measurable (fun ψ : F => weightedBlockKernel R hR hRpos Q ψ φ) :=
  (continuous_weightedBlockKernel_left R hR hRpos Q φ).measurable

/-- Normalization with respect to the native canonical volume on `F`. -/
theorem integral_normalizedGaussian (R : F →ₗ[ℝ] F) (hR : R.IsSymmetric)
    (hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫) :
    ∫ x : F, normalizedGaussian R hR hRpos x = 1 := by
  have hdet : 0 < Real.sqrt (LinearMap.det R) :=
    Real.sqrt_pos.mpr (det_pos_of_pos hR hRpos)
  have hvol : 0 < (2 * π) ^ ((Module.finrank ℝ F : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  unfold normalizedGaussian gaussianPrefactor
  rw [integral_const_mul, integral_exp_neg_half_inner hR hRpos,
    div_mul_div_cancel₀ hvol.ne', div_self hdet.ne']

lemma integrable_normalizedGaussian (R : F →ₗ[ℝ] F) (hR : R.IsSymmetric)
    (hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫) :
    Integrable (normalizedGaussian R hR hRpos) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_normalizedGaussian R hR hRpos]
  exact one_ne_zero

/-- Every fine field determines a normalized density in the block field. -/
theorem integral_weightedBlockKernel (R : F →ₗ[ℝ] F) (hR : R.IsSymmetric)
    (hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫) (Q : E →ₗ[ℝ] F) (φ : E) :
    ∫ ψ : F, weightedBlockKernel R hR hRpos Q ψ φ = 1 := by
  unfold weightedBlockKernel
  rw [← integral_add_right_eq_self
    (fun ψ : F => normalizedGaussian R hR hRpos (ψ - Q φ)) (Q φ)]
  simp only [add_sub_cancel_right]
  exact integral_normalizedGaussian R hR hRpos

lemma integrable_weightedBlockKernel (R : F →ₗ[ℝ] F) (hR : R.IsSymmetric)
    (hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫) (Q : E →ₗ[ℝ] F) (φ : E) :
    Integrable (fun ψ : F => weightedBlockKernel R hR hRpos Q ψ φ) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_weightedBlockKernel R hR hRpos Q φ]
  exact one_ne_zero

lemma measurable_weightedBlockKernel [MeasurableSpace E] [BorelSpace E]
    (R : F →ₗ[ℝ] F) (hR : R.IsSymmetric)
    (hRpos : ∀ x : F, x ≠ 0 → 0 < ⟪x, R x⟫) (Q : E →ₗ[ℝ] F) :
    Measurable (fun z : F × E => weightedBlockKernel R hR hRpos Q z.1 z.2) :=
  (continuous_weightedBlockKernel R hR hRpos Q).measurable

end GaussianBlockSpin.MatrixWeighted
