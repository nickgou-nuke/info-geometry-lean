/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.MatrixGaussianKernel
import InfoGeometry.OperatorAlgebra.GaussianNoiseComposition
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic.Ring

/-!
# Composition of matrix Gaussian Markov kernels

For real rectangular matrices, composing the channels
`x ↦ multivariateGaussian (Q₁ x) R₁⁻¹` and
`y ↦ multivariateGaussian (Q₂ y) R₂⁻¹` gives a Gaussian channel with
mean map `Q₂ * Q₁` and covariance `R₂⁻¹ + Q₂ * R₁⁻¹ * Q₂ᵀ`.

The conclusion is equality of native Markov kernels. The proof integrates the
second channel's characteristic function against the first channel, then uses
uniqueness of characteristic functions. Complex scalars occur only in that
proof infrastructure; all channel spaces, mean maps, and precision matrices
are real. Positive definiteness supplies the covariance semantics and all
inverse identities. No commutation or coisometry assumption is used.

The final corollary applies the channel to an actual Gaussian measure. It is
obtained by evaluating the kernel composition law with an identity first mean
map, rather than introducing another integration argument.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.MatrixGaussianKernel

open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix ProbabilityTheory RealInnerProductSpace

variable {n m l : Type*}
variable [Fintype n] [Fintype m] [Fintype l]
variable [DecidableEq m] [DecidableEq l]

/-- The second channel transports the test vector by its transpose and
contributes its independent centered Gaussian factor. -/
private theorem charFun_gaussianKernel_comp
    (Q₁ : Matrix m n ℝ) (Q₂ : Matrix l m ℝ)
    {R₁ : Matrix m m ℝ} {R₂ : Matrix l l ℝ} (hR₂ : R₂.PosDef)
    (x : EuclideanSpace ℝ n) (t : EuclideanSpace ℝ l) :
    charFun ((gaussianKernel Q₂ R₂ ∘ₖ gaussianKernel Q₁ R₁) x) t =
      charFun (gaussianKernel Q₁ R₁ x) (linearMean Q₂ᵀ t) *
        Complex.exp (-(((t ⬝ᵥ R₂⁻¹ *ᵥ t : ℝ) : ℂ) / 2)) := by
  calc
    charFun ((gaussianKernel Q₂ R₂ ∘ₖ gaussianKernel Q₁ R₁) x) t =
        ∫ y, charFun (gaussianKernel Q₂ R₂ y) t ∂gaussianKernel Q₁ R₁ x := by
      apply Kernel.integral_comp
      exact (integrable_const (1 : ℝ)).mono (by fun_prop) (by simp)
    _ = ∫ y, Complex.exp ((⟪y, linearMean Q₂ᵀ t⟫ : ℂ) * Complex.I) *
          Complex.exp (-(((t ⬝ᵥ R₂⁻¹ *ᵥ t : ℝ) : ℂ) / 2))
          ∂gaussianKernel Q₁ R₁ x := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [gaussianKernel_apply,
        charFun_multivariateGaussian hR₂.inv.posSemidef,
        inner_linearMean, real_inner_comm (linearMean Q₂ᵀ t),
        sub_eq_add_neg, Complex.exp_add]
    _ = _ := integral_mul_const _ _

/-- Exact composition law, first expressed using the transported covariance. -/
theorem gaussianKernel_comp_apply
    (Q₁ : Matrix m n ℝ) (Q₂ : Matrix l m ℝ)
    {R₁ : Matrix m m ℝ} {R₂ : Matrix l l ℝ}
    (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef) (x : EuclideanSpace ℝ n) :
    (gaussianKernel Q₂ R₂ ∘ₖ gaussianKernel Q₁ R₁) x =
      multivariateGaussian (linearMean (Q₂ * Q₁) x)
        (R₂⁻¹ + Q₂ * R₁⁻¹ * Q₂ᵀ) := by
  have hC : (R₂⁻¹ + Q₂ * R₁⁻¹ * Q₂ᵀ).PosSemidef := by
    simpa only [PositiveCoarseGraining.coarseCovariance,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (PositiveCoarseGraining.coarseCovariance_posDef Q₂ hR₁ hR₂).posSemidef
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_gaussianKernel_comp Q₁ Q₂ hR₂ x t,
    gaussianKernel_apply, charFun_multivariateGaussian hR₁.inv.posSemidef,
    charFun_multivariateGaussian hC, ← Complex.exp_add,
    linearMean_transpose_quadratic Q₂ R₁⁻¹ t,
    ← inner_linearMean Q₂ t (linearMean Q₁ x), linearMean_comp]
  congr 1
  simp only [Matrix.add_mulVec, dotProduct_add, Complex.ofReal_add]
  ring

/-- Two matrix Gaussian channels compose to the channel with the multiplied
mean map and the exact Woodbury precision. -/
theorem gaussianKernel_comp
    (Q₁ : Matrix m n ℝ) (Q₂ : Matrix l m ℝ)
    {R₁ : Matrix m m ℝ} {R₂ : Matrix l l ℝ}
    (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef) :
    gaussianKernel Q₂ R₂ ∘ₖ gaussianKernel Q₁ R₁ =
      gaussianKernel (Q₂ * Q₁) (PositiveCoarseGraining.coarsePrecision R₁ R₂ Q₂) := by
  apply Kernel.ext
  intro x
  rw [gaussianKernel_comp_apply Q₁ Q₂ hR₁ hR₂ x, gaussianKernel_apply,
    PositiveCoarseGraining.coarsePrecision_inv Q₂ hR₁ hR₂,
    Matrix.conjTranspose_eq_transpose_of_trivial]

/-- Scalar noise and a scaled coisometry specialize the exact Markov-kernel
composition law to the coefficient `α * β / (β + s * α)`.
Here `β` is the first channel's precision and `α` is the second channel's
precision. The mean map `Q₁` is arbitrary and rectangular. -/
theorem gaussianKernel_comp_scalar_noise
    (Q₁ : Matrix m n ℝ) (Q₂ : Matrix l m ℝ) {α β s : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hs : 0 ≤ s)
    (hQ₂ : Q₂ * Q₂ᵀ = s • (1 : Matrix l l ℝ)) :
    gaussianKernel Q₂ (α • (1 : Matrix l l ℝ)) ∘ₖ
        gaussianKernel Q₁ (β • (1 : Matrix m m ℝ)) =
      gaussianKernel (Q₂ * Q₁)
        ((α * β / (β + s * α)) • (1 : Matrix l l ℝ)) := by
  have hαI : (α • (1 : Matrix l l ℝ)).PosDef :=
    (Matrix.PosDef.one : (1 : Matrix l l ℝ).PosDef).smul hα
  have hβI : (β • (1 : Matrix m m ℝ)).PosDef :=
    (Matrix.PosDef.one : (1 : Matrix m m ℝ).PosDef).smul hβ
  have hQ₂' : Q₂ * Q₂ᴴ = s • (1 : Matrix l l ℝ) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ₂
  rw [gaussianKernel_comp Q₁ Q₂ hβI hαI,
    PositiveCoarseGraining.coarsePrecision_scalar_noise Q₂ hα hβ hs hQ₂']

/-- Applying the channel to a Gaussian input gives the normalized Gaussian
marginal with the Schur-complement precision. -/
theorem gaussianKernel_comp_multivariateGaussian
    [DecidableEq n] (Q : Matrix m n ℝ) {A : Matrix n n ℝ} {R : Matrix m m ℝ}
    (hA : A.PosDef) (hR : R.PosDef) (μ : EuclideanSpace ℝ n) :
    gaussianKernel Q R ∘ₘ multivariateGaussian μ A⁻¹ =
      multivariateGaussian (linearMean Q μ)
        (PositiveCoarseGraining.coarsePrecision A R Q)⁻¹ := by
  have h := congrArg
    (fun κ : Kernel (EuclideanSpace ℝ n) (EuclideanSpace ℝ m) ↦ κ μ)
    (gaussianKernel_comp (1 : Matrix n n ℝ) Q hA hR)
  simpa only [Kernel.comp_apply, gaussianKernel_apply, linearMean_one, Matrix.mul_one] using h

end InfoGeometry.OperatorAlgebra.MatrixGaussianKernel
