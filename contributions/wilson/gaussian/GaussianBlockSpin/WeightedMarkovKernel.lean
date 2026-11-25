/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import GaussianBlockSpin.WeightedKernelConvolution
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Native Markov kernels for matrix-weighted Gaussian coarse-graining

The existing density has output before input. The native kernel takes the
fine input and returns the coarse probability measure. Joint measurability,
integrability and normalization are proved, and Tonelli upgrades the existing
real convolution identity to equality of native kernels. KL data processing
then follows directly from Mathlib for arbitrary finite input measures.
-/

noncomputable section

namespace GaussianBlockSpin.WeightedCoarseGraining

open Matrix MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal ProbabilityTheory

variable {n m : Type*} [Fintype n] [Fintype m]
variable [DecidableEq n] [DecidableEq m]

/-- Joint continuity uses the actual real Euclidean density and matrix maps. -/
theorem continuous_weightedBlockKernel {R : Matrix m m ℝ} (hR : R.PosDef)
    (Q : Matrix m n ℝ) :
    Continuous (fun p : EuclideanSpace ℝ n × EuclideanSpace ℝ m =>
      weightedBlockKernel R hR Q p.2 p.1) := by
  have hQ : Continuous Q.toEuclideanLin :=
    Q.toEuclideanLin.continuous_of_finiteDimensional
  have hRm : Continuous R.toEuclideanLin :=
    R.toEuclideanLin.continuous_of_finiteDimensional
  unfold weightedBlockKernel
  fun_prop

/-- The nonnegative density is jointly measurable in native kernel order. -/
theorem measurable_weightedBlockDensity {R : Matrix m m ℝ} (hR : R.PosDef)
    (Q : Matrix m n ℝ) :
    Measurable (Function.uncurry (fun φ : EuclideanSpace ℝ n =>
      fun ψ : EuclideanSpace ℝ m => ENNReal.ofReal (weightedBlockKernel R hR Q ψ φ))) :=
  (continuous_weightedBlockKernel hR Q).measurable.ennreal_ofReal

/-- The already proved nonzero Gaussian integral establishes integrability. -/
theorem integrable_weightedBlockKernel {R : Matrix m m ℝ} (hR : R.PosDef)
    (Q : Matrix m n ℝ) (φ : EuclideanSpace ℝ n) :
    Integrable (fun ψ : EuclideanSpace ℝ m => weightedBlockKernel R hR Q ψ φ) :=
  integrable_of_integral_eq_one (integral_weightedBlockKernel hR Q φ)

/-- Normalization in the nonnegative integral used by native measures. -/
theorem lintegral_weightedBlockDensity {R : Matrix m m ℝ} (hR : R.PosDef)
    (Q : Matrix m n ℝ) (φ : EuclideanSpace ℝ n) :
    ∫⁻ ψ : EuclideanSpace ℝ m, ENNReal.ofReal (weightedBlockKernel R hR Q ψ φ) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_weightedBlockKernel hR Q φ)
    (Filter.Eventually.of_forall (fun ψ => (weightedBlockKernel_pos hR Q ψ φ).le)),
    integral_weightedBlockKernel, ENNReal.ofReal_one]

/-- A genuine native kernel, based on s-finite Euclidean Lebesgue measure. -/
def weightedMarkovKernel (R : Matrix m m ℝ) (hR : R.PosDef) (Q : Matrix m n ℝ) :
    Kernel (EuclideanSpace ℝ n) (EuclideanSpace ℝ m) :=
  (Kernel.const (EuclideanSpace ℝ n) (volume : Measure (EuclideanSpace ℝ m))).withDensity
    (fun φ ψ => ENNReal.ofReal (weightedBlockKernel R hR Q ψ φ))

/-- Measurability selects the intended density branch of `Kernel.withDensity`. -/
theorem weightedMarkovKernel_apply {R : Matrix m m ℝ} (hR : R.PosDef)
    (Q : Matrix m n ℝ) (φ : EuclideanSpace ℝ n) :
    weightedMarkovKernel R hR Q φ =
      volume.withDensity (fun ψ => ENNReal.ofReal (weightedBlockKernel R hR Q ψ φ)) := by
  rw [weightedMarkovKernel, Kernel.withDensity_apply _ (measurable_weightedBlockDensity hR Q),
    Kernel.const_apply]

/-- Native set probabilities are the integrals of the existing density. -/
theorem weightedMarkovKernel_apply_set {R : Matrix m m ℝ} (hR : R.PosDef)
    (Q : Matrix m n ℝ) (φ : EuclideanSpace ℝ n) {s : Set (EuclideanSpace ℝ m)}
    (hs : MeasurableSet s) :
    weightedMarkovKernel R hR Q φ s =
      ∫⁻ ψ in s, ENNReal.ofReal (weightedBlockKernel R hR Q ψ φ) := by
  rw [weightedMarkovKernel_apply, withDensity_apply _ hs]

/-- Each input is sent to a probability measure, with no normalization assumed. -/
instance instIsMarkovKernel_weightedMarkovKernel {R : Matrix m m ℝ} (hR : R.PosDef)
    (Q : Matrix m n ℝ) : IsMarkovKernel (weightedMarkovKernel R hR Q) where
  isProbabilityMeasure φ := by
    constructor
    rw [weightedMarkovKernel_apply_set hR Q φ MeasurableSet.univ, Measure.restrict_univ]
    exact lintegral_weightedBlockDensity hR Q φ

/-- Integration against the kernel reads back the original nonnegative density. -/
theorem lintegral_weightedMarkovKernel {R : Matrix m m ℝ} (hR : R.PosDef)
    (Q : Matrix m n ℝ) (φ : EuclideanSpace ℝ n)
    {g : EuclideanSpace ℝ m → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ψ, g ψ ∂weightedMarkovKernel R hR Q φ =
      ∫⁻ ψ, ENNReal.ofReal (weightedBlockKernel R hR Q ψ φ) * g ψ :=
  Kernel.lintegral_withDensity (Kernel.const _ volume)
    (measurable_weightedBlockDensity hR Q) φ hg

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- The real convolution integrand is integrable, because its proved integral
is the strictly positive effective Gaussian density. -/
theorem integrable_weightedBlockKernel_mul_weightedBlockKernel
    {R₁ : Matrix m m ℝ} {R₂ : Matrix l l ℝ}
    (Q₁ : Matrix m n ℝ) (Q₂ : Matrix l m ℝ)
    (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef)
    (ψ : EuclideanSpace ℝ l) (φ : EuclideanSpace ℝ n) :
    Integrable (fun θ : EuclideanSpace ℝ m =>
      weightedBlockKernel R₂ hR₂ Q₂ ψ θ * weightedBlockKernel R₁ hR₁ Q₁ θ φ) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_weightedBlockKernel_mul_weightedBlockKernel Q₁ Q₂ hR₁ hR₂ ψ φ]
  exact (weightedBlockKernel_pos (coarsePrecision_posDef Q₂ hR₁ hR₂)
    (Q₂ * Q₁) ψ φ).ne'

/-- Nonnegative density convolution retains the exact Schur-complement kernel. -/
theorem lintegral_weightedBlockDensity_mul_weightedBlockDensity
    {R₁ : Matrix m m ℝ} {R₂ : Matrix l l ℝ}
    (Q₁ : Matrix m n ℝ) (Q₂ : Matrix l m ℝ)
    (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef)
    (ψ : EuclideanSpace ℝ l) (φ : EuclideanSpace ℝ n) :
    ∫⁻ θ : EuclideanSpace ℝ m,
        ENNReal.ofReal (weightedBlockKernel R₂ hR₂ Q₂ ψ θ) *
          ENNReal.ofReal (weightedBlockKernel R₁ hR₁ Q₁ θ φ) =
      ENNReal.ofReal (weightedBlockKernel (coarsePrecision R₁ R₂ Q₂)
        (coarsePrecision_posDef Q₂ hR₁ hR₂) (Q₂ * Q₁) ψ φ) := by
  have hnonneg : 0 ≤ᵐ[volume] (fun θ : EuclideanSpace ℝ m =>
      weightedBlockKernel R₂ hR₂ Q₂ ψ θ * weightedBlockKernel R₁ hR₁ Q₁ θ φ) :=
    Filter.Eventually.of_forall (fun θ =>
      mul_nonneg (weightedBlockKernel_pos hR₂ Q₂ ψ θ).le
        (weightedBlockKernel_pos hR₁ Q₁ θ φ).le)
  have h := ofReal_integral_eq_lintegral_ofReal
    (integrable_weightedBlockKernel_mul_weightedBlockKernel Q₁ Q₂ hR₁ hR₂ ψ φ) hnonneg
  rw [integral_weightedBlockKernel_mul_weightedBlockKernel Q₁ Q₂ hR₁ hR₂ ψ φ] at h
  calc
    (∫⁻ θ : EuclideanSpace ℝ m,
        ENNReal.ofReal (weightedBlockKernel R₂ hR₂ Q₂ ψ θ) *
          ENNReal.ofReal (weightedBlockKernel R₁ hR₁ Q₁ θ φ)) =
      ∫⁻ θ : EuclideanSpace ℝ m,
        ENNReal.ofReal (weightedBlockKernel R₂ hR₂ Q₂ ψ θ *
          weightedBlockKernel R₁ hR₁ Q₁ θ φ) := by
      apply lintegral_congr
      intro θ
      exact (ENNReal.ofReal_mul (weightedBlockKernel_pos hR₂ Q₂ ψ θ).le).symm
    _ = _ := h.symm

/-- Native kernel composition agrees with the proved analytic convolution.
The use of Tonelli supplies equality of measures for every input, not only
pointwise equality of an unbundled density formula. -/
theorem weightedMarkovKernel_comp
    {R₁ : Matrix m m ℝ} {R₂ : Matrix l l ℝ}
    (Q₁ : Matrix m n ℝ) (Q₂ : Matrix l m ℝ)
    (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef) :
    weightedMarkovKernel R₂ hR₂ Q₂ ∘ₖ weightedMarkovKernel R₁ hR₁ Q₁ =
      weightedMarkovKernel (coarsePrecision R₁ R₂ Q₂)
        (coarsePrecision_posDef Q₂ hR₁ hR₂) (Q₂ * Q₁) := by
  refine Kernel.ext_fun (fun φ g hg => ?_)
  rw [Kernel.lintegral_comp _ _ _ hg,
    lintegral_weightedMarkovKernel hR₁ Q₁ φ hg.lintegral_kernel,
    lintegral_weightedMarkovKernel (coarsePrecision_posDef Q₂ hR₁ hR₂) (Q₂ * Q₁) φ hg]
  have hm₁ : Measurable (fun θ : EuclideanSpace ℝ m =>
      ENNReal.ofReal (weightedBlockKernel R₁ hR₁ Q₁ θ φ)) :=
    (measurable_weightedBlockDensity hR₁ Q₁).of_uncurry_left
  have hm₂ := measurable_weightedBlockDensity hR₂ Q₂
  calc
    (∫⁻ θ, ENNReal.ofReal (weightedBlockKernel R₁ hR₁ Q₁ θ φ) *
        ∫⁻ ψ, g ψ ∂weightedMarkovKernel R₂ hR₂ Q₂ θ) =
      ∫⁻ θ, ∫⁻ ψ, ENNReal.ofReal (weightedBlockKernel R₁ hR₁ Q₁ θ φ) *
        (ENNReal.ofReal (weightedBlockKernel R₂ hR₂ Q₂ ψ θ) * g ψ) := by
      apply lintegral_congr
      intro θ
      rw [lintegral_weightedMarkovKernel hR₂ Q₂ θ hg]
      exact (lintegral_const_mul _ ((hm₂.of_uncurry_left).mul hg)).symm
    _ = ∫⁻ ψ, ∫⁻ θ, ENNReal.ofReal (weightedBlockKernel R₁ hR₁ Q₁ θ φ) *
        (ENNReal.ofReal (weightedBlockKernel R₂ hR₂ Q₂ ψ θ) * g ψ) :=
      lintegral_lintegral_swap
        (((hm₁.comp measurable_fst).mul (hm₂.mul (hg.comp measurable_snd))).aemeasurable)
    _ = ∫⁻ ψ, ENNReal.ofReal (weightedBlockKernel (coarsePrecision R₁ R₂ Q₂)
        (coarsePrecision_posDef Q₂ hR₁ hR₂) (Q₂ * Q₁) ψ φ) * g ψ := by
      apply lintegral_congr
      intro ψ
      calc
        (∫⁻ θ, ENNReal.ofReal (weightedBlockKernel R₁ hR₁ Q₁ θ φ) *
            (ENNReal.ofReal (weightedBlockKernel R₂ hR₂ Q₂ ψ θ) * g ψ)) =
          ∫⁻ θ, g ψ * (ENNReal.ofReal (weightedBlockKernel R₂ hR₂ Q₂ ψ θ) *
            ENNReal.ofReal (weightedBlockKernel R₁ hR₁ Q₁ θ φ)) := by
          apply lintegral_congr
          intro θ
          ac_rfl
        _ = g ψ * ∫⁻ θ, ENNReal.ofReal (weightedBlockKernel R₂ hR₂ Q₂ ψ θ) *
            ENNReal.ofReal (weightedBlockKernel R₁ hR₁ Q₁ θ φ) :=
          lintegral_const_mul _ ((hm₂.of_uncurry_right).mul hm₁)
        _ = _ := by
          rw [lintegral_weightedBlockDensity_mul_weightedBlockDensity Q₁ Q₂ hR₁ hR₂ ψ φ]
          exact mul_comm _ _

/-- KL data processing for the actual Gaussian kernel and arbitrary finite
input measures. The extended-valued native divergence includes the mass
correction `ν.real Set.univ - μ.real Set.univ`; on probability measures it is
the ordinary KL divergence. -/
theorem klDiv_weightedMarkovKernel_comp_le
    {R : Matrix m m ℝ} (hR : R.PosDef) (Q : Matrix m n ℝ)
    (μ ν : Measure (EuclideanSpace ℝ n)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    InformationTheory.klDiv (weightedMarkovKernel R hR Q ∘ₘ μ)
        (weightedMarkovKernel R hR Q ∘ₘ ν) ≤ InformationTheory.klDiv μ ν :=
  InformationTheory.klDiv_comp_right_le μ ν (weightedMarkovKernel R hR Q)

end GaussianBlockSpin.WeightedCoarseGraining
