/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PositiveCoarseGraining
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Native Gaussian Markov kernels with matrix precision

An arbitrary rectangular real matrix gives the mean map between the native
Euclidean spaces. Mathlib's `multivariateGaussian` supplies a probability
measure for every mean and matrix parameter, and its proved joint
measurability supplies an actual Markov kernel.

The definition is total. The interpretation of `R` as a precision matrix,
and the covariance identification with `R⁻¹`, are asserted under `R.PosDef`.
The bare probability construction makes no covariance claim for an arbitrary
matrix parameter. No density formula or density normalization is re-proved.

The public state spaces and matrix operators are real. Complex-valued
characteristic functions are the native measure-identification interface.
The final covariance theorem connects the existing positive Schur precision
to this measure-valued construction; the KL theorem is native data processing.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.MatrixGaussianKernel

open Matrix MeasureTheory ProbabilityTheory WithLp

variable {n m : Type*} [Fintype n] [Fintype m]

/-- The rectangular matrix action on the existing real Euclidean carriers. -/
def linearMean (Q : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    EuclideanSpace ℝ m :=
  toLp 2 (Q *ᵥ ofLp x)

/-- The same rectangular action as a native continuous linear map. -/
def linearMeanCLM (Q : Matrix m n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m := by
  classical
  exact (Matrix.toEuclideanLin Q).toContinuousLinearMap

@[simp]
theorem linearMeanCLM_apply (Q : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    linearMeanCLM Q x = linearMean Q x := rfl

omit [Fintype m] in
@[simp]
theorem linearMean_apply (Q : Matrix m n ℝ) (x : EuclideanSpace ℝ n) (i : m) :
    linearMean Q x i = (Q *ᵥ ofLp x) i := rfl

@[fun_prop]
theorem continuous_linearMean (Q : Matrix m n ℝ) : Continuous (linearMean Q) :=
  (linearMeanCLM Q).continuous

@[fun_prop]
theorem measurable_linearMean (Q : Matrix m n ℝ) : Measurable (linearMean Q) :=
  (continuous_linearMean Q).measurable

omit [Fintype m] in
@[simp]
theorem linearMean_zero (Q : Matrix m n ℝ) : linearMean Q 0 = 0 := by
  simp [linearMean]

omit [Fintype m] in
@[simp]
theorem linearMean_zero_matrix (x : EuclideanSpace ℝ n) :
    linearMean (0 : Matrix m n ℝ) x = 0 := by
  simp [linearMean]

@[simp]
theorem linearMean_one [DecidableEq n] (x : EuclideanSpace ℝ n) :
    linearMean (1 : Matrix n n ℝ) x = x := by
  simp [linearMean]

/-- Rectangular mean maps compose in the order of matrix multiplication. -/
theorem linearMean_comp {l : Type*}
    (Q₁ : Matrix m n ℝ) (Q₂ : Matrix l m ℝ) (x : EuclideanSpace ℝ n) :
    linearMean Q₂ (linearMean Q₁ x) = linearMean (Q₂ * Q₁) x := by
  simp only [linearMean, WithLp.ofLp_toLp, Matrix.mulVec_mulVec]

/-- The real transpose is the adjoint of the rectangular mean map. -/
theorem inner_linearMean (Q : Matrix m n ℝ)
    (t : EuclideanSpace ℝ m) (x : EuclideanSpace ℝ n) :
    inner ℝ t (linearMean Q x) = inner ℝ (linearMean Qᵀ t) x := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, linearMean, star_trivial]
  rw [Matrix.dotProduct_transpose_mulVec]
  exact dotProduct_comm _ _

/-- Pulling a quadratic covariance form back by the transpose gives `Q S Qᵀ`.
No symmetry or positivity assumption is needed for this algebraic identity. -/
theorem linearMean_transpose_quadratic (Q : Matrix m n ℝ) (S : Matrix n n ℝ)
    (t : EuclideanSpace ℝ m) :
    (linearMean Qᵀ t) ⬝ᵥ S *ᵥ (linearMean Qᵀ t) =
      t ⬝ᵥ (Q * S * Qᵀ) *ᵥ t := by
  change (Qᵀ *ᵥ ofLp t) ⬝ᵥ S *ᵥ (Qᵀ *ᵥ ofLp t) =
    ofLp t ⬝ᵥ (Q * S * Qᵀ) *ᵥ ofLp t
  rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  simp only [Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec]

variable [DecidableEq m]

/-- Gaussian channel with rectangular mean and an inverse precision parameter.
For positive definite `R`, its pointwise covariance is exactly `R⁻¹`. -/
def gaussianKernel (Q : Matrix m n ℝ) (R : Matrix m m ℝ) :
    Kernel (EuclideanSpace ℝ n) (EuclideanSpace ℝ m) where
  toFun x := multivariateGaussian (linearMean Q x) R⁻¹
  measurable' := measurable_multivariateGaussian.comp
    ((measurable_linearMean Q).prodMk measurable_const)

@[simp]
theorem gaussianKernel_apply (Q : Matrix m n ℝ) (R : Matrix m m ℝ)
    (x : EuclideanSpace ℝ n) :
    gaussianKernel Q R x = multivariateGaussian (linearMean Q x) R⁻¹ := rfl

instance gaussianKernel_isGaussian (Q : Matrix m n ℝ) (R : Matrix m m ℝ)
    (x : EuclideanSpace ℝ n) : IsGaussian (gaussianKernel Q R x) := by
  change IsGaussian (multivariateGaussian (linearMean Q x) R⁻¹)
  infer_instance

instance gaussianKernel_isMarkovKernel (Q : Matrix m n ℝ) (R : Matrix m m ℝ) :
    IsMarkovKernel (gaussianKernel Q R) where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure (multivariateGaussian (linearMean Q x) R⁻¹)
    infer_instance

/-- The actual Bochner mean of the pointwise channel law is `Q x`. -/
@[simp]
theorem integral_id_gaussianKernel (Q : Matrix m n ℝ) (R : Matrix m m ℝ)
    (x : EuclideanSpace ℝ n) :
    ∫ y, y ∂gaussianKernel Q R x = linearMean Q x :=
  integral_id_multivariateGaussian

/-- Positive definite precision identifies the actual covariance bilinear form. -/
theorem covarianceBilin_gaussianKernel (Q : Matrix m n ℝ) (R : Matrix m m ℝ)
    (hR : R.PosDef) (x : EuclideanSpace ℝ n) (u v : EuclideanSpace ℝ m) :
    covarianceBilin (gaussianKernel Q R x) u v = u ⬝ᵥ R⁻¹ *ᵥ v :=
  covarianceBilin_multivariateGaussian hR.inv.posSemidef u v

/-- Coordinate covariances are the entries of the inverse precision. -/
theorem covariance_eval_gaussianKernel (Q : Matrix m n ℝ) (R : Matrix m m ℝ)
    (hR : R.PosDef) (x : EuclideanSpace ℝ n) (i j : m) :
    covariance (fun y : EuclideanSpace ℝ m => y i) (fun y => y j)
      (gaussianKernel Q R x) = R⁻¹ i j :=
  covariance_eval_multivariateGaussian hR.inv.posSemidef i j

/-- Native characteristic function for positive definite matrix precision. -/
theorem charFun_gaussianKernel (Q : Matrix m n ℝ) (R : Matrix m m ℝ)
    (hR : R.PosDef) (x : EuclideanSpace ℝ n) (t : EuclideanSpace ℝ m) :
    charFun (gaussianKernel Q R x) t =
      Complex.exp ((inner ℝ t (linearMean Q x) : ℂ) * Complex.I -
        (t ⬝ᵥ R⁻¹ *ᵥ t : ℝ) / 2) :=
  charFun_multivariateGaussian hR.inv.posSemidef t

/-- A zero observation matrix gives a constant centered Gaussian channel. -/
theorem gaussianKernel_zero_matrix (R : Matrix m m ℝ) :
    gaussianKernel (0 : Matrix m n ℝ) R =
      Kernel.const (EuclideanSpace ℝ n)
        (multivariateGaussian (0 : EuclideanSpace ℝ m) R⁻¹) := by
  apply Kernel.ext
  intro x
  simp only [gaussianKernel_apply, linearMean_zero_matrix, Kernel.const_apply]

/-- Unit precision and zero mean recover the native standard Gaussian. -/
theorem gaussianKernel_zero_one :
    gaussianKernel (0 : Matrix m n ℝ) (1 : Matrix m m ℝ) =
      Kernel.const (EuclideanSpace ℝ n) (stdGaussian (EuclideanSpace ℝ m)) := by
  rw [gaussianKernel_zero_matrix]
  simp only [inv_one, multivariateGaussian_zero_one]

/-- Reading an existing positive Schur precision through the actual channel
covariance gives the already-proved coarse covariance formula. -/
theorem covarianceBilin_gaussianKernel_coarsePrecision [DecidableEq n]
    (Q : Matrix m n ℝ) (A : Matrix n n ℝ) (R : Matrix m m ℝ)
    (hA : A.PosDef) (hR : R.PosDef) (x : EuclideanSpace ℝ n)
    (u v : EuclideanSpace ℝ m) :
    covarianceBilin
        (gaussianKernel Q (PositiveCoarseGraining.coarsePrecision A R Q) x) u v =
      u ⬝ᵥ PositiveCoarseGraining.coarseCovariance A R Q *ᵥ v := by
  simpa only [PositiveCoarseGraining.coarsePrecision_inv Q hA hR,
    PositiveCoarseGraining.coarseCovariance] using
    covarianceBilin_gaussianKernel Q (PositiveCoarseGraining.coarsePrecision A R Q)
      (PositiveCoarseGraining.coarsePrecision_posDef Q hA hR) x u v

/-- Applying the Gaussian channel cannot increase native KL divergence. -/
theorem klDiv_gaussianKernel_le (Q : Matrix m n ℝ) (R : Matrix m m ℝ)
    (μ ν : Measure (EuclideanSpace ℝ n)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    InformationTheory.klDiv (gaussianKernel Q R ∘ₘ μ) (gaussianKernel Q R ∘ₘ ν) ≤
      InformationTheory.klDiv μ ν :=
  InformationTheory.klDiv_comp_right_le μ ν (gaussianKernel Q R)

end InfoGeometry.OperatorAlgebra.MatrixGaussianKernel
