/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
import GaussianBlockSpin.WeightedEffectiveForm
import GaussianBlockSpin.WeightedCoarseGrainingVariational

/-!
# Matrix-weighted real Gaussian block-spin kernels

The general positive-definite Gaussian integral from the upstream library is
combined with the matrix Schur-complement square completion. The normalization
is with respect to ordinary Euclidean Lebesgue measure. No change of lattice
inner product is implicit in this interface.
-/

noncomputable section

namespace GaussianBlockSpin.WeightedCoarseGraining

open Matrix MeasureTheory Real
open scoped RealInnerProductSpace

variable {n m : Type*} [Fintype n] [Fintype m]
variable [DecidableEq n] [DecidableEq m]

/-- The normalization of a positive-definite Gaussian on the coarse space. -/
def weightedKernelNormalizer (R : Matrix m m ℝ) : ℝ :=
  Real.sqrt R.det / (2 * π) ^ ((Fintype.card m : ℝ) / 2)

/-- A normalized Gaussian block density with arbitrary matrix precision.
The positivity argument restricts the interface to genuine Gaussian densities. -/
def weightedBlockKernel (R : Matrix m m ℝ) (_hR : R.PosDef)
    (Q : Matrix m n ℝ) (ψ : EuclideanSpace ℝ m) (φ : EuclideanSpace ℝ n) : ℝ :=
  weightedKernelNormalizer R *
    Real.exp (-(1 / 2) *
      ⟪ψ - Q.toEuclideanLin φ, R.toEuclideanLin (ψ - Q.toEuclideanLin φ)⟫)

theorem weightedKernelNormalizer_pos {R : Matrix m m ℝ} (hR : R.PosDef) :
    0 < weightedKernelNormalizer R := by
  exact div_pos (Real.sqrt_pos.mpr hR.det_pos) (by positivity)

theorem weightedBlockKernel_pos {R : Matrix m m ℝ} (hR : R.PosDef)
    (Q : Matrix m n ℝ) (ψ : EuclideanSpace ℝ m) (φ : EuclideanSpace ℝ n) :
    0 < weightedBlockKernel R hR Q ψ φ :=
  mul_pos (weightedKernelNormalizer_pos hR) (Real.exp_pos _)

/-- The upstream Gaussian integral in native matrix coordinates. -/
theorem integral_exp_neg_half_matrix {A : Matrix n n ℝ} (hA : A.PosDef) :
    ∫ x : EuclideanSpace ℝ n, Real.exp (-(1 / 2) * ⟪x, A.toEuclideanLin x⟫) =
      (2 * π) ^ ((Fintype.card n : ℝ) / 2) / Real.sqrt A.det := by
  simpa only [finrank_euclideanSpace, Matrix.toEuclideanLin,
    LinearMap.det_toLpLin] using
    integral_exp_neg_half_inner
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian)
      (inner_toEuclideanLin_pos A hA)

/-- Normalization is proved for arbitrary positive-definite coarse precision. -/
theorem integral_weightedBlockKernel {R : Matrix m m ℝ} (hR : R.PosDef)
    (Q : Matrix m n ℝ) (φ : EuclideanSpace ℝ n) :
    ∫ ψ : EuclideanSpace ℝ m, weightedBlockKernel R hR Q ψ φ = 1 := by
  unfold weightedBlockKernel
  rw [integral_const_mul,
    ← integral_add_right_eq_self
      (fun ψ : EuclideanSpace ℝ m => Real.exp (-(1 / 2) *
        ⟪ψ - Q.toEuclideanLin φ, R.toEuclideanLin (ψ - Q.toEuclideanLin φ)⟫))
      (Q.toEuclideanLin φ)]
  simp only [add_sub_cancel_right]
  rw [integral_exp_neg_half_matrix hR]
  have hdet : Real.sqrt R.det ≠ 0 := (Real.sqrt_pos.mpr hR.det_pos).ne'
  have hπ : (2 * π) ^ ((Fintype.card m : ℝ) / 2) ≠ 0 := by positivity
  unfold weightedKernelNormalizer
  field_simp

/-- The coefficient of the weighted density specializes to the existing scalar one. -/
theorem weightedKernelNormalizer_scalar {α : ℝ} (hα : 0 < α) :
    weightedKernelNormalizer (α • (1 : Matrix m m ℝ)) =
      (α / (2 * π)) ^ ((Fintype.card m : ℝ) / 2) := by
  unfold weightedKernelNormalizer
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul hα.le,
    Real.div_rpow hα.le (by positivity)]
  congr 2
  rw [mul_one_div]

/-- Matrix precision `α I` recovers the exact upstream density, including normalization. -/
theorem weightedBlockKernel_scalar {α : ℝ} (hα : 0 < α)
    (Q : Matrix m n ℝ) (ψ : EuclideanSpace ℝ m) (φ : EuclideanSpace ℝ n) :
    weightedBlockKernel (α • (1 : Matrix m m ℝ)) (Matrix.PosDef.one.smul hα)
        Q ψ φ = blockKernel α hα Q.toEuclideanLin ψ φ := by
  unfold weightedBlockKernel blockKernel
  rw [weightedKernelNormalizer_scalar hα]
  simp only [map_smul, Matrix.toEuclideanLin, Matrix.toLpLin_one,
    LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_right,
    real_inner_self_eq_norm_sq, finrank_euclideanSpace]
  congr 2
  rw [← mul_assoc, neg_mul (1 / 2 : ℝ) α, mul_comm (1 / 2 : ℝ) α, mul_one_div]

/-- Exact matrix square completion transported to real Euclidean inner products. -/
theorem quadratic_completion_euclidean {A : Matrix n n ℝ} {R : Matrix m m ℝ}
    (Q : Matrix m n ℝ) (hA : A.PosDef) (hR : R.PosDef)
    (ψ : EuclideanSpace ℝ m) (φ : EuclideanSpace ℝ n) :
    ⟪φ, A.toEuclideanLin φ⟫ +
        ⟪ψ - Q.toEuclideanLin φ, R.toEuclideanLin (ψ - Q.toEuclideanLin φ)⟫ =
      ⟪ψ, (coarsePrecision A R Q).toEuclideanLin ψ⟫ +
        ⟪φ - (harmonicExtension A R Q).toEuclideanLin ψ,
          (finePrecision A R Q).toEuclideanLin
            (φ - (harmonicExtension A R Q).toEuclideanLin ψ)⟫ := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin,
    Matrix.ofLp_toLpLin, Matrix.toLin'_apply, WithLp.ofLp_sub, dotProduct_comm] using
    quadratic_completion Q hA hR (WithLp.ofLp ψ) (WithLp.ofLp φ)

/-- Elimination of the fine Gaussian with arbitrary matrix-weighted coarse noise.
The canonical harmonic extension supplies the translation; the determinant factor
is retained explicitly. -/
theorem integral_weightedBlockKernel_mul_gaussian
    {A : Matrix n n ℝ} {R : Matrix m m ℝ}
    (Q : Matrix m n ℝ) (hA : A.PosDef) (hR : R.PosDef)
    (ψ : EuclideanSpace ℝ m) :
    ∫ φ : EuclideanSpace ℝ n, weightedBlockKernel R hR Q ψ φ *
        Real.exp (-(1 / 2) * ⟪φ, A.toEuclideanLin φ⟫) =
      weightedKernelNormalizer R *
        ((2 * π) ^ ((Fintype.card n : ℝ) / 2) /
          Real.sqrt (finePrecision A R Q).det) *
        Real.exp (-(1 / 2) * ⟪ψ, (coarsePrecision A R Q).toEuclideanLin ψ⟫) := by
  let v := (harmonicExtension A R Q).toEuclideanLin ψ
  have hpoint (φ : EuclideanSpace ℝ n) :
      weightedBlockKernel R hR Q ψ φ *
          Real.exp (-(1 / 2) * ⟪φ, A.toEuclideanLin φ⟫) =
        (weightedKernelNormalizer R *
          Real.exp (-(1 / 2) * ⟪ψ, (coarsePrecision A R Q).toEuclideanLin ψ⟫)) *
          Real.exp (-(1 / 2) * ⟪φ - v, (finePrecision A R Q).toEuclideanLin (φ - v)⟫) := by
    unfold weightedBlockKernel
    rw [mul_assoc, ← Real.exp_add]
    have he : -(1 / 2) *
          ⟪ψ - Q.toEuclideanLin φ, R.toEuclideanLin (ψ - Q.toEuclideanLin φ)⟫ +
          -(1 / 2) * ⟪φ, A.toEuclideanLin φ⟫ =
        -(1 / 2) * ⟪ψ, (coarsePrecision A R Q).toEuclideanLin ψ⟫ +
          -(1 / 2) * ⟪φ - v, (finePrecision A R Q).toEuclideanLin (φ - v)⟫ := by
      have h := quadratic_completion_euclidean Q hA hR ψ φ
      dsimp [v]
      linarith
    rw [he, Real.exp_add, ← mul_assoc]
  simp_rw [hpoint]
  rw [integral_const_mul,
    ← integral_add_right_eq_self
      (fun φ : EuclideanSpace ℝ n =>
        Real.exp (-(1 / 2) * ⟪φ - v, (finePrecision A R Q).toEuclideanLin (φ - v)⟫)) v]
  simp only [add_sub_cancel_right]
  rw [integral_exp_neg_half_matrix (finePrecision_posDef Q hA hR)]
  ring

end GaussianBlockSpin.WeightedCoarseGraining
