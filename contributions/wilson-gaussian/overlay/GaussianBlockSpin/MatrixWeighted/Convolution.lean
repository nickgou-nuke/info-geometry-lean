/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/- The Apache LICENSE for these contributed files is retained as
`LICENSE-InfoGeometry-Apache-2.0` at the package root, together with
`NOTICE-InfoGeometry`; the upstream root CC0 license is separate. -/
import GaussianBlockSpin.MatrixWeighted.EffectiveForm
import GaussianBlockSpin.MatrixWeighted.Composition
import GaussianBlockSpin.Convolution

/-!
# Convolution of matrix-weighted Gaussian block kernels

For arbitrary positive definite precisions `R₁` and `R₂`, integrating the
intermediate Euclidean field composes two normalized block kernels. The new
averaging map is `Q₂ * Q₁`; the new precision is
`coarsePrecision R₁ R₂ Q₂`, whose inverse is
`R₂⁻¹ + Q₂ * R₁⁻¹ * Q₂ᴴ`.

The proof uses the actual volume integral, translation of the intermediate
field, the effective-form integral, and the positive determinant identity.
No commutation or coisometry hypothesis is needed for the matrix theorem.
The final corollary recovers the scalar coefficient under the original
scaled-coisometry hypothesis.
-/

noncomputable section

open MeasureTheory Real Matrix
open scoped RealInnerProductSpace

namespace GaussianBlockSpin.MatrixWeighted

variable {n m l : Type*}
variable [Fintype n] [Fintype m] [Fintype l]
variable [DecidableEq n] [DecidableEq m] [DecidableEq l]
variable {A : Matrix n n ℝ} {R : Matrix m m ℝ}

/-- The fine Gaussian normalization combines with the elimination determinant
to give the normalized coarse Gaussian. -/
lemma gaussianPrefactor_convolution (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) :
    gaussianPrefactor A.toEuclideanLin * gaussianPrefactor R.toEuclideanLin *
        ((2 * π) ^ ((Fintype.card n : ℝ) / 2) /
          Real.sqrt (finePrecision A R Q).det) =
      gaussianPrefactor (coarsePrecision A R Q).toEuclideanLin := by
  have hvol : 0 < (2 * π) ^ ((Fintype.card n : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  simp only [gaussianPrefactor, det_toEuclideanLin, finrank_euclideanSpace]
  rw [sqrt_det_coarsePrecision Q hA hR]
  calc
    _ = (Real.sqrt R.det / (2 * π) ^ ((Fintype.card m : ℝ) / 2)) *
        ((Real.sqrt A.det / (2 * π) ^ ((Fintype.card n : ℝ) / 2)) *
          ((2 * π) ^ ((Fintype.card n : ℝ) / 2) /
            Real.sqrt (finePrecision A R Q).det)) := by ring
    _ = (Real.sqrt R.det / (2 * π) ^ ((Fintype.card m : ℝ) / 2)) *
        (Real.sqrt A.det / Real.sqrt (finePrecision A R Q).det) := by
      rw [div_mul_div_cancel₀ hvol.ne']
    _ = _ := by ring

/-- Pushing a normalized Gaussian through a normalized observation kernel
gives the Gaussian with the Schur-complement precision. -/
theorem integral_weightedBlockKernel_mul_normalizedGaussian (Q : Matrix m n ℝ)
    (hA : A.PosDef) (hR : R.PosDef) (y : EuclideanSpace ℝ m) :
    ∫ x : EuclideanSpace ℝ n,
      weightedBlockKernel R.toEuclideanLin
          (toEuclideanLin_isSymmetric hR) (inner_toEuclideanLin_pos hR)
          Q.toEuclideanLin y x *
        normalizedGaussian A.toEuclideanLin
          (toEuclideanLin_isSymmetric hA) (inner_toEuclideanLin_pos hA) x =
      normalizedGaussian (coarsePrecision A R Q).toEuclideanLin
        (toEuclideanLin_isSymmetric (coarsePrecision_posDef Q hA hR))
        (inner_toEuclideanLin_pos (coarsePrecision_posDef Q hA hR)) y := by
  have hint (x : EuclideanSpace ℝ n) :
      weightedBlockKernel R.toEuclideanLin
          (toEuclideanLin_isSymmetric hR) (inner_toEuclideanLin_pos hR)
          Q.toEuclideanLin y x *
        normalizedGaussian A.toEuclideanLin
          (toEuclideanLin_isSymmetric hA) (inner_toEuclideanLin_pos hA) x =
      gaussianPrefactor A.toEuclideanLin *
        (weightedBlockKernel R.toEuclideanLin
          (toEuclideanLin_isSymmetric hR) (inner_toEuclideanLin_pos hR)
          Q.toEuclideanLin y x * Real.exp (-(1 / 2) * ⟪x, A.toEuclideanLin x⟫)) := by
    unfold normalizedGaussian
    exact mul_left_comm _ _ _
  simp only [hint]
  rw [integral_const_mul, integral_weightedBlockKernel_mul_gaussian Q hA hR y]
  unfold normalizedGaussian
  calc
    _ = (gaussianPrefactor A.toEuclideanLin * gaussianPrefactor R.toEuclideanLin *
          ((2 * π) ^ ((Fintype.card n : ℝ) / 2) /
            Real.sqrt (finePrecision A R Q).det)) *
        Real.exp (-(1 / 2) * ⟪y, (coarsePrecision A R Q).toEuclideanLin y⟫) := by
      simp only [mul_assoc]
    _ = _ := by rw [gaussianPrefactor_convolution Q hA hR]

variable {R₁ : Matrix m m ℝ} {R₂ : Matrix l l ℝ}

/-- Actual kernel convolution on the intermediate Euclidean field.
The positive output precision is the existing ordered Schur complement. -/
theorem integral_weightedBlockKernel_mul_weightedBlockKernel
    (Q₁ : Matrix m n ℝ) (Q₂ : Matrix l m ℝ)
    (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef)
    (ψ : EuclideanSpace ℝ l) (φ : EuclideanSpace ℝ n) :
    ∫ θ : EuclideanSpace ℝ m,
      weightedBlockKernel R₂.toEuclideanLin
          (toEuclideanLin_isSymmetric hR₂) (inner_toEuclideanLin_pos hR₂)
          Q₂.toEuclideanLin ψ θ *
        weightedBlockKernel R₁.toEuclideanLin
          (toEuclideanLin_isSymmetric hR₁) (inner_toEuclideanLin_pos hR₁)
          Q₁.toEuclideanLin θ φ =
      weightedBlockKernel (coarsePrecision R₁ R₂ Q₂).toEuclideanLin
        (toEuclideanLin_isSymmetric (coarsePrecision_posDef Q₂ hR₁ hR₂))
        (inner_toEuclideanLin_pos (coarsePrecision_posDef Q₂ hR₁ hR₂))
        (Q₂ * Q₁).toEuclideanLin ψ φ := by
  have hint (θ : EuclideanSpace ℝ m) :
      weightedBlockKernel R₂.toEuclideanLin
          (toEuclideanLin_isSymmetric hR₂) (inner_toEuclideanLin_pos hR₂)
          Q₂.toEuclideanLin ψ (θ + Q₁.toEuclideanLin φ) *
        weightedBlockKernel R₁.toEuclideanLin
          (toEuclideanLin_isSymmetric hR₁) (inner_toEuclideanLin_pos hR₁)
          Q₁.toEuclideanLin (θ + Q₁.toEuclideanLin φ) φ =
      weightedBlockKernel R₂.toEuclideanLin
          (toEuclideanLin_isSymmetric hR₂) (inner_toEuclideanLin_pos hR₂)
          Q₂.toEuclideanLin (ψ - Q₂.toEuclideanLin (Q₁.toEuclideanLin φ)) θ *
        normalizedGaussian R₁.toEuclideanLin
          (toEuclideanLin_isSymmetric hR₁) (inner_toEuclideanLin_pos hR₁) θ := by
    have hshift : ψ - Q₂.toEuclideanLin (θ + Q₁.toEuclideanLin φ) =
        (ψ - Q₂.toEuclideanLin (Q₁.toEuclideanLin φ)) - Q₂.toEuclideanLin θ := by
      rw [map_add]
      abel
    simp only [weightedBlockKernel, hshift, add_sub_cancel_right]
  rw [← integral_add_right_eq_self
    (fun θ : EuclideanSpace ℝ m =>
      weightedBlockKernel R₂.toEuclideanLin
          (toEuclideanLin_isSymmetric hR₂) (inner_toEuclideanLin_pos hR₂)
          Q₂.toEuclideanLin ψ θ *
        weightedBlockKernel R₁.toEuclideanLin
          (toEuclideanLin_isSymmetric hR₁) (inner_toEuclideanLin_pos hR₁)
          Q₁.toEuclideanLin θ φ) (Q₁.toEuclideanLin φ)]
  simp only [hint]
  rw [integral_weightedBlockKernel_mul_normalizedGaussian Q₂ hR₁ hR₂]
  simp only [weightedBlockKernel, toEuclideanLin_mul, LinearMap.comp_apply]

/-- Scalar matrix precision reads back to the original scalar kernel. -/
lemma weightedBlockKernel_smul_matrix_one {α : ℝ} (hα : 0 < α)
    (Q : Matrix m n ℝ) (ψ : EuclideanSpace ℝ m) (φ : EuclideanSpace ℝ n) :
    weightedBlockKernel (α • (1 : Matrix m m ℝ)).toEuclideanLin
        (toEuclideanLin_isSymmetric (Matrix.PosDef.one.smul hα))
        (inner_toEuclideanLin_pos (Matrix.PosDef.one.smul hα))
        Q.toEuclideanLin ψ φ =
      blockKernel α hα Q.toEuclideanLin ψ φ := by
  simpa only [weightedBlockKernel, normalizedGaussian, toEuclideanLin_smul_one] using
    weightedBlockKernel_smul_id hα Q.toEuclideanLin ψ φ

/-- The general matrix convolution specializes to the original scalar law
when the outer observation is a scaled coisometry. -/
theorem integral_blockKernel_mul_blockKernel_of_matrix
    {α β s : ℝ} (hα : 0 < α) (hβ : 0 < β) (hs : 0 ≤ s)
    (Q₁ : Matrix m n ℝ) (Q₂ : Matrix l m ℝ)
    (hQ : Q₂ * Q₂ᵀ = s • (1 : Matrix l l ℝ))
    (ψ : EuclideanSpace ℝ l) (φ : EuclideanSpace ℝ n) :
    ∫ θ : EuclideanSpace ℝ m,
      blockKernel α hα Q₂.toEuclideanLin ψ θ *
        blockKernel β hβ Q₁.toEuclideanLin θ φ =
      blockKernel (α * β / (β + s * α))
        (GaussianBlockSpin.convCoeff_pos hα hβ hs) (Q₂ * Q₁).toEuclideanLin ψ φ := by
  have hβI : (β • (1 : Matrix m m ℝ)).PosDef := Matrix.PosDef.one.smul hβ
  have hαI : (α • (1 : Matrix l l ℝ)).PosDef := Matrix.PosDef.one.smul hα
  have hγ := GaussianBlockSpin.convCoeff_pos hα hβ hs
  calc
    _ = weightedBlockKernel
        (coarsePrecision (β • (1 : Matrix m m ℝ)) (α • (1 : Matrix l l ℝ)) Q₂).toEuclideanLin
        (toEuclideanLin_isSymmetric (coarsePrecision_posDef Q₂ hβI hαI))
        (inner_toEuclideanLin_pos (coarsePrecision_posDef Q₂ hβI hαI))
        (Q₂ * Q₁).toEuclideanLin ψ φ := by
      simpa only [weightedBlockKernel_smul_matrix_one hα,
        weightedBlockKernel_smul_matrix_one hβ] using
        integral_weightedBlockKernel_mul_weightedBlockKernel Q₁ Q₂ hβI hαI ψ φ
    _ = _ := by
      simpa only [weightedBlockKernel, normalizedGaussian,
        scalar_coarsePrecision hα hβ hs Q₂ hQ] using
        weightedBlockKernel_smul_matrix_one hγ (Q₂ * Q₁) ψ φ

end GaussianBlockSpin.MatrixWeighted
