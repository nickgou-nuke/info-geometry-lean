/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
import GaussianBlockSpin.EffectiveForm
import GaussianBlockSpin.WeightedCoarseGraining
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Scalar block-spin specialization of weighted coarse-graining

The matrix-weighted definitions specialize to the existing finite-dimensional
Gaussian block-spin API on real Euclidean spaces. The scalar coarse precision
is `α • 1`; the canonical harmonic extension is the translation `α • w` of
`complete_square_translate`, where `effStiffness α H Q w = Q* ψ`.

The final theorem consumes the existing Gaussian integration theorem, retaining
its determinant normalization while expressing the exponent by the canonical
coarse precision. Complex symmetric holomorphic Gaussian forms are outside this
real-slice adapter.
-/

noncomputable section

namespace GaussianBlockSpin.WeightedCoarseGraining

open Matrix MeasureTheory Real
open scoped RealInnerProductSpace

variable {n m l : Type*}
variable [Fintype n] [Fintype m] [Fintype l]
variable [DecidableEq n] [DecidableEq m] [DecidableEq l]

omit [Fintype l] [DecidableEq l] in
/-- Matrix composition is composition of the corresponding Euclidean maps. -/
private lemma toEuclideanLin_mul (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    (A * B).toEuclideanLin = A.toEuclideanLin ∘ₗ B.toEuclideanLin :=
  Matrix.toLpLin_mul 2 2 2 A B

variable (A : Matrix n n ℝ) (Q : Matrix m n ℝ) (α : ℝ)

/-- The scalar coarse precision gives exactly the existing `effStiffness`. -/
theorem finePrecision_scalar_toEuclideanLin :
    (finePrecision A (α • (1 : Matrix m m ℝ)) Q).toEuclideanLin =
      effStiffness α A.toEuclideanLin Q.toEuclideanLin := by
  simp only [finePrecision, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    map_add, map_smul, effStiffness]
  rw [toEuclideanLin_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

/-- The canonical harmonic extension solves the scalar normal equation in
the coordinates used by the weighted matrix theory. -/
theorem harmonicExtension_scalar_mulVec_eq {α : ℝ} (hA : A.PosDef) (hα : 0 < α)
    (ψ : m → ℝ) (w : n → ℝ)
    (hw : finePrecision A (α • (1 : Matrix m m ℝ)) Q *ᵥ w = Qᴴ *ᵥ ψ) :
    harmonicExtension A (α • (1 : Matrix m m ℝ)) Q *ᵥ ψ = α • w := by
  have hR : (α • (1 : Matrix m m ℝ)).PosDef := Matrix.PosDef.one.smul hα
  apply Matrix.mulVec_injective_of_isUnit (finePrecision_posDef Q hA hR).isUnit
  rw [Matrix.mulVec_mulVec, finePrecision_mul_harmonicExtension Q hA hR]
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mulVec,
    Matrix.mulVec_smul, hw]

/-- On Euclidean spaces, the matrix normal equation has the existing
`effStiffness` and adjoint conventions, including the factor `α`. -/
theorem effStiffness_harmonicExtension {α : ℝ} (hA : A.PosDef) (hα : 0 < α)
    (ψ : EuclideanSpace ℝ m) :
    effStiffness α A.toEuclideanLin Q.toEuclideanLin
        ((harmonicExtension A (α • (1 : Matrix m m ℝ)) Q).toEuclideanLin ψ) =
      α • LinearMap.adjoint Q.toEuclideanLin ψ := by
  have hR : (α • (1 : Matrix m m ℝ)).PosDef := Matrix.PosDef.one.smul hα
  have h := congrArg (fun M : Matrix n m ℝ => M.toEuclideanLin ψ)
    (finePrecision_mul_harmonicExtension Q hA hR)
  simpa only [toEuclideanLin_mul, LinearMap.comp_apply,
    finePrecision_scalar_toEuclideanLin, Matrix.mul_smul, Matrix.mul_one,
    map_smul, LinearMap.smul_apply,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint] using h

/-- The canonical harmonic extension is the translation `α • w`, rather than
the auxiliary normal-equation solution `w` of `EffectiveForm`. -/
theorem harmonicExtension_scalar_eq {α : ℝ} (hA : A.PosDef) (hα : 0 < α)
    (ψ : EuclideanSpace ℝ m) (w : EuclideanSpace ℝ n)
    (hw : effStiffness α A.toEuclideanLin Q.toEuclideanLin w =
      LinearMap.adjoint Q.toEuclideanLin ψ) :
    (harmonicExtension A (α • (1 : Matrix m m ℝ)) Q).toEuclideanLin ψ = α • w := by
  have hw' := hw
  rw [← finePrecision_scalar_toEuclideanLin,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at hw'
  have hcoords : finePrecision A (α • (1 : Matrix m m ℝ)) Q *ᵥ WithLp.ofLp w =
      Qᴴ *ᵥ WithLp.ofLp ψ := congrArg WithLp.ofLp hw'
  have h := harmonicExtension_scalar_mulVec_eq A Q hA hα
    (WithLp.ofLp ψ) (WithLp.ofLp w) hcoords
  exact congrArg (WithLp.toLp 2) h

/-- The coarse quadratic form is precisely the exponent in the existing
scalar block-spin Gaussian integral. -/
theorem coarsePrecision_scalar_inner {α : ℝ} (hA : A.PosDef) (hα : 0 < α)
    (ψ : EuclideanSpace ℝ m) (w : EuclideanSpace ℝ n)
    (hw : effStiffness α A.toEuclideanLin Q.toEuclideanLin w =
      LinearMap.adjoint Q.toEuclideanLin ψ) :
    ⟪ψ, (coarsePrecision A (α • (1 : Matrix m m ℝ)) Q).toEuclideanLin ψ⟫ =
      α * ‖ψ‖ ^ 2 - α ^ 2 * ⟪ψ, Q.toEuclideanLin w⟫ := by
  rw [coarsePrecision_eq_sub_response]
  simp only [Matrix.smul_mul, Matrix.one_mul, map_sub, map_smul,
    Matrix.toEuclideanLin, Matrix.toLpLin_one, Matrix.toLpLin_mul_same,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.comp_apply]
  change ⟪ψ, α • ψ - α • Q.toEuclideanLin
    ((harmonicExtension A (α • (1 : Matrix m m ℝ)) Q).toEuclideanLin ψ)⟫ = _
  rw [harmonicExtension_scalar_eq A Q hA hα ψ w hw]
  simp only [map_smul, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [← mul_assoc, ← sq]

/-- Positive matrix precision supplies the strict positivity hypothesis of
the target Gaussian integral on real Euclidean space. -/
theorem inner_toEuclideanLin_pos (hA : A.PosDef) (x : EuclideanSpace ℝ n)
    (hx : x ≠ 0) : 0 < ⟪x, A.toEuclideanLin x⟫ := by
  have hx' : WithLp.ofLp x ≠ 0 := by
    intro h
    apply hx
    exact congrArg (WithLp.toLp 2) h
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin,
    Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct_comm] using
    hA.dotProduct_mulVec_pos hx'

/-- The scalar block-spin Gaussian integral with canonical weighted precision.
The existing determinant normalization is retained, and no normal-equation
solution is supplied as an extra hypothesis. -/
theorem integral_blockKernel_mul_gaussian_coarsePrecision {α : ℝ}
    (hA : A.PosDef) (hα : 0 < α) (ψ : EuclideanSpace ℝ m) :
    ∫ φ : EuclideanSpace ℝ n,
        blockKernel α hα Q.toEuclideanLin ψ φ *
          Real.exp (-(1 / 2) * ⟪φ, A.toEuclideanLin φ⟫) =
      (α / (2 * π)) ^ ((Module.finrank ℝ (EuclideanSpace ℝ m) : ℝ) / 2) *
        ((2 * π) ^ ((Module.finrank ℝ (EuclideanSpace ℝ n) : ℝ) / 2) /
          Real.sqrt (LinearMap.det
            (effStiffness α A.toEuclideanLin Q.toEuclideanLin))) *
        Real.exp (-(1 / 2) *
          ⟪ψ, (coarsePrecision A (α • (1 : Matrix m m ℝ)) Q).toEuclideanLin ψ⟫) := by
  let w : EuclideanSpace ℝ n := α⁻¹ •
    (harmonicExtension A (α • (1 : Matrix m m ℝ)) Q).toEuclideanLin ψ
  have hw : effStiffness α A.toEuclideanLin Q.toEuclideanLin w =
      LinearMap.adjoint Q.toEuclideanLin ψ := by
    dsimp only [w]
    rw [map_smul, effStiffness_harmonicExtension A Q hA hα,
      smul_smul, inv_mul_cancel₀ hα.ne', one_smul]
  rw [integral_blockKernel_mul_gaussian hα
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian)
    (inner_toEuclideanLin_pos A hA) Q.toEuclideanLin ψ w hw,
    coarsePrecision_scalar_inner A Q hA hα ψ w hw]

end GaussianBlockSpin.WeightedCoarseGraining
