/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/- The Apache LICENSE for these contributed files is retained as
`LICENSE-InfoGeometry-Apache-2.0` at the package root, together with
`NOTICE-InfoGeometry`; the upstream root CC0 license is separate. -/
import GaussianBlockSpin.MatrixWeighted.Variational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Adapted to real matrices from
`InfoGeometry.OperatorAlgebra.CoarseGrainingComposition` in
`nickgou-nuke/info-geometry-lean`; original Apache 2.0 attribution is retained.
The scalar field in this module is `ℝ`. Native conjugate transpose and real-part
notations reduce to ordinary transpose and the identity, respectively.

# Composition of positive operator eliminations

Two arbitrary rectangular coarse-graining maps transport covariance in order.
The joint quadratic problem has the same unique minimizer as successive
elimination. The result retains both matrix-valued noise weights and every
cross-space coupling; no simultaneous diagonalization is assumed.
-/

noncomputable section

namespace GaussianBlockSpin.MatrixWeighted

open Matrix

variable {n m l : Type*}
variable [Fintype n] [Fintype m] [Fintype l]
variable [DecidableEq n] [DecidableEq m] [DecidableEq l]
variable {A : Matrix n n ℝ} {R₁ : Matrix m m ℝ} {R₂ : Matrix l l ℝ}
variable (Q₁ : Matrix m n ℝ) (Q₂ : Matrix l m ℝ)

/-- The covariance of two successive eliminations, with ordered composite map. -/
theorem twoStage_coarsePrecision_inv (hA : A.PosDef) (hR₁ : R₁.PosDef)
    (hR₂ : R₂.PosDef) :
    (coarsePrecision (coarsePrecision A R₁ Q₁) R₂ Q₂)⁻¹ =
      R₂⁻¹ + Q₂ * R₁⁻¹ * Q₂ᴴ + (Q₂ * Q₁) * A⁻¹ * (Q₂ * Q₁)ᴴ := by
  rw [coarsePrecision_inv Q₂ (coarsePrecision_posDef Q₁ hA hR₁) hR₂,
    coarsePrecision_inv Q₁ hA hR₁]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc, add_assoc]

/-- Joint energy before either of the two fine variables has been eliminated. -/
def twoStageEnergy (A : Matrix n n ℝ) (R₁ : Matrix m m ℝ) (R₂ : Matrix l l ℝ)
    (Q₁ : Matrix m n ℝ) (Q₂ : Matrix l m ℝ)
    (y : l → ℝ) (z : m → ℝ) (x : n → ℝ) : ℝ :=
  quadraticEnergy A R₁ Q₁ z x +
    RCLike.re (star (y - Q₂ *ᵥ z) ⬝ᵥ (R₂ *ᵥ (y - Q₂ *ᵥ z)))

omit [DecidableEq l] in
/-- Two exact square completions retain both positive residual terms. -/
theorem twoStageEnergy_completion (hA : A.PosDef) (hR₁ : R₁.PosDef)
    (hR₂ : R₂.PosDef) (y : l → ℝ) (z : m → ℝ) (x : n → ℝ) :
    let S₁ := coarsePrecision A R₁ Q₁
    let E₁ := harmonicExtension A R₁ Q₁
    let E₂ := harmonicExtension S₁ R₂ Q₂
    twoStageEnergy A R₁ R₂ Q₁ Q₂ y z x =
      RCLike.re (star y ⬝ᵥ (coarsePrecision S₁ R₂ Q₂ *ᵥ y)) +
        RCLike.re (star (z - E₂ *ᵥ y) ⬝ᵥ
          (finePrecision S₁ R₂ Q₂ *ᵥ (z - E₂ *ᵥ y))) +
        RCLike.re (star (x - E₁ *ᵥ z) ⬝ᵥ
          (finePrecision A R₁ Q₁ *ᵥ (x - E₁ *ᵥ z))) := by
  dsimp only
  rw [twoStageEnergy, quadraticEnergy_completion Q₁ hA hR₁]
  have h₂ := quadraticEnergy_completion Q₂ (coarsePrecision_posDef Q₁ hA hR₁) hR₂ y z
  dsimp only [quadraticEnergy] at h₂
  rw [add_right_comm, h₂]

omit [DecidableEq l] in
theorem twoStageEnergy_lower_bound (hA : A.PosDef) (hR₁ : R₁.PosDef)
    (hR₂ : R₂.PosDef) (y : l → ℝ) (z : m → ℝ) (x : n → ℝ) :
    RCLike.re (star y ⬝ᵥ
        (coarsePrecision (coarsePrecision A R₁ Q₁) R₂ Q₂ *ᵥ y)) ≤
      twoStageEnergy A R₁ R₂ Q₁ Q₂ y z x := by
  rw [twoStageEnergy_completion Q₁ Q₂ hA hR₁ hR₂, add_assoc]
  apply le_add_of_nonneg_right
  exact add_nonneg
    ((finePrecision_posDef Q₂ (coarsePrecision_posDef Q₁ hA hR₁)
      hR₂).posSemidef.re_dotProduct_nonneg _)
    ((finePrecision_posDef Q₁ hA hR₁).posSemidef.re_dotProduct_nonneg _)

omit [DecidableEq l] in
/-- Equality identifies the unique joint state, with composed harmonic extension. -/
theorem twoStageEnergy_eq_min_iff (hA : A.PosDef) (hR₁ : R₁.PosDef)
    (hR₂ : R₂.PosDef) (y : l → ℝ) (z : m → ℝ) (x : n → ℝ) :
    let E₁ := harmonicExtension A R₁ Q₁
    let E₂ := harmonicExtension (coarsePrecision A R₁ Q₁) R₂ Q₂
    twoStageEnergy A R₁ R₂ Q₁ Q₂ y z x =
        RCLike.re (star y ⬝ᵥ
          (coarsePrecision (coarsePrecision A R₁ Q₁) R₂ Q₂ *ᵥ y)) ↔
      z = E₂ *ᵥ y ∧ x = (E₁ * E₂) *ᵥ y := by
  dsimp only
  have hH₁ := finePrecision_posDef Q₁ hA hR₁
  have hH₂ := finePrecision_posDef Q₂ (coarsePrecision_posDef Q₁ hA hR₁) hR₂
  rw [twoStageEnergy_completion Q₁ Q₂ hA hR₁ hR₂, add_assoc, add_eq_left,
    add_eq_zero_iff_of_nonneg (hH₂.posSemidef.re_dotProduct_nonneg _)
      (hH₁.posSemidef.re_dotProduct_nonneg _),
    quadratic_re_eq_zero_iff hH₂, quadratic_re_eq_zero_iff hH₁, sub_eq_zero, sub_eq_zero]
  constructor
  · rintro ⟨hz, hx⟩
    exact ⟨hz, by simpa only [hz, Matrix.mulVec_mulVec] using hx⟩
  · rintro ⟨hz, hx⟩
    exact ⟨hz, by simpa only [hz, Matrix.mulVec_mulVec] using hx⟩

omit [DecidableEq l] in
/-- Successive elimination solves the global joint minimization problem. -/
theorem is_joint_minimizer_iff (hA : A.PosDef) (hR₁ : R₁.PosDef)
    (hR₂ : R₂.PosDef) (y : l → ℝ) (z : m → ℝ) (x : n → ℝ) :
    let E₁ := harmonicExtension A R₁ Q₁
    let E₂ := harmonicExtension (coarsePrecision A R₁ Q₁) R₂ Q₂
    (∀ z' x', twoStageEnergy A R₁ R₂ Q₁ Q₂ y z x ≤
      twoStageEnergy A R₁ R₂ Q₁ Q₂ y z' x') ↔
      z = E₂ *ᵥ y ∧ x = (E₁ * E₂) *ᵥ y := by
  dsimp only
  let E₁ := harmonicExtension A R₁ Q₁
  let E₂ := harmonicExtension (coarsePrecision A R₁ Q₁) R₂ Q₂
  have hmin := (twoStageEnergy_eq_min_iff Q₁ Q₂ hA hR₁ hR₂ y
    (E₂ *ᵥ y) ((E₁ * E₂) *ᵥ y)).2 ⟨rfl, rfl⟩
  constructor
  · intro h
    apply (twoStageEnergy_eq_min_iff Q₁ Q₂ hA hR₁ hR₂ y z x).1
    refine le_antisymm ?_ (twoStageEnergy_lower_bound Q₁ Q₂ hA hR₁ hR₂ y z x)
    simpa only [hmin] using h (E₂ *ᵥ y) ((E₁ * E₂) *ᵥ y)
  · intro h z' x'
    rw [(twoStageEnergy_eq_min_iff Q₁ Q₂ hA hR₁ hR₂ y z x).2 h]
    exact twoStageEnergy_lower_bound Q₁ Q₂ hA hR₁ hR₂ y z' x'

/-- Combining the noise weights first gives the same precision as successive elimination. -/
theorem twoStage_coarsePrecision_eq_single (hA : A.PosDef) (hR₁ : R₁.PosDef)
    (hR₂ : R₂.PosDef) :
    coarsePrecision (coarsePrecision A R₁ Q₁) R₂ Q₂ =
      coarsePrecision A (coarsePrecision R₁ R₂ Q₂) (Q₂ * Q₁) := by
  have hS₁ := coarsePrecision_posDef Q₁ hA hR₁
  have hReff := coarsePrecision_posDef Q₂ hR₁ hR₂
  let := (coarsePrecision_posDef Q₂ hS₁ hR₂).isUnit.invertible
  let := (coarsePrecision_posDef (Q₂ * Q₁) hA hReff).isUnit.invertible
  have h : (coarsePrecision (coarsePrecision A R₁ Q₁) R₂ Q₂)⁻¹ =
      (coarsePrecision A (coarsePrecision R₁ R₂ Q₂) (Q₂ * Q₁))⁻¹ := by
    rw [twoStage_coarsePrecision_inv Q₁ Q₂ hA hR₁ hR₂,
      coarsePrecision_inv (Q₂ * Q₁) hA hReff,
      coarsePrecision_inv Q₂ hR₁ hR₂]
  simpa only [Matrix.inv_inv_of_invertible] using congrArg (fun M => M⁻¹) h

/-- Inverting a nonzero scalar identity needs no choice of coordinates. -/
theorem scalarIdentity_inv {k : Type*} [Fintype k] [DecidableEq k]
    (a : ℝ) (ha : a ≠ 0) :
    (a • (1 : Matrix k k ℝ))⁻¹ = a⁻¹ • (1 : Matrix k k ℝ) := by
  apply Matrix.inv_eq_right_inv
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    mul_inv_cancel₀ ha, one_smul]

/-- Isotropic input weights and a scaled coisometry give an isotropic output covariance. -/
theorem scalar_coarseCovariance {α β s : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (Q : Matrix m n ℝ) (hQ : Q * Qᵀ = s • (1 : Matrix m m ℝ)) :
    coarseCovariance (β • (1 : Matrix n n ℝ)) (α • (1 : Matrix m m ℝ)) Q =
      (α⁻¹ + s * β⁻¹) • (1 : Matrix m m ℝ) := by
  rw [coarseCovariance, scalarIdentity_inv α (ne_of_gt hα),
    scalarIdentity_inv β (ne_of_gt hβ)]
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul, hQ, smul_smul]
  rw [← add_smul, mul_comm β⁻¹ s]

/-- The matrix composition law specializes to the scalar coefficient used by `Convolution`. -/
theorem scalar_coarsePrecision {α β s : ℝ} (hα : 0 < α) (hβ : 0 < β) (hs : 0 ≤ s)
    (Q : Matrix m n ℝ) (hQ : Q * Qᵀ = s • (1 : Matrix m m ℝ)) :
    coarsePrecision (β • (1 : Matrix n n ℝ)) (α • (1 : Matrix m m ℝ)) Q =
      (α * β / (β + s * α)) • (1 : Matrix m m ℝ) := by
  have hA : (β • (1 : Matrix n n ℝ)).PosDef := Matrix.PosDef.one.smul hβ
  have hR : (α • (1 : Matrix m m ℝ)).PosDef := Matrix.PosDef.one.smul hα
  have ht : 0 < α⁻¹ + s * β⁻¹ :=
    add_pos_of_pos_of_nonneg (inv_pos.2 hα) (mul_nonneg hs (inv_nonneg.2 hβ.le))
  rw [← coarseCovariance_inv Q hA hR, scalar_coarseCovariance hα hβ Q hQ,
    scalarIdentity_inv _ (ne_of_gt ht)]
  have hscalar : α⁻¹ + s * β⁻¹ = (β + s * α) / (α * β) := by
    field_simp [ne_of_gt hα, ne_of_gt hβ] <;> ring
  rw [hscalar, inv_div]

end GaussianBlockSpin.MatrixWeighted
