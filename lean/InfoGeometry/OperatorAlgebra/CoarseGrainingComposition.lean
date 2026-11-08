/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CoarseGrainingVariational

/-!
# Composition of positive operator eliminations

Two arbitrary rectangular coarse-graining maps transport covariance in order.
The joint quadratic problem has the same unique minimizer as successive
elimination. The result retains both matrix-valued noise weights and every
cross-space coupling; no simultaneous diagonalization is assumed.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PositiveCoarseGraining

open Matrix
open scoped ComplexOrder

variable {𝕜 n m l : Type*} [RCLike 𝕜]
variable [Fintype n] [Fintype m] [Fintype l]
variable [DecidableEq n] [DecidableEq m] [DecidableEq l]
variable {A : Matrix n n 𝕜} {R₁ : Matrix m m 𝕜} {R₂ : Matrix l l 𝕜}
variable (Q₁ : Matrix m n 𝕜) (Q₂ : Matrix l m 𝕜)

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
def twoStageEnergy (A : Matrix n n 𝕜) (R₁ : Matrix m m 𝕜) (R₂ : Matrix l l 𝕜)
    (Q₁ : Matrix m n 𝕜) (Q₂ : Matrix l m 𝕜)
    (y : l → 𝕜) (z : m → 𝕜) (x : n → 𝕜) : ℝ :=
  quadraticEnergy A R₁ Q₁ z x +
    RCLike.re (star (y - Q₂ *ᵥ z) ⬝ᵥ (R₂ *ᵥ (y - Q₂ *ᵥ z)))

omit [DecidableEq l] in
/-- Two exact square completions retain both positive residual terms. -/
theorem twoStageEnergy_completion (hA : A.PosDef) (hR₁ : R₁.PosDef)
    (hR₂ : R₂.PosDef) (y : l → 𝕜) (z : m → 𝕜) (x : n → 𝕜) :
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
    (hR₂ : R₂.PosDef) (y : l → 𝕜) (z : m → 𝕜) (x : n → 𝕜) :
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
    (hR₂ : R₂.PosDef) (y : l → 𝕜) (z : m → 𝕜) (x : n → 𝕜) :
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
    (hR₂ : R₂.PosDef) (y : l → 𝕜) (z : m → 𝕜) (x : n → 𝕜) :
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

end InfoGeometry.OperatorAlgebra.PositiveCoarseGraining
