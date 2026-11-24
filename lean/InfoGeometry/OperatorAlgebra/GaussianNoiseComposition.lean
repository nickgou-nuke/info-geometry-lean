/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CoarseGrainingComposition
import Mathlib.Tactic.FieldSimp

/-!
# Collapse of matrix-valued Gaussian noise

Successive coarse observations combine their noise covariances by transport
and addition. Their collapsed noise precision is the existing Schur complement
`coarsePrecision R₁ R₂ Q₂`; its positivity and inverse are supplied by
`coarsePrecision_posDef Q₂ hR₁ hR₂` and `coarsePrecision_inv Q₂ hR₁ hR₂`.

The new composition theorem identifies two successive eliminations with one
elimination using this collapsed noise and the ordered composite map. The
observation maps may be rectangular and no commutation is assumed. The real scalar corollary
recovers `α * β / (β + s * α)` under `Q * Qᴴ = s • 1`.

These are identities of finite precision and covariance matrices. Gaussian
measure or Markov-kernel composition requires separate measure-theoretic
theorems.
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

/-- Covariance transport commutes with collapsing the two noise precisions. -/
theorem coarseCovariance_comp (hA : A.PosDef) (hR₁ : R₁.PosDef)
    (hR₂ : R₂.PosDef) :
    coarseCovariance (coarsePrecision A R₁ Q₁) R₂ Q₂ =
      coarseCovariance A (coarsePrecision R₁ R₂ Q₂) (Q₂ * Q₁) := by
  change R₂⁻¹ + Q₂ * (coarsePrecision A R₁ Q₁)⁻¹ * Q₂ᴴ =
    (coarsePrecision R₁ R₂ Q₂)⁻¹ + (Q₂ * Q₁) * A⁻¹ * (Q₂ * Q₁)ᴴ
  rw [coarsePrecision_inv Q₁ hA hR₁, coarsePrecision_inv Q₂ hR₁ hR₂]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc, add_assoc]

/-- Two positive eliminations equal one elimination with their collapsed noise.

Taking `A` itself to be the first noise precision also gives associativity of
three successive noise stages, with the indicated composite observation map.
-/
theorem coarsePrecision_comp (hA : A.PosDef) (hR₁ : R₁.PosDef)
    (hR₂ : R₂.PosDef) :
    coarsePrecision (coarsePrecision A R₁ Q₁) R₂ Q₂ =
      coarsePrecision A (coarsePrecision R₁ R₂ Q₂) (Q₂ * Q₁) := by
  rw [← coarseCovariance_inv Q₂ (coarsePrecision_posDef Q₁ hA hR₁) hR₂,
    ← coarseCovariance_inv (Q₂ * Q₁) hA (coarsePrecision_posDef Q₂ hR₁ hR₂),
    coarseCovariance_comp Q₁ Q₂ hA hR₁ hR₂]

/-- The inverse after collapse is the sum of the transported prior covariance
and the already-composed noise covariance. -/
theorem coarsePrecision_comp_inv (hA : A.PosDef) (hR₁ : R₁.PosDef)
    (hR₂ : R₂.PosDef) :
    (coarsePrecision (coarsePrecision A R₁ Q₁) R₂ Q₂)⁻¹ =
      (coarsePrecision R₁ R₂ Q₂)⁻¹ + (Q₂ * Q₁) * A⁻¹ * (Q₂ * Q₁)ᴴ := by
  rw [coarsePrecision_comp Q₁ Q₂ hA hR₁ hR₂,
    coarsePrecision_inv (Q₂ * Q₁) hA (coarsePrecision_posDef Q₂ hR₁ hR₂)]

section RealScalarNoise

private theorem inv_smul_one_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℝ) (ha : a ≠ 0) :
    (a • (1 : Matrix ι ι ℝ))⁻¹ = a⁻¹ • (1 : Matrix ι ι ℝ) := by
  apply Matrix.inv_eq_left_inv
  simp [smul_smul, ha]

/-- The covariance underlying the scalar block-convolution formula. -/
theorem coarseCovariance_scalar_noise (Q : Matrix l m ℝ) {α β s : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hQ : Q * Qᴴ = s • (1 : Matrix l l ℝ)) :
    coarseCovariance (β • (1 : Matrix m m ℝ)) (α • (1 : Matrix l l ℝ)) Q =
      (α⁻¹ + β⁻¹ * s) • (1 : Matrix l l ℝ) := by
  rw [coarseCovariance, inv_smul_one_real α hα.ne', inv_smul_one_real β hβ.ne']
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQ, smul_smul,
    ← add_smul]

/-- Scalar positive noise and a scaled coisometry recover the usual convolution
coefficient. The hypothesis `0 ≤ s` also covers an empty output index type. -/
theorem coarsePrecision_scalar_noise (Q : Matrix l m ℝ) {α β s : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hs : 0 ≤ s)
    (hQ : Q * Qᴴ = s • (1 : Matrix l l ℝ)) :
    coarsePrecision (β • (1 : Matrix m m ℝ)) (α • (1 : Matrix l l ℝ)) Q =
      (α * β / (β + s * α)) • (1 : Matrix l l ℝ) := by
  have hαI : (α • (1 : Matrix l l ℝ)).PosDef :=
    (Matrix.PosDef.one : (1 : Matrix l l ℝ).PosDef).smul hα
  have hβI : (β • (1 : Matrix m m ℝ)).PosDef :=
    (Matrix.PosDef.one : (1 : Matrix m m ℝ).PosDef).smul hβ
  have hc : 0 < α⁻¹ + β⁻¹ * s :=
    add_pos_of_pos_of_nonneg (inv_pos.mpr hα)
      (mul_nonneg (inv_nonneg.mpr hβ.le) hs)
  have hsum : α⁻¹ + β⁻¹ * s = (β + s * α) / (α * β) := by
    field_simp [hα.ne', hβ.ne']
  rw [← coarseCovariance_inv Q hβI hαI,
    coarseCovariance_scalar_noise Q hα hβ hQ,
    inv_smul_one_real (α⁻¹ + β⁻¹ * s) hc.ne', hsum, inv_div]

/-- The scalar convolution coefficient may be substituted directly into the
general rectangular elimination theorem. -/
theorem coarsePrecision_comp_scalar_noise {A : Matrix n n ℝ}
    (Q₁ : Matrix m n ℝ) (Q₂ : Matrix l m ℝ) {α β s : ℝ}
    (hA : A.PosDef) (hα : 0 < α) (hβ : 0 < β) (hs : 0 ≤ s)
    (hQ₂ : Q₂ * Q₂ᴴ = s • (1 : Matrix l l ℝ)) :
    coarsePrecision (coarsePrecision A (β • (1 : Matrix m m ℝ)) Q₁)
        (α • (1 : Matrix l l ℝ)) Q₂ =
      coarsePrecision A ((α * β / (β + s * α)) • (1 : Matrix l l ℝ)) (Q₂ * Q₁) := by
  have hαI : (α • (1 : Matrix l l ℝ)).PosDef :=
    (Matrix.PosDef.one : (1 : Matrix l l ℝ).PosDef).smul hα
  have hβI : (β • (1 : Matrix m m ℝ)).PosDef :=
    (Matrix.PosDef.one : (1 : Matrix m m ℝ).PosDef).smul hβ
  rw [coarsePrecision_comp Q₁ Q₂ hA hβI hαI,
    coarsePrecision_scalar_noise Q₂ hα hβ hs hQ₂]

end RealScalarNoise

end InfoGeometry.OperatorAlgebra.PositiveCoarseGraining
