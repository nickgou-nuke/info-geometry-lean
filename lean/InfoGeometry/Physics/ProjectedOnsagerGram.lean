/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.FiniteOnsagerGram
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Energy-preserving projected Gram dissipation

The positive pairing here is the ordinary real coordinate dot product, not
an indefinite split norm. The energy projector is constructed explicitly;
at the zero energy covector it is the identity. For a nonnegative real rate
`γ`, the operator `γ (R P)ᵀ (R P)` is symmetric, positive semidefinite, and
annihilates the energy covector. Its production vanishes exactly when the
projected force lies in the kernel of `R`, provided `γ > 0`.

These are pointwise finite-dimensional operator laws. Identifying the force
vectors with differentials of particular functions, solving an evolution,
or specifying heat exchange requires further data.
-/

noncomputable section

namespace InfoGeometry.Physics.ProjectedOnsagerGram

open Matrix
open InfoGeometry.Physics.FiniteOnsagerGram
open InfoGeometry.SuperMetriplectic

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Orthogonal projection off the line spanned by the energy covector.
The field convention `0⁻¹ = 0` makes this the identity at `h = 0`. -/
def energyProjector (h : n → ℝ) : Matrix n n ℝ :=
  1 - (dotProduct h h)⁻¹ • Matrix.vecMulVec h h

theorem energyProjector_mulVec (h v : n → ℝ) :
    energyProjector h *ᵥ v =
      v - (dotProduct h v / dotProduct h h) • h := by
  unfold energyProjector
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  ext i
  change v i - (dotProduct h h)⁻¹ * (∑ j, h i * h j * v j) =
    v i - (dotProduct h v / dotProduct h h) * h i
  have hsum : (∑ j, h i * h j * v j) = h i * dotProduct h v := by
    simp only [dotProduct, Finset.mul_sum, mul_assoc]
  rw [hsum]
  ring

@[simp] theorem energyProjector_zero :
    energyProjector (0 : n → ℝ) = 1 := by
  simp [energyProjector]

@[simp] theorem energyProjector_transpose (h : n → ℝ) :
    (energyProjector h)ᵀ = energyProjector h := by
  simp [energyProjector, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_vecMulVec]

@[simp] theorem energyProjector_energy (h : n → ℝ) :
    energyProjector h *ᵥ h = 0 := by
  rw [energyProjector_mulVec]
  by_cases hh : h = 0
  · simp [hh]
  · have hnorm : dotProduct h h ≠ 0 :=
      fun hz => hh (dotProduct_self_eq_zero.mp hz)
    rw [div_self hnorm, one_smul, sub_self]

/-- The projected vector is orthogonal to the energy covector, also at zero. -/
theorem energyProjector_orthogonal (h v : n → ℝ) :
    dotProduct h (energyProjector h *ᵥ v) = 0 := by
  by_cases hh : h = 0
  · simp [hh]
  · have hnorm : dotProduct h h ≠ 0 :=
      fun hz => hh (dotProduct_self_eq_zero.mp hz)
    rw [energyProjector_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul, div_mul_cancel₀ _ hnorm, sub_self]

theorem energyProjector_idempotent (h : n → ℝ) :
    energyProjector h * energyProjector h = energyProjector h := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec, energyProjector_mulVec h (energyProjector h *ᵥ v),
    energyProjector_orthogonal, zero_div, zero_smul, sub_zero]

/-- A nonnegative rate multiplies a Gram matrix after energy projection.
The rate is a real number, not a Clifford generator. -/
def projectedGram (γ : ℝ) (R : Matrix m n ℝ) (h : n → ℝ) : Matrix n n ℝ :=
  γ • ((R * energyProjector h)ᵀ * (R * energyProjector h))

@[simp] theorem projectedGram_transpose (γ : ℝ) (R : Matrix m n ℝ) (h : n → ℝ) :
    (projectedGram γ R h)ᵀ = projectedGram γ R h := by
  simp [projectedGram, Matrix.transpose_mul, Matrix.transpose_smul]

/-- The exact squared leakage, reusing the existing finite Gram identity. -/
theorem projectedGram_contraction (γ : ℝ) (R : Matrix m n ℝ) (h v : n → ℝ) :
    dotProduct v (projectedGram γ R h *ᵥ v) =
      γ * ∑ i : m, ((R *ᵥ (energyProjector h *ᵥ v)) i) ^ 2 := by
  unfold projectedGram
  rw [Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
    gram_contraction]
  simp only [← Matrix.mulVec_mulVec, smul_eq_mul]

theorem projectedGram_nonnegative (γ : ℝ) (hγ : 0 ≤ γ)
    (R : Matrix m n ℝ) (h v : n → ℝ) :
    0 ≤ dotProduct v (projectedGram γ R h *ᵥ v) := by
  rw [projectedGram_contraction]
  exact mul_nonneg hγ (Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem projectedGram_symmetric (γ : ℝ) (R : Matrix m n ℝ) (h u v : n → ℝ) :
    dotProduct u (projectedGram γ R h *ᵥ v) =
      dotProduct v (projectedGram γ R h *ᵥ u) := by
  calc
    _ = dotProduct u ((projectedGram γ R h)ᵀ *ᵥ v) := by
      rw [projectedGram_transpose]
    _ = dotProduct (projectedGram γ R h *ᵥ u) v :=
      dot_transpose_mulVec _ _ _
    _ = _ := dotProduct_comm _ _

@[simp] theorem projectedGram_energy (γ : ℝ) (R : Matrix m n ℝ) (h : n → ℝ) :
    projectedGram γ R h *ᵥ h = 0 := by
  simp [projectedGram, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]

/-- Zero production is exactly zero projected leakage when the rate is positive. -/
theorem projectedGram_contraction_eq_zero_iff (γ : ℝ) (hγ : 0 < γ)
    (R : Matrix m n ℝ) (h v : n → ℝ) :
    dotProduct v (projectedGram γ R h *ᵥ v) = 0 ↔
      R *ᵥ (energyProjector h *ᵥ v) = 0 := by
  rw [projectedGram_contraction]
  have hsquares : (∑ i : m, ((R *ᵥ (energyProjector h *ᵥ v)) i) ^ 2) =
      dotProduct (R *ᵥ (energyProjector h *ᵥ v))
        (R *ᵥ (energyProjector h *ᵥ v)) := by
    simp only [dotProduct, pow_two]
  rw [hsquares, mul_eq_zero, dotProduct_self_eq_zero]
  simp [ne_of_gt hγ]

theorem projectedGram_contraction_pos_iff (γ : ℝ) (hγ : 0 < γ)
    (R : Matrix m n ℝ) (h v : n → ℝ) :
    0 < dotProduct v (projectedGram γ R h *ᵥ v) ↔
      R *ᵥ (energyProjector h *ᵥ v) ≠ 0 := by
  have hzero := projectedGram_contraction_eq_zero_iff γ hγ R h v
  constructor
  · intro hpos hleak
    exact (ne_of_gt hpos) (hzero.mpr hleak)
  · intro hleak
    exact lt_of_le_of_ne (projectedGram_nonnegative γ hγ.le R h v)
      (fun hz => hleak (hzero.mp hz.symm))

/-- Concrete Onsager data: symmetry and positivity are proved from `R`,
and the energy kernel is enforced by the explicit projector. -/
def projectedGramMetricData (γ : ℝ) (hγ : 0 ≤ γ)
    (R : Matrix m n ℝ) (h : n → ℝ) : OnsagerMetricData (n → ℝ) where
  onsager := Matrix.toLin' (projectedGram γ R h)
  pairing := dotProduct
  metric_symmetric := projectedGram_symmetric γ R h
  metric_nonnegative := projectedGram_nonnegative γ hγ R h
  pairing_zero_right := dotProduct_zero

@[simp] theorem projectedGramMetricData_energy (γ : ℝ) (hγ : 0 ≤ γ)
    (R : Matrix m n ℝ) (h : n → ℝ) :
    (projectedGramMetricData γ hγ R h).onsager h = 0 :=
  projectedGram_energy γ R h

/-- The dissipative contribution to the energy rate vanishes identically. -/
theorem dissipative_energy_rate (γ : ℝ) (R : Matrix m n ℝ) (h s : n → ℝ) :
    dotProduct h (projectedGram γ R h *ᵥ s) = 0 := by
  rw [projectedGram_symmetric, projectedGram_energy, dotProduct_zero]

/-- The skew reversible part and projected Gram part both preserve energy. -/
theorem total_energy_rate (A : Matrix n n ℝ) (γ : ℝ)
    (R : Matrix m n ℝ) (h s : n → ℝ) :
    dotProduct h ((A - Aᵀ) *ᵥ h + projectedGram γ R h *ᵥ s) = 0 := by
  rw [dotProduct_add, skew_contraction_zero, dissipative_energy_rate, add_zero]

/-- For one chosen energy/entropy pair, zero reversible entropy rate suffices.
This hypothesis is weaker than requiring entropy to be a full Poisson Casimir. -/
theorem total_entropy_rate (A : Matrix n n ℝ) (γ : ℝ)
    (R : Matrix m n ℝ) (h s : n → ℝ)
    (hrev : dotProduct s ((A - Aᵀ) *ᵥ h) = 0) :
    dotProduct s ((A - Aᵀ) *ᵥ h + projectedGram γ R h *ᵥ s) =
      γ * ∑ i : m, ((R *ᵥ (energyProjector h *ᵥ s)) i) ^ 2 := by
  rw [dotProduct_add, hrev, zero_add, projectedGram_contraction]

end InfoGeometry.Physics.ProjectedOnsagerGram
