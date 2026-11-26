/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GromovTropicalPluckerFisherBridge
import InfoGeometry.LLM.EarlyLearningFoundations
import InfoGeometry.Canonical.AttentionQueryGibbsDuality

/-!
# Canonical Bridge Between Early Threshold XOR Obstructions, Penrose–Plücker Bilinear XOR, and Attention Gibbs Duality

Unifies three owners across learning foundations and finite attention geometry:
1. Direct Boolean equivalence between `EarlyLearningFoundations.twoLayerThresholdXOR` and the
   bilinear determinant `GromovTropicalPluckerFisherBridge.pluckerXOR` around threshold `1 / 2`,
   contrasted directly with `minsky_papert_no_single_layer_xor`,
2. Exact identification between `AttentionQueryGeometry.queryPotential K β q` and
   `β * tempLogPartition β (fun j => K j q)`,
3. Finite-temperature tropical sandwich bounds on `(1 / β) * queryPotential K β q` and on the
   entropy-regularized variational attention objective from `AttentionQueryGibbsDuality`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open AttentionInformationGeometry
open InfoGeometry.Canonical.GromovTropicalPluckerFisherBridge
open InfoGeometry.LLM.EarlyLearningFoundations
open InfoGeometry.Canonical.AttentionQueryGeometry
open InfoGeometry.Canonical.AttentionQueryGibbsDuality

namespace InfoGeometry.Canonical.GromovEarlyLearningAttentionBridge

private lemma bitToReal_eq_ite (b : Bool) : bitToReal b = (if b then 1 else 0) :=
  rfl

/-- `pluckerXOR` around decision threshold `1 / 2` is logically equivalent to the depth-2
McCulloch–Pitts threshold circuit `twoLayerThresholdXOR`. -/
theorem pluckerXOR_iff_twoLayerThresholdXOR (x₁ x₂ : Bool) :
    ((1 / 2 : ℝ) < pluckerXOR (bitToReal x₁) (bitToReal x₂)) ↔ twoLayerThresholdXOR x₁ x₂ := by
  rw [bitToReal_eq_ite, bitToReal_eq_ite, pluckerXOR_computes_bool_xor,
    mcculloch_pitts_two_layer_computes_xor]

/-- Unified XOR dichotomy: no single-layer threshold gate computes `xor`, whereas the bilinear
Plücker spinor minor evaluates to `if xor x₁ x₂ then 1 else 0` on Boolean inputs `{0, 1}`. -/
theorem xor_linear_impossibility_and_plucker_realization :
    (¬ ∃ w₁ w₂ θ : ℝ, ∀ x₁ x₂ : Bool,
        singleLayerThreshold w₁ w₂ θ x₁ x₂ ↔ xor x₁ x₂ = true) ∧
      (∀ x₁ x₂ : Bool, pluckerXOR (bitToReal x₁) (bitToReal x₂) = if xor x₁ x₂ then 1 else 0) := by
  refine ⟨minsky_papert_no_single_layer_xor, ?_⟩
  intro x₁ x₂
  cases x₁ <;> cases x₂ <;> simp [pluckerXOR_eq_sq_sub, bitToReal]

/-- The finite query log-partition potential equals `β * tempLogPartition β (fun j => K j q)`
whenever `β ≠ 0`. -/
theorem queryPotential_eq_mul_tempLogPartition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : ℕ} (K : Fin M → E →L[ℝ] ℝ) {β : ℝ} (hβ : β ≠ 0) (q : E) :
    queryPotential K β q = β * tempLogPartition β (fun j => K j q) := by
  unfold queryPotential tempLogPartition partitionZ queryLogits
  have hmul : β * (1 / β) = 1 := mul_one_div_cancel hβ
  rw [← mul_assoc, hmul, one_mul]

/-- Finite-temperature tropical sandwich for query attention logits:
`sup K_j(q) ≤ (1 / β) * queryPotential K β q ≤ sup K_j(q) + log M / β` for `β > 0`. -/
theorem queryPotential_tropical_sandwich
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : ℕ} [NeZero M] (K : Fin M → E →L[ℝ] ℝ) {β : ℝ} (hβ : 0 < β) (q : E) :
    Finset.univ.sup' Finset.univ_nonempty (fun j => K j q) ≤ (1 / β) * queryPotential K β q ∧
      (1 / β) * queryPotential K β q ≤
        Finset.univ.sup' Finset.univ_nonempty (fun j => K j q) + Real.log (M : ℝ) / β := by
  let a : Fin M → ℝ := fun j => K j q
  obtain ⟨jStar, _, hjStar_eq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty a
  have hjStar_max : ∀ j : Fin M, a j ≤ a jStar := fun j => by
    rw [← hjStar_eq]
    exact Finset.le_sup' a (Finset.mem_univ j)
  have hsand := tempLogPartition_tropical_sandwich (NeZero.pos M) β hβ a jStar hjStar_max
  have hscale : (1 / β) * queryPotential K β q = tempLogPartition β a := by
    rw [queryPotential_eq_mul_tempLogPartition K hβ.ne' q, ← mul_assoc, one_div_mul_cancel hβ.ne',
      one_mul]
  rw [hscale, hjStar_eq]
  exact hsand

/-- Variational entropy–regularized attention score is bounded above by the tropical maximum
score plus `(log M) / β` for every strictly positive probability distribution `μ`. -/
theorem queryAttention_entropy_regularized_tropical_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : ℕ} [NeZero M] (K : Fin M → E →L[ℝ] ℝ) {β : ℝ} (hβ : 0 < β) (q : E)
    (μ : Fin M → ℝ) (hμ_pos : ∀ j, 0 < μ j) (hμ_sum : ∑ j, μ j = 1) :
    ∑ j, μ j * K j q - (1 / β) * ∑ j, μ j * Real.log (μ j) ≤
      Finset.univ.sup' Finset.univ_nonempty (fun j => K j q) + Real.log (M : ℝ) / β := by
  have hvar := queryPotential_variational_bound K β q μ hμ_pos hμ_sum
  have hscaled := mul_le_mul_of_nonneg_left hvar (one_div_nonneg.mpr hβ.le)
  have hlhs :
      (1 / β) * (β * ∑ j, μ j * K j q - ∑ j, μ j * Real.log (μ j)) =
        ∑ j, μ j * K j q - (1 / β) * ∑ j, μ j * Real.log (μ j) := by
    rw [mul_sub, ← mul_assoc, one_div_mul_cancel hβ.ne', one_mul]
  rw [hlhs] at hscaled
  exact hscaled.trans (queryPotential_tropical_sandwich K hβ q).2

/-- Classical single-layer affine perceptron score `L(x₁, x₂) = w₁ x₁ + w₂ x₂ + b`. -/
def affinePerceptron (w₁ w₂ b x₁ x₂ : ℝ) : ℝ :=
  w₁ * x₁ + w₂ * x₂ + b

/-- Minsky–Papert (1969) affine perceptron XOR impossibility contrasted directly with
exact `{0, 1}²` evaluation of `GromovTropicalPluckerFisherBridge.pluckerXOR`. -/
theorem minsky_papert_xor_no_go_vs_plucker_spinor_resolution :
    (¬ ∃ w₁ w₂ b : ℝ,
      affinePerceptron w₁ w₂ b 0 0 < 0 ∧
      affinePerceptron w₁ w₂ b 1 1 < 0 ∧
      0 < affinePerceptron w₁ w₂ b 1 0 ∧
      0 < affinePerceptron w₁ w₂ b 0 1) ∧
    (pluckerXOR 0 0 = 0 ∧
     pluckerXOR 1 1 = 0 ∧
     pluckerXOR 1 0 = 1 ∧
     pluckerXOR 0 1 = 1) := by
  constructor
  · rintro ⟨w₁, w₂, b, h00, h11, h10, h01⟩
    unfold affinePerceptron at *
    linarith
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [pluckerXOR_eq_sq_sub]

/-- Finite-temperature tropical sandwich indexed by a witness index `j_max : Fin N`
(automatically ensuring `0 < N` via `Fin.pos j_max`). -/
theorem souriau_tropical_mcculloch_pitts_sandwich {N : ℕ}
    (β : ℝ) (hβ : 0 < β) (a : Fin N → ℝ) (j_max : Fin N)
    (hMax : ∀ j : Fin N, a j ≤ a j_max) :
    a j_max ≤ tempLogPartition β a ∧
      tempLogPartition β a ≤ a j_max + Real.log (N : ℝ) / β :=
  tempLogPartition_tropical_sandwich (Fin.pos j_max) β hβ a j_max hMax

end InfoGeometry.Canonical.GromovEarlyLearningAttentionBridge
