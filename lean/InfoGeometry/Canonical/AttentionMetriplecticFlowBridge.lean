/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import InfoGeometry.Canonical.AttentionInformationGeometry
import InfoGeometry.SuperMetriplectic.Flow

/-!
# Attention Metriplectic Flow Bridge

This module formalizes the exact mathematical bridge connecting the
**Fisher–Rao Information Metric of Softmax Attention** to the
**Abstract Metriplectic Flow Packet** (`InfoGeometry.SuperMetriplectic.Flow`).

It establishes:
1. `attentionOnsagerLinearMap`: The linear dissipative operator induced by the
   Fisher–Rao Hessian matrix `hessianLogZ s`.
2. `attentionOnsagerMetricData`: The canonical `OnsagerMetricData` packet for attention logits,
   with proved symmetry and positive semi-definiteness from the covariance of token observables.
3. `energy_degeneracy`: Exact annihilation of the uniform logit shift direction
   `L(1) = 0`, identifying the global additive gauge with the metriplectic Casimir.
4. `AttentionMetriplecticPacket`: An explicit, verified `MetriplecticFlow` realization
   where attention dynamics fuse symplectic reversible motion with Fisher dissipation.
-/

namespace InfoGeometry.Canonical.AttentionMetriplectic

open scoped BigOperators
open AttentionInformationGeometry
open InfoGeometry.SuperMetriplectic

variable {M : ℕ} [NeZero M]

/-! ### 1. Inner Product and Onsager Dissipative Operator -/

/-- Standard Euclidean pairing on the finite token logit space `Fin M → ℝ`. -/
def tokenPairing (u v : Fin M → ℝ) : ℝ :=
  ∑ j : Fin M, u j * v j

omit [NeZero M] in
/-- Symmetry of the token pairing. -/
theorem tokenPairing_comm (u v : Fin M → ℝ) :
    tokenPairing u v = tokenPairing v u := by
  dsimp [tokenPairing]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm (u j) (v j)

omit [NeZero M] in
/-- Right-annihilation of zero in the pairing. -/
theorem tokenPairing_zero_right (u : Fin M → ℝ) :
    tokenPairing u 0 = 0 := by
  dsimp [tokenPairing]
  simp only [mul_zero, Finset.sum_const_zero]

omit [NeZero M] in
/-- Matrix entry symmetry of the attention Fisher–Rao Hessian. -/
theorem hessianLogZ_symmetric (s : Fin M → ℝ) (j k : Fin M) :
    hessianLogZ s j k = hessianLogZ s k j := by
  dsimp [hessianLogZ]
  rw [mul_comm (softmaxProb s j) (softmaxProb s k)]
  by_cases h : j = k
  · subst h; rfl
  · have h' : ¬(k = j) := fun hkj => h hkj.symm
    simp [h, h']

/-- The linear Onsager dissipative operator `L : (Fin M → ℝ) →ₗ[ℝ] (Fin M → ℝ)`
given by multiplication by the attention Hessian matrix. -/
noncomputable def attentionOnsagerLinearMap (s : Fin M → ℝ) :
    (Fin M → ℝ) →ₗ[ℝ] (Fin M → ℝ) where
  toFun v := fun j => ∑ k : Fin M, hessianLogZ s j k * v k
  map_add' v w := by
    ext j
    dsimp
    simp_rw [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext j
    dsimp
    have hterm (k : Fin M) : hessianLogZ s j k * (c * v k) = c * (hessianLogZ s j k * v k) := by ring
    simp_rw [hterm, ← Finset.mul_sum]

/-! ### 2. Onsager Metric Properties: Symmetry and Nonnegativity -/

omit [NeZero M] in
/-- Metric symmetry: `⟨u, L v⟩ = ⟨v, L u⟩` following from Hessian matrix symmetry. -/
theorem attention_metric_symmetric (s : Fin M → ℝ) (u v : Fin M → ℝ) :
    tokenPairing u (attentionOnsagerLinearMap s v) =
      tokenPairing v (attentionOnsagerLinearMap s u) := by
  dsimp [tokenPairing, attentionOnsagerLinearMap]
  calc
    (∑ j : Fin M, u j * (∑ k : Fin M, hessianLogZ s j k * v k))
      = ∑ j : Fin M, ∑ k : Fin M, u j * hessianLogZ s j k * v k := by
        simp_rw [Finset.mul_sum, mul_assoc]
    _ = ∑ k : Fin M, ∑ j : Fin M, u j * hessianLogZ s j k * v k := by
        rw [Finset.sum_comm]
    _ = ∑ k : Fin M, ∑ j : Fin M, v k * hessianLogZ s k j * u j := by
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro j _
        rw [hessianLogZ_symmetric s j k]
        ring
    _ = ∑ k : Fin M, v k * (∑ j : Fin M, hessianLogZ s k j * u j) := by
        simp_rw [Finset.mul_sum, mul_assoc]

/-- Nonnegativity: `0 ≤ ⟨u, L u⟩` from positive semi-definiteness of the covariance Hessian. -/
theorem attention_metric_nonnegative (s : Fin M → ℝ) (u : Fin M → ℝ) :
    0 ≤ tokenPairing u (attentionOnsagerLinearMap s u) := by
  dsimp [tokenPairing, attentionOnsagerLinearMap]
  have h_eq : (∑ j : Fin M, u j * ∑ k : Fin M, hessianLogZ s j k * u k) =
      ∑ j : Fin M, ∑ k : Fin M, u j * hessianLogZ s j k * u k := by
    simp_rw [Finset.mul_sum, mul_assoc]
  rw [h_eq]
  exact hessianLogZ_positive_semidefinite s u

/-- Canonical instantiation of `OnsagerMetricData` for attention logit dynamics. -/
noncomputable def attentionOnsagerMetricData (s : Fin M → ℝ) :
    OnsagerMetricData (Fin M → ℝ) where
  onsager := attentionOnsagerLinearMap s
  pairing := tokenPairing
  metric_symmetric := attention_metric_symmetric s
  metric_nonnegative := attention_metric_nonnegative s
  pairing_zero_right := tokenPairing_zero_right

/-! ### 3. Energy Casimir: Annihilation of the Constant Logit Gauge -/

omit [NeZero M] in
/-- The constant logit gauge vector `1 = (1, 1, ..., 1)`. -/
def unitGaugeVector : Fin M → ℝ :=
  fun _ => 1

/-- Energy degeneracy: The attention Onsager operator strictly annihilates the
constant logit vector: `L(1) = 0`. -/
theorem attention_onsager_unitGaugeVector_eq_zero (s : Fin M → ℝ) :
    attentionOnsagerLinearMap s unitGaugeVector = 0 := by
  ext j
  dsimp [attentionOnsagerLinearMap, unitGaugeVector]
  simp_rw [mul_one]
  dsimp [hessianLogZ]
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ k : Fin M, (if j = k then softmaxProb s j else 0)) = softmaxProb s j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hne
      simp [Ne.symm hne]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  have h2 : (∑ k : Fin M, softmaxProb s j * softmaxProb s k) = softmaxProb s j := by
    rw [← Finset.mul_sum, softmaxProb_sum s, mul_one]
  rw [h1, h2, sub_self]

/-! ### 4. Assembling the Attention Metriplectic Flow -/

/-- Canonical construction of an attention metriplectic flow.
Combines an arbitrary reversible vector (such as symplectic token drift)
with the gradient dissipative flow along the Fisher–Rao metric. -/
noncomputable def makeAttentionMetriplecticFlow
    (s : Fin M → ℝ)
    (entropyForce : Fin M → ℝ)
    (reversibleFlow : Fin M → ℝ) :
    MetriplecticFlow (Fin M → ℝ) where
  metric := attentionOnsagerMetricData s
  entropyForce := entropyForce
  energyForce := unitGaugeVector
  reversibleFlow := reversibleFlow
  dissipativeFlow := attentionOnsagerLinearMap s entropyForce
  totalFlow := reversibleFlow + attentionOnsagerLinearMap s entropyForce
  entropyProduction := tokenPairing entropyForce (attentionOnsagerLinearMap s entropyForce)
  dissipativeFlow_eq_onsager_entropy := rfl
  totalFlow_eq_reversible_add_dissipative := rfl
  energy_degeneracy := attention_onsager_unitGaugeVector_eq_zero s
  entropyProduction_eq_quadratic := rfl

/-- Canonical alias for the attention metriplectic flow constructor. -/
noncomputable abbrev AttentionMetriplecticPacket
    (s : Fin M → ℝ)
    (entropyForce : Fin M → ℝ)
    (reversibleFlow : Fin M → ℝ) :
    MetriplecticFlow (Fin M → ℝ) :=
  makeAttentionMetriplecticFlow s entropyForce reversibleFlow

/-- The Second Law for Attention: Entropy production in any attention metriplectic
flow is strictly non-negative. -/
theorem attention_entropy_production_nonnegative
    (s : Fin M → ℝ)
    (entropyForce : Fin M → ℝ)
    (reversibleFlow : Fin M → ℝ) :
    0 ≤ (makeAttentionMetriplecticFlow s entropyForce reversibleFlow).entropyProduction :=
  (makeAttentionMetriplecticFlow s entropyForce reversibleFlow).entropyProduction_nonnegative

/-- Energy Conservation: The dissipative attention flow strictly conserves the
global additive logit energy: `⟨1, L dS⟩ = 0`. -/
theorem attention_dissipative_energy_conserved
    (s : Fin M → ℝ)
    (entropyForce : Fin M → ℝ)
    (reversibleFlow : Fin M → ℝ) :
    tokenPairing unitGaugeVector (attentionOnsagerLinearMap s entropyForce) = 0 := by
  have h := (makeAttentionMetriplecticFlow s entropyForce reversibleFlow).dissipative_energy_change_eq_zero
  dsimp [makeAttentionMetriplecticFlow] at h
  exact h

end InfoGeometry.Canonical.AttentionMetriplectic
