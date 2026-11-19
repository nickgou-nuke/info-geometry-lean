/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.InformationEnergy.BinaryErasure

/-!
# Entropy effective counts and genuine finite state counts

For positive normalized finite weights, exponentiating Shannon entropy gives
an effective count. It agrees with the size of the state space exactly at
uniform weights. The same comparison holds between `exp (N * entropyOf q)`
and the actual cardinality of length-`N` words, for positive `N`.

This corrects the cardinality interpretation of Vopson (2019), equation (3).
It does not define a new probability carrier or infer physical microstates.
-/

noncomputable section

namespace InfoGeometry.Physics.InformationEnergy.EffectiveStateCount

open scoped BigOperators
open InfoGeometry.Inference.FiniteGibbs

variable {α : Type*} [Fintype α] [Nonempty α]

/-- The true length-`N` word count is the exponential of `N` times log-cardinality. -/
theorem word_count_eq_exp (N : ℕ) :
    (Fintype.card (Fin N → α) : ℝ) =
      Real.exp ((N : ℝ) * Real.log (Fintype.card α)) := by
  have hcard : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  simp [Real.exp_nat_mul, Real.exp_log hcard]

/-- Entropy effective count never exceeds the number of possible finite words. -/
theorem effectiveCount_le_word_count (q : α → ℝ) (hq : ∀ i, 0 < q i)
    (hsum : ∑ i, q i = 1) (N : ℕ) :
    Real.exp ((N : ℝ) * entropyOf q) ≤ (Fintype.card (Fin N → α) : ℝ) := by
  rw [word_count_eq_exp]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (entropyOf_le_log_card q hq hsum) (Nat.cast_nonneg N)

/-- For a positive word length, actual cardinality is attained exactly at uniformity. -/
theorem effectiveCount_eq_word_count_iff_uniform (q : α → ℝ) (hq : ∀ i, 0 < q i)
    (hsum : ∑ i, q i = 1) (N : ℕ) (hN : 0 < N) :
    Real.exp ((N : ℝ) * entropyOf q) = (Fintype.card (Fin N → α) : ℝ) ↔
      ∀ i, q i = 1 / (Fintype.card α : ℝ) := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [word_count_eq_exp]
  constructor
  · intro h
    apply (entropyOf_eq_log_card_iff_uniform q hq hsum).mp
    exact mul_left_cancel₀ hNreal (Real.exp_injective h)
  · intro h
    rw [(entropyOf_eq_log_card_iff_uniform q hq hsum).mpr h]

/-- A nonuniform law gives a strict effective-count deficit at every positive word length. -/
theorem effectiveCount_lt_word_count (q : α → ℝ) (hq : ∀ i, 0 < q i)
    (hsum : ∑ i, q i = 1) (N : ℕ) (hN : 0 < N)
    (hnonuniform : ¬ ∀ i, q i = 1 / (Fintype.card α : ℝ)) :
    Real.exp ((N : ℝ) * entropyOf q) < (Fintype.card (Fin N → α) : ℝ) := by
  apply lt_of_le_of_ne (effectiveCount_le_word_count q hq hsum N)
  intro h
  exact hnonuniform ((effectiveCount_eq_word_count_iff_uniform q hq hsum N hN).mp h)

/-- A genuine nonuniform binary law has an effective count strictly between one and two. -/
theorem binary_effectiveCount_between (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hne : p ≠ 2⁻¹) :
    1 < Real.exp (Real.binEntropy p) ∧ Real.exp (Real.binEntropy p) < 2 := by
  constructor
  · simpa using Real.exp_lt_exp.mpr (Real.binEntropy_pos hp hp1)
  · calc
      Real.exp (Real.binEntropy p) < Real.exp (Real.log 2) :=
        Real.exp_lt_exp.mpr (Real.binEntropy_lt_log_two.mpr hne)
      _ = 2 := Real.exp_log (by norm_num)

/-- In particular, the binary effective count is not a cardinality at nonuniform interior weights. -/
theorem binary_effectiveCount_not_nat (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hne : p ≠ 2⁻¹) (m : ℕ) :
    Real.exp (Real.binEntropy p) ≠ (m : ℝ) := by
  intro heq
  obtain ⟨hlo, hhi⟩ := binary_effectiveCount_between p hp hp1 hne
  rw [heq] at hlo hhi
  have hmlo : 1 < m := by exact_mod_cast hlo
  have hmhi : m < 2 := by exact_mod_cast hhi
  omega

end InfoGeometry.Physics.InformationEnergy.EffectiveStateCount
