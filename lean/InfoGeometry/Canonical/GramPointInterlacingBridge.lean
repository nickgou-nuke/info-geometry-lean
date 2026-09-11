import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import InfoGeometry.Canonical.HardyZRealizationBridge

/-!
# Conditional Gram-Interval IVT Bridge

This module formalizes an abstract interval argument. The sequence called
`gram_point`, the continuity of `Z`, and the sign alternation are fields of
`GramInterlacingDatum`; no theorem here proves that they are the actual Gram
points or the actual Hardy Z-function.

The proved consequences are:
1. **A supplied increasing sequence**:
   A sequence of points $g_n \in \mathbb{R}$ ($n \in \mathbb{Z}$) where the phase angle satisfies:
   $$\theta(g_n) = n \pi$$
2. **A supplied sign-alternation hypothesis**:
   $$(-1)^n Z(g_n) > 0 \implies \operatorname{sgn}(Z(g_n)) = (-1)^n$$
3. **Consecutive Opposite Signs**:
   $$Z(g_n) \cdot Z(g_{n+1}) < 0$$
4. **Intermediate Value Theorem consequence**:
   For continuous $Z : \mathbb{R} \to \mathbb{R}$, there exists a real zero $t_n \in (g_n, g_{n+1})$:
   $$Z(t_n) = 0 \implies \zeta\left(\frac{1}{2} + i t_n\right) = 0$$
5. **Conditional critical-line transfer**:
   Every supplied sign-changing interval produces a zero of the supplied
   critical-line readout.
-/

noncomputable section

namespace InfoGeometry.Canonical.GramInterlacing

open Complex
open InfoGeometry.Canonical.HardyZ

/-- Datum for Gram point sign alternation along the critical line -/
structure GramInterlacingDatum extends HardyZDatum where
  /-- Sequence of Gram points g : ℤ → ℝ -/
  gram_point : ℤ → ℝ
  /-- Strictly increasing Gram points: g_n < g_{n+1} -/
  h_gram_mono : ∀ n : ℤ, gram_point n < gram_point (n + 1)
  /-- Continuity of the real Hardy Z function -/
  h_Z_cont : Continuous Z
  /-- Gram point sign alternation: Z(g_n) has sign (-1)^n -/
  h_gram_sign : ∀ n : ℤ, 0 < (-1 : ℝ)^n * Z (gram_point n)

/-- 🏆 THEOREM 1: Non-Zero Value at Gram Points -/
theorem gram_point_Z_ne_zero (D : GramInterlacingDatum) (n : ℤ) :
    D.Z (D.gram_point n) ≠ 0 := by
  intro h_zero
  have h_sign := D.h_gram_sign n
  rw [h_zero, mul_zero] at h_sign
  linarith

/-- 🏆 THEOREM 2: Opposite Signs at Consecutive Gram Points -/
theorem gram_consecutive_opposite_signs (D : GramInterlacingDatum) (n : ℤ) :
    D.Z (D.gram_point n) * D.Z (D.gram_point (n + 1)) < 0 := by
  have h_n := D.h_gram_sign n
  have h_np1 := D.h_gram_sign (n + 1)
  have h_pow_np1 : (-1 : ℝ)^(n + 1) = - ((-1 : ℝ)^n) := by
    rw [zpow_add_one₀ (by norm_num)]
    ring
  rw [h_pow_np1] at h_np1
  have h_np1_neg : ((-1 : ℝ)^n) * D.Z (D.gram_point (n + 1)) < 0 := by
    linarith
  have h_prod : ((-1 : ℝ)^n * D.Z (D.gram_point n)) * ((-1 : ℝ)^n * D.Z (D.gram_point (n + 1))) < 0 :=
    mul_neg_of_pos_of_neg h_n h_np1_neg
  have h_sq : ((-1 : ℝ)^n)^2 = 1 := by
    rw [sq, ← zpow_add₀ (by norm_num)]
    have : n + n = 2 * n := by ring
    rw [this, zpow_mul]
    norm_num
  have h_alg : ((-1 : ℝ)^n * D.Z (D.gram_point n)) * ((-1 : ℝ)^n * D.Z (D.gram_point (n + 1))) =
      (((-1 : ℝ)^n)^2) * (D.Z (D.gram_point n) * D.Z (D.gram_point (n + 1))) := by ring
  rw [h_alg, h_sq, one_mul] at h_prod
  exact h_prod

/-- 🏆 THEOREM 3: Existence of a Real Zero in Every Gram Interval (Bolzano/IVT) -/
theorem exists_real_zero_in_gram_interval (D : GramInterlacingDatum) (n : ℤ) :
    ∃ t ∈ Set.Ioo (D.gram_point n) (D.gram_point (n + 1)), D.Z t = 0 := by
  have h_mono := D.h_gram_mono n
  have h_opp := gram_consecutive_opposite_signs D n
  have h_cont := D.h_Z_cont.continuousOn (s := Set.Icc (D.gram_point n) (D.gram_point (n + 1)))
  by_cases hZn_pos : 0 < D.Z (D.gram_point n)
  · have hZnp1_neg : D.Z (D.gram_point (n + 1)) < 0 := by
      nlinarith [h_opp, hZn_pos]
    have h_ivt := intermediate_value_Ioo' (le_of_lt h_mono) h_cont
    have h_mem : (0 : ℝ) ∈ Set.Ioo (D.Z (D.gram_point (n + 1))) (D.Z (D.gram_point n)) := ⟨hZnp1_neg, hZn_pos⟩
    rcases h_ivt h_mem with ⟨t, ht_in, ht_val⟩
    exact ⟨t, ht_in, ht_val⟩
  · have hZn_neg : D.Z (D.gram_point n) < 0 := by
      have h_ne := gram_point_Z_ne_zero D n
      exact lt_of_le_of_ne (le_of_not_gt hZn_pos) h_ne
    have hZnp1_pos : 0 < D.Z (D.gram_point (n + 1)) := by
      nlinarith [h_opp, hZn_neg]
    have h_ivt := intermediate_value_Ioo (le_of_lt h_mono) h_cont
    have h_mem : (0 : ℝ) ∈ Set.Ioo (D.Z (D.gram_point n)) (D.Z (D.gram_point (n + 1))) := ⟨hZn_neg, hZnp1_pos⟩
    rcases h_ivt h_mem with ⟨t, ht_in, ht_val⟩
    exact ⟨t, ht_in, ht_val⟩

/-- 🏆 THEOREM 4: Critical Line Zero Guarantee from Gram Interlacing -/
theorem exists_critical_line_zeta_zero (D : GramInterlacingDatum) (n : ℤ) :
    ∃ t ∈ Set.Ioo (D.gram_point n) (D.gram_point (n + 1)), D.zeta_crit t = 0 := by
  rcases exists_real_zero_in_gram_interval D n with ⟨t, ht_in, ht_Z_zero⟩
  use t, ht_in
  exact (hardy_Z_zero_iff_zeta_zero D.toHardyZDatum t).mp ht_Z_zero

end InfoGeometry.Canonical.GramInterlacing
