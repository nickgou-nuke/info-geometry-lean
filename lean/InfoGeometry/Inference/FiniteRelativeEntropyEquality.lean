/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteRelativeEntropy

/-!
# Equality case for finite relative entropy
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Data : Type*} [Fintype Data]

noncomputable def relativeEntropyGap
    (q p : Data → ℝ) (i : Data) : ℝ :=
  q i * Real.log (q i / p i) - (q i - p i)

theorem relativeEntropyGap_nonneg
    (q p : Data → ℝ)
    (hq_pos : ∀ i, 0 < q i)
    (hp_pos : ∀ i, 0 < p i) (i : Data) :
    0 ≤ relativeEntropyGap q p i := by
  unfold relativeEntropyGap
  have hlog := Real.log_le_sub_one_of_pos
    (div_pos (hp_pos i) (hq_pos i))
  have hmul := mul_le_mul_of_nonneg_left hlog (hq_pos i).le
  have hratio : q i / p i = (p i / q i)⁻¹ := by
    field_simp [ne_of_gt (hq_pos i), ne_of_gt (hp_pos i)]
  have hleft : q i * Real.log (q i / p i) =
      -(q i * Real.log (p i / q i)) := by
    rw [hratio, Real.log_inv]
    ring
  have hright : q i * (p i / q i - 1) = p i - q i := by
    field_simp [ne_of_gt (hq_pos i)]
  rw [hright] at hmul
  linarith

theorem relativeEntropyGap_pos_of_ne
    (q p : Data → ℝ)
    (hq_pos : ∀ i, 0 < q i)
    (hp_pos : ∀ i, 0 < p i) {i : Data}
    (hneq : q i ≠ p i) :
    0 < relativeEntropyGap q p i := by
  unfold relativeEntropyGap
  have hratio_ne : p i / q i ≠ 1 := by
    intro h
    apply hneq
    field_simp [ne_of_gt (hq_pos i)] at h
    linarith
  have hlog := Real.log_lt_sub_one_of_pos
    (div_pos (hp_pos i) (hq_pos i)) hratio_ne
  have hmul := mul_lt_mul_of_pos_left hlog (hq_pos i)
  have hratio : q i / p i = (p i / q i)⁻¹ := by
    field_simp [ne_of_gt (hq_pos i), ne_of_gt (hp_pos i)]
  have hleft : q i * Real.log (q i / p i) =
      -(q i * Real.log (p i / q i)) := by
    rw [hratio, Real.log_inv]
    ring
  have hright : q i * (p i / q i - 1) = p i - q i := by
    field_simp [ne_of_gt (hq_pos i)]
  rw [hright] at hmul
  linarith

theorem finiteRelativeEntropy_eq_zero_iff
    (q p : Data → ℝ)
    (hq_pos : ∀ i, 0 < q i)
    (hp_pos : ∀ i, 0 < p i)
    (hq_sum : ∑ i : Data, q i = 1)
    (hp_sum : ∑ i : Data, p i = 1) :
    finiteRelativeEntropy q p = 0 ↔ q = p := by
  constructor
  · intro hzero
    funext i
    by_contra hneq
    have hgap_pos := relativeEntropyGap_pos_of_ne q p hq_pos hp_pos hneq
    have hgap_nonneg : ∀ j, 0 ≤ relativeEntropyGap q p j :=
      fun j => relativeEntropyGap_nonneg q p hq_pos hp_pos j
    have hsum_gap_pos : 0 < ∑ j : Data, relativeEntropyGap q p j := by
      exact Finset.sum_pos' (fun j _ => hgap_nonneg j)
        ⟨i, Finset.mem_univ i, hgap_pos⟩
    have hsum_gap_eq :
        ∑ j : Data, relativeEntropyGap q p j = finiteRelativeEntropy q p := by
      unfold relativeEntropyGap finiteRelativeEntropy
      rw [Finset.sum_sub_distrib]
      rw [Finset.sum_sub_distrib, hq_sum, hp_sum]
      norm_num
    linarith
  · intro hqp
    subst p
    simp [finiteRelativeEntropy]

end InfoGeometry.Inference
