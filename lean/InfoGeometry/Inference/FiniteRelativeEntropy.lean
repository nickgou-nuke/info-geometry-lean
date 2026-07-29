/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite relative entropy

This is the finite positive-distribution KL functional used by the Gibbs
variational layer. The hypotheses exclude zero-probability boundary terms so
the logarithmic expression remains an ordinary real-valued formula.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Data : Type*} [Fintype Data]

noncomputable def finiteRelativeEntropy
    (q p : Data → ℝ) : ℝ :=
  ∑ i : Data, (q i * Real.log (q i / p i))

theorem finiteRelativeEntropy_nonneg
    (q p : Data → ℝ)
    (hq_pos : ∀ i, 0 < q i)
    (hp_pos : ∀ i, 0 < p i)
    (hq_sum : ∑ i : Data, q i = 1)
    (hp_sum : ∑ i : Data, p i = 1) :
    0 ≤ finiteRelativeEntropy q p := by
  unfold finiteRelativeEntropy
  have hpoint : ∀ i : Data,
      q i - p i ≤ q i * Real.log (q i / p i) := by
    intro i
    have hlog : Real.log (p i / q i) ≤ p i / q i - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hp_pos i) (hq_pos i))
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
  have hsum :
      (Finset.univ.sum (fun i : Data => (q i - p i))) ≤
        Finset.univ.sum (fun i : Data => (q i * Real.log (q i / p i))) := by
    exact Finset.sum_le_sum (fun i hi => hpoint i)
  calc
    0 = Finset.univ.sum (fun i : Data => q i - p i) := by
      rw [Finset.sum_sub_distrib, hq_sum, hp_sum]
      norm_num
    _ ≤ ∑ i : Data, (q i * Real.log (q i / p i)) := hsum

end InfoGeometry.Inference
