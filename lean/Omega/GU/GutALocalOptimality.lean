/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic

namespace Omega.GU

open scoped BigOperators

/-- Finite-family version of membership of zero in the convex hull of active channel slopes. -/
def gut_a_local_optimality_zero_in_finite_convex_hull {ι : Type*} [Fintype ι]
    (slope : ι → ℝ) : Prop :=
  ∃ α : ι → ℝ,
    (∀ i, 0 ≤ α i) ∧
      (∑ i, α i = 1) ∧
        ∑ i, α i * slope i = 0

/- A normalized nonnegative weighting with zero weighted slope forces the active
slopes to bracket zero. This is a geometric consequence of the finite KKT witness,
not a renaming of that witness. -/
theorem gut_a_local_optimality_weights_force_slope_bracketing
    {ι : Type*} [Fintype ι] (slope : ι → ℝ)
    (hweights : gut_a_local_optimality_zero_in_finite_convex_hull slope) :
    (∃ i, slope i ≤ 0) ∧ (∃ j, 0 ≤ slope j) := by
  rcases hweights with ⟨α, hα, hmass, hmoment⟩
  have hαpos : ∃ i, 0 < α i := by
    by_contra h
    push Not at h
    have hneg : 0 ≤ ∑ i : ι, -α i :=
      Finset.sum_nonneg fun i _ => neg_nonneg.mpr (h i)
    have hneg' : 0 ≤ -(∑ i : ι, α i) := by simpa using hneg
    rw [hmass] at hneg'
    norm_num at hneg'
  obtain ⟨i₀, hi₀⟩ := hαpos
  constructor
  · by_contra h
    push Not at h
    have hterm_nonneg : ∀ i ∈ (Finset.univ : Finset ι),
        0 ≤ α i * slope i := fun i _ => mul_nonneg (hα i) (le_of_lt (h i))
    have hterm_pos : ∃ i ∈ (Finset.univ : Finset ι),
        0 < α i * slope i :=
      ⟨i₀, Finset.mem_univ _, mul_pos hi₀ (h i₀)⟩
    have hsum_pos : 0 < ∑ i : ι, α i * slope i :=
      Finset.sum_pos' hterm_nonneg hterm_pos
    linarith
  · by_contra h
    push Not at h
    have hterm_nonneg : ∀ i ∈ (Finset.univ : Finset ι),
        0 ≤ α i * (-slope i) := fun i _ =>
          mul_nonneg (hα i) (neg_nonneg.mpr (le_of_lt (h i)))
    have hterm_pos : ∃ i ∈ (Finset.univ : Finset ι),
        0 < α i * (-slope i) :=
      ⟨i₀, Finset.mem_univ _, mul_pos hi₀ (neg_pos.mpr (h i₀))⟩
    have hsum_pos : 0 < ∑ i : ι, α i * (-slope i) :=
      Finset.sum_pos' hterm_nonneg hterm_pos
    have hsum_neg : (∑ i : ι, α i * (-slope i)) = 0 := by
      calc
        (∑ i : ι, α i * (-slope i)) = ∑ i : ι, -(α i * slope i) := by
          congr 1
          funext i
          ring
        _ = -(∑ i : ι, α i * slope i) := by simp only [Finset.sum_neg_distrib]
        _ = 0 := by rw [hmoment]; simp
    linarith

end Omega.GU
