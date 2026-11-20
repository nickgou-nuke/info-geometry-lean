/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Spectrometry.GlobalHyperbolicBounds
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
# The exact finite two-line balancing root

Checked with Lean 4.34.1 and Mathlib commit d13f23b. The companion
`GlobalHyperbolicBounds.lean` must be on the import path. The sum score and the
mean score have exactly the same zeros for a finite nonempty column type.

Existence, global uniqueness, and the bracket require only a uniform bound on
the supplied `z`; mean zero is needed only for the cubic residual estimate at
zero. These statements do not assume that a numerical iteration converged.
-/

namespace InfoGeometry.Spectrometry.ExactTwoLineRoot

open Set
open scoped BigOperators
open GlobalHyperbolicBounds

noncomputable section

variable {J : Type*} [Fintype J] [Nonempty J]

def score (z : J → ℝ) (delta : ℝ) : ℝ :=
  ∑ j, Real.tanh (z j - delta / 2)

def meanScore (z : J → ℝ) (delta : ℝ) : ℝ :=
  score z delta / (Fintype.card J : ℝ)

def scoreDerivative (z : J → ℝ) (delta : ℝ) : ℝ :=
  ∑ j, -(1 / Real.cosh (z j - delta / 2) ^ 2) / 2

omit [Nonempty J] in
theorem hasDerivAt_score (z : J → ℝ) (delta : ℝ) :
    HasDerivAt (score z) (scoreDerivative z delta) delta := by
  have hterm (j : J) :
      HasDerivAt (fun t => Real.tanh (z j - t / 2))
        (-(1 / Real.cosh (z j - delta / 2) ^ 2) / 2) delta := by
    convert (hasDerivAt_tanh_sech (z j - delta / 2)).comp delta
      ((hasDerivAt_const delta (z j)).sub ((hasDerivAt_id delta).div_const 2))
      using 1 <;> first | (funext t; rfl) | ring
  exact HasDerivAt.fun_sum (fun j _ => hterm j)

omit [Nonempty J] in
theorem continuous_score (z : J → ℝ) : Continuous (score z) :=
  (show Differentiable ℝ (score z) from
    fun delta => (hasDerivAt_score z delta).differentiableAt).continuous

theorem strictAnti_score (z : J → ℝ) : StrictAnti (score z) := by
  intro a b hab
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro j _
  apply strictMono_tanh
  linarith

theorem meanScore_zero_iff (z : J → ℝ) (delta : ℝ) :
    meanScore z delta = 0 ↔ score z delta = 0 := by
  have hcard : (Fintype.card J : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card J ≠ 0)
  simp only [meanScore, div_eq_zero_iff, hcard, or_false]

omit [Nonempty J] in
theorem score_left_nonneg (z : J → ℝ) (M : ℝ)
    (hbound : ∀ j, |z j| ≤ M) : 0 ≤ score z (-2 * M) := by
  apply Finset.sum_nonneg
  intro j _
  apply tanh_nonneg
  have hj := (abs_le.mp (hbound j)).1
  linarith

omit [Nonempty J] in
theorem score_right_nonpos (z : J → ℝ) (M : ℝ)
    (hbound : ∀ j, |z j| ≤ M) : score z (2 * M) ≤ 0 := by
  apply Finset.sum_nonpos
  intro j _
  apply tanh_nonpos
  have hj := (abs_le.mp (hbound j)).2
  linarith

omit [Nonempty J] in
theorem exists_root_bracket (z : J → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |z j| ≤ M) :
    ∃ delta : ℝ, |delta| ≤ 2 * M ∧ score z delta = 0 := by
  have hvalues : (0 : ℝ) ∈ Icc (score z (2 * M)) (score z (-2 * M)) :=
    ⟨score_right_nonpos z M hbound, score_left_nonneg z M hbound⟩
  obtain ⟨delta, hdelta, hzero⟩ :=
    intermediate_value_Icc' (show -2 * M ≤ 2 * M by linarith only [hM])
      (continuous_score z).continuousOn hvalues
  refine ⟨delta, ?_, hzero⟩
  apply abs_le.mpr
  constructor <;> linarith [hdelta.1, hdelta.2]

/-- Uniqueness is on the entire real line, not merely inside the bracket. -/
theorem exists_unique_root (z : J → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |z j| ≤ M) : ∃! delta : ℝ, score z delta = 0 := by
  obtain ⟨delta, _, hzero⟩ := exists_root_bracket z M hM hbound
  refine ⟨delta, hzero, ?_⟩
  intro eta heta
  exact (strictAnti_score z).injective (heta.trans hzero.symm)

theorem root_abs_le (z : J → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |z j| ≤ M) (delta : ℝ) (hzero : score z delta = 0) :
    |delta| ≤ 2 * M := by
  obtain ⟨eta, heta, heq⟩ := exists_root_bracket z M hM hbound
  have hsame : delta = eta := (strictAnti_score z).injective (hzero.trans heq.symm)
  simpa only [hsame] using heta

theorem exists_unique_mean_root (z : J → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, |z j| ≤ M) : ∃! delta : ℝ, meanScore z delta = 0 := by
  simpa only [meanScore_zero_iff] using exists_unique_root z M hM hbound

omit [Nonempty J] in
/-- Centering turns the residual at zero into a sum of cubic remainders. -/
theorem abs_score_zero_le_cubic (z : J → ℝ) (hcenter : ∑ j, z j = 0) :
    |score z 0| ≤ (∑ j, |z j| ^ 3) / 3 := by
  have hscore : score z 0 = ∑ j, (Real.tanh (z j) - z j) := by
    simp only [score, zero_div, sub_zero, Finset.sum_sub_distrib, hcenter]
  rw [hscore]
  calc
    |∑ j, (Real.tanh (z j) - z j)| ≤
        ∑ j, |Real.tanh (z j) - z j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |z j| ^ 3 / 3 := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_sub_comm]
      exact abs_sub_tanh_le_cube (z j)
    _ = (∑ j, |z j| ^ 3) / 3 := by rw [Finset.sum_div]

end
end InfoGeometry.Spectrometry.ExactTwoLineRoot
