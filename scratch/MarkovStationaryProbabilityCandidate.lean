/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

/-!
# Candidate: stationary probability vectors for positive finite Markov matrices

This scratch file attempts an entirely finite-dimensional existence proof.
It first extracts a nonzero left fixed vector from singularity of `1 - P`,
then uses absolute values and equality in the finite triangle inequality to
produce a nonnegative stationary vector, which is normalized by its positive
total mass.
-/

open scoped BigOperators
open Matrix

namespace MarkovStationaryProbabilityCandidate

theorem exists_stationary_probability
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (hpos : ∀ i j, 0 < P i j) :
    ∃ π : ι → ℝ,
      (∀ i, 0 ≤ π i) ∧
      (∑ i, π i = 1) ∧
      (∀ j, ∑ i, π i * P i j = π j) := by
  classical
  have hone_ne : (1 : ι → ℝ) ≠ 0 := by
    intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := congrFun h i
    norm_num at this
  have hone_fix : P *ᵥ (1 : ι → ℝ) = 1 :=
    (Matrix.mem_rowStochastic.mp hP).2
  have hLone : (1 - P) *ᵥ (1 : ι → ℝ) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hone_fix, sub_self]
  have hdet : (1 - P).det = 0 :=
    (Matrix.exists_mulVec_eq_zero_iff).mp ⟨1, hone_ne, hLone⟩
  obtain ⟨v, hvne, hvL⟩ := (Matrix.exists_vecMul_eq_zero_iff).mpr hdet
  have hvstat : v ᵥ* P = v := by
    have hsub := Matrix.vecMul_sub 1 P v
    rw [Matrix.vecMul_one] at hsub
    rw [hsub] at hvL
    have : v - v ᵥ* P = 0 := hvL
    exact (sub_eq_zero.mp this).symm

  let w : ι → ℝ := fun i => |v i|
  have hdom (j : ι) : |v j| ≤ ∑ i, |v i| * P i j := by
    have hj : v j = ∑ i, v i * P i j := by
      have := congrFun hvstat j
      simpa [Matrix.vecMul, dotProduct] using this.symm
    rw [hj]
    calc
      |∑ i, v i * P i j| ≤ ∑ i, |v i * P i j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |v i| * P i j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_pos (hpos i j)]
  have hRhs : (∑ j, ∑ i, |v i| * P i j) = ∑ i, |v i| := by
    rw [Finset.sum_comm]
    calc
      (∑ i, ∑ j, |v i| * P i j) = ∑ i, |v i| * (∑ j, P i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = ∑ i, |v i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Matrix.sum_row_of_mem_rowStochastic hP i, mul_one]
  have hdomSum : (∑ j, |v j|) = ∑ j, ∑ i, |v i| * P i j := by
    apply le_antisymm
    · exact Finset.sum_le_sum fun j hj => hdom j
    · rw [hRhs]
  have hdomEq : ∀ j, |v j| = ∑ i, |v i| * P i j := by
    intro j
    have hnonneg (k : ι) : 0 ≤ (∑ i, |v i| * P i k) - |v k| := sub_nonneg.mpr (hdom k)
    have hsumzero : ∑ k, ((∑ i, |v i| * P i k) - |v k|) = 0 := by
      rw [Finset.sum_sub_distrib, ← hdomSum]
      simp
    have hterm : (∑ i, |v i| * P i j) - |v j| = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => hnonneg k)).mp hsumzero j
      simp
    linarith
  have hwstationary (j : ι) : ∑ i, w i * P i j = w j := by
    exact (hdomEq j).symm
  have hw_nonneg (i : ι) : 0 ≤ w i := abs_nonneg _
  have hw_sum_pos : 0 < ∑ i, w i := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hvne (funext h)
    have hiabs : 0 < w i := abs_pos.mpr hi
    have hsum : w i ≤ ∑ k, w k := Finset.single_le_sum (fun k hk => hw_nonneg k) (Finset.mem_univ i)
    exact lt_of_lt_of_le hiabs hsum
  let c : ℝ := (∑ i, w i)⁻¹
  refine ⟨fun i => c * w i, ?_, ?_, ?_⟩
  · intro i
    exact mul_nonneg (le_of_lt (inv_pos.mpr hw_sum_pos)) (hw_nonneg i)
  · calc
      (∑ i, c * w i) = c * (∑ i, w i) := by rw [Finset.mul_sum]
      _ = 1 := by dsimp [c]; exact inv_mul_cancel₀ hw_sum_pos.ne'
  · intro j
    calc
      (∑ i, c * w i * P i j) = c * (∑ i, w i * P i j) := by
        simp_rw [mul_assoc]
        rw [Finset.mul_sum]
      _ = c * w j := by rw [hwstationary j]

end MarkovStationaryProbabilityCandidate

#print axioms MarkovStationaryProbabilityCandidate.exists_stationary_probability
