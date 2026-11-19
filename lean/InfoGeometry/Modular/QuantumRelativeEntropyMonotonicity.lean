/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite Probability Relative Entropy and Assumed Entropy Decay

This module defines classical relative entropy on strictly positive finite
probability distributions and proves its nonnegativity. Its `SemigroupTrajectory`
structure assumes an entropy-decay equation; the monotonicity lemma derives the
corresponding scalar inequality from that field. It does not construct a
quantum channel or prove monotonicity for noncommutative density operators.
-/

noncomputable section

open BigOperators
open Finset

namespace InfoGeometry.Modular.RelativeEntropy

variable {n : Type*} [Fintype n]

/-- Strictly positive finite probability distribution. -/
structure StateDist (n : Type*) [Fintype n] where
  prob : n → ℝ
  pos : ∀ i, 0 < prob i
  normalized : ∑ i, prob i = 1

/-- 
  The Relative Entropy / Kullback–Leibler Divergence:
  S(p ∥ q) = ∑_i p_i (Real.log (p_i) - Real.log (q_i)).
-/
def relEntropy (p q : StateDist n) : ℝ :=
  ∑ i, p.prob i * (Real.log (p.prob i) - Real.log (q.prob i))

/-- THEOREM 1: Relative Entropy of Identical States is Identically Zero: S(p ∥ p) = 0. -/
@[simp]
theorem relEntropy_self (p : StateDist n) :
    relEntropy p p = 0 := by
  dsimp [relEntropy]
  have h_zero (i : n) : p.prob i * (Real.log (p.prob i) - Real.log (p.prob i)) = 0 := by
    rw [sub_self, mul_zero]
  simp only [h_zero, sum_const_zero]

/-- 
  Fundamental inequality for the logarithm: log x ≤ x - 1 for all x > 0,
  or equivalently: 1 - 1/u ≤ log u.
  For u = p/q: p log(p/q) ≥ p - q.
-/
lemma log_ratio_ge_sub (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    p * (Real.log p - Real.log q) ≥ p - q := by
  have h_div : Real.log p - Real.log q = Real.log (p / q) := by
    exact (Real.log_div hp.ne' hq.ne').symm
  rw [h_div]
  have h_log_le := Real.log_le_sub_one_of_pos (div_pos hq hp)
  have h_neg_log : Real.log (p / q) = - Real.log (q / p) := by
    rw [← Real.log_inv, inv_div]
  rw [h_neg_log]
  have h_bound : - (q / p - 1) ≤ - Real.log (q / p) := neg_le_neg h_log_le
  have h_mult : p * (- (q / p - 1)) ≤ p * (- Real.log (q / p)) := by
    exact mul_le_mul_of_nonneg_left h_bound hp.le
  have h_simpl : p * (- (q / p - 1)) = p - q := by
    calc
      p * (- (q / p - 1)) = p * (1 - q / p) := by ring
      _ = p * 1 - p * (q / p) := mul_sub p 1 (q / p)
      _ = p - q := by rw [mul_one, mul_div_cancel₀ q hp.ne']
  rw [h_simpl] at h_mult
  exact h_mult

/-- Nonnegativity of classical relative entropy for strictly positive finite
probability distributions. -/
theorem relEntropy_nonneg (p q : StateDist n) :
    0 ≤ relEntropy p q := by
  dsimp [relEntropy]
  have h_sum_ge : (∑ i, p.prob i * (Real.log (p.prob i) - Real.log (q.prob i))) ≥
      ∑ i, (p.prob i - q.prob i) := by
    apply Finset.sum_le_sum
    intro i _
    exact log_ratio_ge_sub (p.prob i) (q.prob i) (p.pos i) (q.pos i)
  have h_diff_sum : (∑ i, (p.prob i - q.prob i)) = 0 := by
    rw [sum_sub_distrib, p.normalized, q.normalized, sub_self]
  linarith

/-!
=============================================================================
PART 2: Entropy Production and Monotonic Decay along the Dynamical Flow
=============================================================================
-/

/-- A finite probability trajectory together with an assumed scalar entropy
decay law and nonnegative production rate. No operator semigroup is constructed
by this data structure. -/
structure SemigroupTrajectory (n : Type*) [Fintype n] where
  state : ℝ → StateDist n
  inv_state : StateDist n
  entropy_prod : ℝ → ℝ
  prod_nonneg : ∀ t ≥ 0, 0 ≤ entropy_prod t
  relEntropy_decay : ∀ t ≥ 0, ∀ s ≥ 0,
    relEntropy (state (t + s)) inv_state = relEntropy (state t) inv_state - s * entropy_prod t

/-- The assumed decay law implies monotonicity of the finite-distribution
relative entropy along the supplied trajectory. -/
theorem relEntropy_monotonic (traj : SemigroupTrajectory n) (t : ℝ) (ht : 0 ≤ t) (s : ℝ) (hs : 0 ≤ s) :
    relEntropy (traj.state (t + s)) traj.inv_state ≤ relEntropy (traj.state t) traj.inv_state := by
  have h_decay := traj.relEntropy_decay t ht s hs
  have h_prod := traj.prod_nonneg t ht
  have h_nonneg_term : 0 ≤ s * traj.entropy_prod t := mul_nonneg hs h_prod
  linarith

/-- Finite-time contraction from the initial distribution, under the trajectory's
assumed decay law. -/
theorem relEntropy_finite_time_contraction (traj : SemigroupTrajectory n) (t : ℝ) (ht : 0 ≤ t) :
    relEntropy (traj.state t) traj.inv_state ≤ relEntropy (traj.state 0) traj.inv_state := by
  have h := relEntropy_monotonic traj 0 (le_refl 0) t ht
  simpa using h

end InfoGeometry.Modular.RelativeEntropy

end noncomputable section
