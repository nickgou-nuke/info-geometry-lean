import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Topological.ChernSimonsCochain

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def chernSimonsLevel (k : ℤ) : ℤ := k

def wilsonLoopTrace (γ : ℝ) (p : ℝ) : ℝ :=
  2 * Real.cosh ((γ * Real.log p) / 2)

theorem large_gauge_exp_integer (k w : ℤ) :
    Complex.exp (((k * w : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
  exact Complex.exp_int_mul_two_pi_mul_I (k * w)

theorem wilson_loop_lower_bound (γ : ℝ) (p : ℝ) (hp : 0 < p) :
    2 ≤ wilsonLoopTrace γ p := by
  unfold wilsonLoopTrace
  have h_cosh := Real.cosh_eq ((γ * Real.log p) / 2)
  have h_exp_pos : 0 < Real.exp ((γ * Real.log p) / 2) := Real.exp_pos _
  have h_sq : 0 ≤ (Real.exp ((γ * Real.log p) / 2) - 1) ^ 2 := sq_nonneg _
  have h_inv : Real.exp (- ((γ * Real.log p) / 2)) = 1 / Real.exp ((γ * Real.log p) / 2) := by
    rw [Real.exp_neg, one_div]
  have h_am_gm : 2 ≤ Real.exp ((γ * Real.log p) / 2) + 1 / Real.exp ((γ * Real.log p) / 2) := by
    have h_diff : Real.exp ((γ * Real.log p) / 2) + 1 / Real.exp ((γ * Real.log p) / 2) - 2 =
                  (Real.exp ((γ * Real.log p) / 2) - 1) ^ 2 / Real.exp ((γ * Real.log p) / 2) := by
      field_simp
      ring
    have h_div_nonneg : 0 ≤ (Real.exp ((γ * Real.log p) / 2) - 1) ^ 2 / Real.exp ((γ * Real.log p) / 2) :=
      div_nonneg h_sq (le_of_lt h_exp_pos)
    linarith
  have h_sum : 2 ≤ Real.exp ((γ * Real.log p) / 2) + Real.exp (- ((γ * Real.log p) / 2)) := by
    rw [h_inv]
    exact h_am_gm
  linarith
