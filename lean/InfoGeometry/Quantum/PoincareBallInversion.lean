import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.PoincareBallInversion

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def poincareInversion (r : ℝ) : ℝ :=
  1 / r

def rapidityScale (r : ℝ) : ℝ :=
  Real.log r

theorem poincare_inversion_involution (r : ℝ) (hr : r ≠ 0) :
    poincareInversion (poincareInversion r) = r := by
  unfold poincareInversion
  exact one_div_one_div r

theorem poincare_inversion_rapidity_neg (r : ℝ) (hr : 0 < r) :
    rapidityScale (poincareInversion r) = - rapidityScale r := by
  unfold rapidityScale poincareInversion
  rw [Real.log_div (by positivity) (ne_of_gt hr), Real.log_one, zero_sub]

theorem poincare_equator_fixed_point :
    poincareInversion 1 = 1 := by
  unfold poincareInversion
  norm_num

theorem poincare_inversion_fixed_iff (r : ℝ) (hr : 0 < r) :
    poincareInversion r = r ↔ r = 1 := by
  unfold poincareInversion
  constructor
  · intro h
    have h_mul : (1 / r) * r = r * r := by rw [h]
    rw [one_div_mul_cancel (ne_of_gt hr)] at h_mul
    have h_sq : r ^ 2 = 1 := by
      calc r ^ 2 = r * r := sq r
        _ = 1 := h_mul.symm
    have h_pos : 0 ≤ r := le_of_lt hr
    have h_sqrt := Real.sqrt_sq h_pos
    rw [h_sq, Real.sqrt_one] at h_sqrt
    exact h_sqrt.symm
  · intro h
    rw [h, one_div_one]

theorem poincare_inner_outer_critical_line (σ : ℝ) (h_inv : poincareInversion (Real.exp (σ - 1/2)) = Real.exp (σ - 1/2)) :
    σ = 1 / 2 := by
  have h_exp_pos : 0 < Real.exp (σ - 1/2) := Real.exp_pos _
  have h_eq_one := (poincare_inversion_fixed_iff (Real.exp (σ - 1/2)) h_exp_pos).mp h_inv
  have h_log := congr_arg Real.log h_eq_one
  rw [Real.log_exp, Real.log_one] at h_log
  linarith
