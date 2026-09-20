import InfoGeometry.Synthesis.ImpedanceMatchingDuality
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section

namespace InfoGeometry.Synthesis.QuadraticContactDerivatives

open ImpedanceMatchingDuality

theorem capacity_hasDerivAt (coupling efficiency : ℝ) :
    HasDerivAt (fisher_capacity coupling)
      (coupling - 2 * coupling ^ 2 * efficiency) efficiency := by
  convert ((((hasDerivAt_id efficiency).const_mul coupling).sub_const (1 / 2)).pow 2).const_sub
    (1 / 4) using 1
  · ext value
    exact capacity_vertex coupling value
  · dsimp
    ring

theorem criticalValue_hasDerivAt (momentum : ℝ) :
    HasDerivAt criticalValue (2 * momentum) momentum := by
  convert ((hasDerivAt_id momentum).pow 2).const_add (1 / 4) using 1
  · ext value
    exact criticalValue_formula value
  · dsimp
    ring

theorem capacity_deriv (coupling efficiency : ℝ) :
    deriv (fisher_capacity coupling) efficiency = coupling - 2 * coupling ^ 2 * efficiency :=
  (capacity_hasDerivAt coupling efficiency).deriv

theorem criticalValue_deriv (momentum : ℝ) : deriv criticalValue momentum = 2 * momentum :=
  (criticalValue_hasDerivAt momentum).deriv

theorem capacity_second_deriv (coupling efficiency : ℝ) :
    deriv (deriv (fisher_capacity coupling)) efficiency = -2 * coupling ^ 2 := by
  have hderiv : HasDerivAt (fun value : ℝ => coupling - 2 * coupling ^ 2 * value)
      (-2 * coupling ^ 2) efficiency := by
    convert ((hasDerivAt_id efficiency).const_mul (2 * coupling ^ 2)).const_sub coupling using 1
    ring
  simpa only [funext (capacity_deriv coupling)] using hderiv.deriv

theorem criticalValue_second_deriv (momentum : ℝ) :
    deriv (deriv criticalValue) momentum = 2 := by
  simpa only [funext criticalValue_deriv, mul_one] using
    ((hasDerivAt_id momentum).const_mul 2).deriv

theorem stationary_capacity_iff (coupling efficiency : ℝ) (hnonzero : coupling ≠ 0) :
    deriv (fisher_capacity coupling) efficiency = 0 ↔ efficiency = 1 / (2 * coupling) := by
  rw [capacity_deriv]
  constructor
  · intro hzero
    have hfactor : coupling * (1 - 2 * coupling * efficiency) = 0 := by nlinarith [hzero]
    have hlinear := (mul_eq_zero.mp hfactor).resolve_left hnonzero
    apply (eq_div_iff (mul_ne_zero (by norm_num) hnonzero)).mpr
    nlinarith
  · rintro rfl
    field_simp
    ring

theorem stationary_criticalValue_iff (momentum : ℝ) :
    deriv criticalValue momentum = 0 ↔ momentum = 0 := by
  rw [criticalValue_deriv]
  exact mul_eq_zero.trans (or_iff_right (by norm_num))

def action (coupling efficiency momentum : ℝ) : ℝ :=
  criticalValue momentum - fisher_capacity coupling efficiency

theorem action_efficiency_hasDerivAt (coupling efficiency momentum : ℝ) :
    HasDerivAt (fun value => action coupling value momentum)
      (2 * coupling ^ 2 * efficiency - coupling) efficiency := by
  convert (capacity_hasDerivAt coupling efficiency).const_sub (criticalValue momentum) using 1
  ring

theorem action_momentum_hasDerivAt (coupling efficiency momentum : ℝ) :
    HasDerivAt (action coupling efficiency) (2 * momentum) momentum :=
  (criticalValue_hasDerivAt momentum).sub_const (fisher_capacity coupling efficiency)

theorem action_zero_iff (coupling efficiency momentum : ℝ) (hnonzero : coupling ≠ 0) :
    action coupling efficiency momentum = 0 ↔
      efficiency = 1 / (2 * coupling) ∧ momentum = 0 := by
  rw [action, sub_eq_zero, eq_comm]
  exact unique_contact_point coupling efficiency momentum hnonzero

theorem action_strict_minimum (coupling efficiency momentum : ℝ) (hnonzero : coupling ≠ 0)
    (haway : ¬ (efficiency = 1 / (2 * coupling) ∧ momentum = 0)) :
    0 < action coupling efficiency momentum := by
  have hnonnegative := pointwise_gap_nonnegative coupling efficiency momentum
  have hne : action coupling efficiency momentum ≠ 0 := by
    intro hequal
    exact haway ((action_zero_iff coupling efficiency momentum hnonzero).mp hequal)
  exact lt_of_le_of_ne hnonnegative hne.symm

theorem action_exact_increment (coupling efficiency momentum deltaEfficiency deltaMomentum : ℝ) :
    action coupling (efficiency + deltaEfficiency) (momentum + deltaMomentum) =
      action coupling efficiency momentum +
      (2 * coupling ^ 2 * efficiency - coupling) * deltaEfficiency +
      (2 * momentum) * deltaMomentum +
      coupling ^ 2 * deltaEfficiency ^ 2 + deltaMomentum ^ 2 := by
  simp only [action, pointwise_gap]
  ring

theorem action_second_variation_positive (coupling deltaEfficiency deltaMomentum : ℝ)
    (hnonzero : coupling ≠ 0) (hdirection : deltaEfficiency ≠ 0 ∨ deltaMomentum ≠ 0) :
    0 < 2 * coupling ^ 2 * deltaEfficiency ^ 2 + 2 * deltaMomentum ^ 2 := by
  rcases hdirection with hfirst | hsecond
  · have hpositive := mul_pos (sq_pos_of_ne_zero hnonzero) (sq_pos_of_ne_zero hfirst)
    nlinarith [sq_nonneg deltaMomentum]
  · have hpositive := sq_pos_of_ne_zero hsecond
    have hnonnegative := mul_nonneg (sq_nonneg coupling) (sq_nonneg deltaEfficiency)
    nlinarith

end InfoGeometry.Synthesis.QuadraticContactDerivatives
