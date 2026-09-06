import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Spectral.RiemannVonMangoldtStaircase

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def smoothZeroStaircase (E : ℝ) : ℝ :=
  (E / (2 * Real.pi)) * Real.log (E / (2 * Real.pi * Real.exp 1)) + 7 / 8

theorem smooth_staircase_deriv (E : ℝ) (hE : 0 < E) :
    HasDerivAt smoothZeroStaircase ((1 / (2 * Real.pi)) * Real.log (E / (2 * Real.pi))) E := by
  unfold smoothZeroStaircase
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_den_pos : 0 < 2 * Real.pi * Real.exp 1 := by positivity
  have h_c : HasDerivAt (fun x : ℝ => x / (2 * Real.pi * Real.exp 1)) (1 / (2 * Real.pi * Real.exp 1)) E := by
    simpa only [one_mul] using (hasDerivAt_id E).div_const (2 * Real.pi * Real.exp 1)
  have h_log_inner := HasDerivAt.log h_c (ne_of_gt (div_pos hE h_den_pos))
  have h_frac : (1 / (2 * Real.pi * Real.exp 1)) / (E / (2 * Real.pi * Real.exp 1)) = 1 / E := by
    field_simp [ne_of_gt h_den_pos, ne_of_gt hE]
  rw [h_frac] at h_log_inner
  have h_linear : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) (1 / (2 * Real.pi)) E := by
    simpa only [one_mul] using (hasDerivAt_id E).div_const (2 * Real.pi)
  have h_full_prod := HasDerivAt.mul h_linear h_log_inner
  have h_full_add := HasDerivAt.add_const (7 / 8) h_full_prod
  have h_prod_div : (E / (2 * Real.pi)) * (1 / E) = 1 / (2 * Real.pi) := by
    field_simp [ne_of_gt hE, ne_of_gt h_pi_pos]
  have h_log_split : Real.log (E / (2 * Real.pi * Real.exp 1)) =
                     Real.log (E / (2 * Real.pi)) - 1 := by
    have h_rew : E / (2 * Real.pi * Real.exp 1) = (E / (2 * Real.pi)) / Real.exp 1 := by ring
    rw [h_rew, Real.log_div (by positivity) (ne_of_gt (Real.exp_pos 1)), Real.log_exp]
  have h_alg : (1 / (2 * Real.pi)) * Real.log (E / (2 * Real.pi * Real.exp 1)) +
               (E / (2 * Real.pi)) * (1 / E) =
               (1 / (2 * Real.pi)) * Real.log (E / (2 * Real.pi)) := by
    rw [h_prod_div, h_log_split]
    ring
  rw [h_alg] at h_full_add
  exact h_full_add
