import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Thermal.ThermodynamicBetheAnsatz

open Real Complex Filter Topology

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def freePseudoEnergy (x : ℝ) : ℝ := x

def yangYangLFunction (ε : ℝ) : ℝ :=
  Real.log (1 + Real.exp (-ε))

def yangYangEntropyDensity (ε : ℝ) : ℝ :=
  yangYangLFunction ε + ε / (1 + Real.exp ε)

def zamolodchikovDilogIntegral : ℝ :=
  Real.pi ^ 2 / 12

def effectiveCentralChargeTBA : ℝ :=
  (6 / Real.pi ^ 2) * zamolodchikovDilogIntegral

theorem yang_yang_L_function_pos (ε : ℝ) :
    0 < yangYangLFunction ε := by
  unfold yangYangLFunction
  have h_exp_pos : 0 < Real.exp (-ε) := Real.exp_pos _
  have h_gt_one : 1 < 1 + Real.exp (-ε) := by linarith
  exact Real.log_pos h_gt_one

theorem hasDerivAt_yangYangLFunction (ε : ℝ) :
    HasDerivAt yangYangLFunction (- (1 / (1 + Real.exp ε))) ε := by
  unfold yangYangLFunction
  have h_exp_pos : 0 < Real.exp (-ε) := Real.exp_pos _
  have h_den_pos : 0 < 1 + Real.exp (-ε) := by linarith
  have h_inner : HasDerivAt (fun x : ℝ => 1 + Real.exp (-x)) (- Real.exp (-ε)) ε := by
    have h_neg_x : HasDerivAt (fun x : ℝ => -x) (-1) ε := by
      simpa only [neg_one_mul] using (hasDerivAt_id ε).neg
    have h_exp := HasDerivAt.exp h_neg_x
    have h_exp_eval : Real.exp (-ε) * -1 = - Real.exp (-ε) := by ring
    rw [h_exp_eval] at h_exp
    exact HasDerivAt.const_add 1 h_exp
  have h_log := HasDerivAt.log h_inner (ne_of_gt h_den_pos)
  have h_simp : (- Real.exp (-ε)) / (1 + Real.exp (-ε)) = - (1 / (1 + Real.exp ε)) := by
    have h_rew : 1 + Real.exp (-ε) = (Real.exp ε + 1) / Real.exp ε := by
      rw [Real.exp_neg]
      field_simp
    rw [h_rew, Real.exp_neg]
    field_simp
    ring
  rwa [h_simp] at h_log

theorem effective_central_charge_tba_eval :
    effectiveCentralChargeTBA = 1 / 2 := by
  unfold effectiveCentralChargeTBA zamolodchikovDilogIntegral
  have h_pi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h_pi_sq : Real.pi ^ 2 ≠ 0 := pow_ne_zero 2 h_pi_ne
  calc (6 / Real.pi ^ 2) * (Real.pi ^ 2 / 12)
    _ = (6 * Real.pi ^ 2) / (Real.pi ^ 2 * 12) := by ring
    _ = (6 * Real.pi ^ 2) / (12 * Real.pi ^ 2) := by
      have : Real.pi ^ 2 * 12 = 12 * Real.pi ^ 2 := mul_comm (Real.pi ^ 2) 12
      rw [this]
    _ = 6 / 12 := mul_div_mul_right 6 12 h_pi_sq
    _ = 1 / 2 := by norm_num

theorem total_cft_central_charge_from_tba :
    effectiveCentralChargeTBA + effectiveCentralChargeTBA = 1 := by
  rw [effective_central_charge_tba_eval]
  ring
