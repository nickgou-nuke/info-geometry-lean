import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.CFT.VirasoroVOAZeta

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def virasoroCentralCharge : ℝ := 1

def primaryConformalWeight (alpha : ℝ) : ℝ :=
  (alpha ^ 2) / 2

def zetaPoleParameter : ℝ := 1

theorem c_equals_one : virasoroCentralCharge = 1 := rfl

theorem primary_weight_pos (p : ℝ) (hp : 2 ≤ p) :
    0 < primaryConformalWeight (Real.log p) := by
  unfold primaryConformalWeight
  have h_ln_pos : 0 < Real.log p := by
    have : 1 < p := by linarith
    exact Real.log_pos this
  have h_sq : 0 < (Real.log p) ^ 2 := sq_pos_of_pos h_ln_pos
  linarith

theorem vacuum_state_conformal_weight :
    primaryConformalWeight (Real.log 1) = 0 := by
  unfold primaryConformalWeight
  rw [Real.log_one]
  norm_num

theorem virasoro_zeta_scaling_alignment (p : ℝ) (hp : 2 ≤ p) :
    (primaryConformalWeight (Real.log p) = (Real.log p) ^ 2 / 2) ∧
    (zetaPoleParameter = 1) ∧
    (primaryConformalWeight (Real.log 1) = 0) :=
  ⟨rfl, rfl, vacuum_state_conformal_weight⟩
