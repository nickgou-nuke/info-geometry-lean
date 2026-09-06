import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Spectral.HeisenbergTime

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def meanLevelDensity (E : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * Real.log (E / (2 * Real.pi))

def heisenbergTime (E : ℝ) : ℝ :=
  2 * Real.pi * meanLevelDensity E

theorem heisenberg_time_log_scale (E : ℝ) :
    heisenbergTime E = Real.log (E / (2 * Real.pi)) := by
  unfold heisenbergTime meanLevelDensity
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_nz : 2 * Real.pi ≠ 0 := by linarith
  calc 2 * Real.pi * ((1 / (2 * Real.pi)) * Real.log (E / (2 * Real.pi)))
    _ = (2 * Real.pi * (1 / (2 * Real.pi))) * Real.log (E / (2 * Real.pi)) := by ring
    _ = 1 * Real.log (E / (2 * Real.pi)) := by rw [mul_one_div_cancel h_pi_nz]
    _ = Real.log (E / (2 * Real.pi)) := by ring
