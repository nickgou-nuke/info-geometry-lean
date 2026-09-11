import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Real

namespace JarzynskiThermodynamics

/-- Dissipative Non-Equilibrium Work W_diss = <W> - ΔF. -/
def dissipatedWork (W_avg deltaF : ℝ) : ℝ :=
  W_avg - deltaF

/-- **Theorem**: Reversible Process (Zero Dissipated Work): <W> = ΔF ⟹ W_diss = 0. -/
theorem reversible_process_zero_dissipation (W_avg deltaF : ℝ) (h_rev : W_avg = deltaF) :
    dissipatedWork W_avg deltaF = 0 := by
  dsimp [dissipatedWork]
  rw [h_rev]
  ring

/-- **Theorem**: Second Law of Non-Equilibrium Thermodynamics: <W> ≥ ΔF ⟹ W_diss ≥ 0. -/
theorem second_law_work_inequality (W_avg deltaF : ℝ) (h_second_law : deltaF ≤ W_avg) :
    0 ≤ dissipatedWork W_avg deltaF := by
  dsimp [dissipatedWork]
  linarith

/-- Jarzynski Exponential Average Identity: exp(-β * ΔF) = exp(-β * ΔF). -/
def jarzynskiAverageExp (beta deltaF : ℝ) : ℝ :=
  Real.exp (-beta * deltaF)

/-- **Theorem**: Jarzynski Equality Identity Consistency. -/
theorem jarzynski_equality_consistency (beta deltaF : ℝ) :
    jarzynskiAverageExp beta deltaF = Real.exp (-beta * deltaF) := rfl

end JarzynskiThermodynamics
