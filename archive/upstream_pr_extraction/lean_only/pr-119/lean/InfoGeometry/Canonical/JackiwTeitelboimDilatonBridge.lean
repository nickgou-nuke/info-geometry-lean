import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

namespace JackiwTeitelboim

/-- 2D Topological Euler Characteristic χ(M) = 2 - 2g - b for genus g and boundary count b. -/
def eulerCharacteristic (g b : ℤ) : ℤ :=
  2 - 2 * g - b

/-- **Theorem**: Topological Euler Characteristic of Hyperbolic Disk (g = 0, b = 1): χ(Disk) = 1. -/
theorem euler_char_disk : eulerCharacteristic 0 1 = 1 := rfl

/-- 2D JT Gravity Topological Action S_top = S_0 * χ(M). -/
def jtTopologicalAction (S0 : ℝ) (g b : ℤ) : ℝ :=
  S0 * (eulerCharacteristic g b : ℝ)

/-- **Theorem**: Disk Topological Action S_top(Disk) = S_0. -/
theorem jt_disk_action (S0 : ℝ) :
    jtTopologicalAction S0 0 1 = S0 := by
  dsimp [jtTopologicalAction]
  rw [euler_char_disk]
  ring

/-- Schwarzian Boundary Action S_Sch = C / β for boundary coupling constant C > 0. -/
def schwarzianAction (C beta : ℝ) (hC : 0 < C) (h_beta : 0 < beta) : ℝ :=
  C / beta

/-- **Theorem**: Schwarzian Action is strictly positive: S_Sch > 0. -/
theorem schwarzian_action_pos (C beta : ℝ) (hC : 0 < C) (h_beta : 0 < beta) :
    0 < schwarzianAction C beta hC h_beta := by
  dsimp [schwarzianAction]
  exact div_pos hC h_beta

end JackiwTeitelboim
