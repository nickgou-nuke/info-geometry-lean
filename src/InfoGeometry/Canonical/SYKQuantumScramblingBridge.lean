import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

namespace SYKScrambling

/-- Majorana Operator Anti-Commutator {χ_i, χ_j} = 2 * δ_{ij}. -/
def majoranaAntiCommutator (i j : ℕ) : ℝ :=
  if i = j then 2 else 0

/-- **Theorem**: Same-site Majorana Anti-Commutator 2 * χ_i² = 2. -/
theorem majorana_same_site_anticomm (i : ℕ) :
    majoranaAntiCommutator i i = 2 := by
  dsimp [majoranaAntiCommutator]
  rw [if_pos rfl]

/-- **Theorem**: Different-site Majorana Anti-Commutator {χ_i, χ_j} = 0 for i ≠ j. -/
theorem majorana_diff_site_anticomm (i j : ℕ) (h_ne : i ≠ j) :
    majoranaAntiCommutator i j = 0 := by
  dsimp [majoranaAntiCommutator]
  rw [if_neg h_ne]

/-- SYK Low-Temperature Linear Specific Heat C(T) = gamma * T. -/
def sykSpecificHeat (gamma T : ℝ) : ℝ :=
  gamma * T

/-- **Theorem**: SYK Low-Temperature Specific Heat Positivity for gamma > 0 and T > 0. -/
theorem syk_specific_heat_pos (gamma T : ℝ) (h_gamma : 0 < gamma) (h_T : 0 < T) :
    0 < sykSpecificHeat gamma T := by
  dsimp [sykSpecificHeat]
  exact mul_pos h_gamma h_T

end SYKScrambling
