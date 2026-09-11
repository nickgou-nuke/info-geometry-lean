import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Complex

namespace KacMoody

/-- U(1) Kac-Moody Current Algebra generator J_n commutator [J_m, J_n] = m * δ_{m+n, 0}. -/
def currentCommutator (m n : ℤ) : ℂ :=
  if m + n = 0 then (m : ℂ) else 0

/-- **Theorem**: Kac-Moody Anti-Symmetry: [J_m, J_n] = - [J_n, J_m]. -/
theorem current_commutator_antisymm (m n : ℤ) :
    currentCommutator m n = - currentCommutator n m := by
  dsimp [currentCommutator]
  have h_add : m + n = 0 ↔ n + m = 0 := by rw [add_comm]
  by_cases h : m + n = 0
  · have h2 : n + m = 0 := h_add.mp h
    rw [if_pos h, if_pos h2]
    have hn : n = -m := by linarith
    rw [hn]; push_cast; ring
  · have h2 : ¬(n + m = 0) := fun h_nm => h (h_add.mpr h_nm)
    rw [if_neg h, if_neg h2]
    ring

/-- **Theorem**: Zero mode commutes with all current generators: [J_0, J_n] = 0. -/
theorem current_zero_mode_commute (n : ℤ) :
    currentCommutator 0 n = 0 := by
  dsimp [currentCommutator]
  split_ifs with h
  · have hn : n = 0 := by linarith
    subst hn; ring
  · rfl

/-- Sugawara Construction Central Charge c = 1 for chiral U(1) boson edge state. -/
def sugawaraCentralCharge : ℝ := 1

/-- **Theorem**: Central Charge is strictly positive: c = 1 > 0. -/
theorem central_charge_pos : 0 < sugawaraCentralCharge := by
  dsimp [sugawaraCentralCharge]
  norm_num

/-- Virasoro Central Extension Anomaly term (c / 12) * m * (m² - 1) * δ_{m+n, 0}. -/
def virasoroCentralAnomaly (c : ℝ) (m n : ℤ) : ℝ :=
  if m + n = 0 then (c / 12) * (m : ℝ) * ((m : ℝ) ^ 2 - 1) else 0

/-- **Theorem**: Virasoro Anomaly vanishes for m = 0, ±1 (SL(2, ℝ) global subalgebra invariance). -/
theorem virasoro_anomaly_sl2_invariance (c : ℝ) (n : ℤ) :
    virasoroCentralAnomaly c 0 n = 0 ∧
    virasoroCentralAnomaly c 1 (-1) = 0 ∧
    virasoroCentralAnomaly c (-1) 1 = 0 := by
  dsimp [virasoroCentralAnomaly]
  refine ⟨by split_ifs; ring; rfl, ⟨by ring, by ring⟩⟩

end KacMoody
