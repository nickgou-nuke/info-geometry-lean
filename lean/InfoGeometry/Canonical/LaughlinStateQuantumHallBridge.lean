import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Real

namespace QuantumHall

namespace LaughlinState

/-- Filling factor ν = 1 / m -/
def fillingFactor (m : ℕ) : ℝ :=
  1 / (m : ℝ)

/-- **Theorem**: Filling factor is strictly positive: 0 < ν. -/
theorem filling_factor_pos (m : ℕ) (hm : 0 < m) : 0 < fillingFactor m := by
  dsimp [fillingFactor]
  exact one_div_pos.mpr (Nat.cast_pos.mpr hm)

/-- Quasi-hole fractional electric charge q = e / m -/
def quasiHoleCharge (m : ℕ) (e : ℝ) : ℝ :=
  e / (m : ℝ)

/-- **Theorem**: Quasi-hole charge is a fraction of fundamental electron charge: q * m = e. -/
theorem quasi_hole_charge_mult (m : ℕ) (hm : 0 < m) (e : ℝ) :
    quasiHoleCharge m e * (m : ℝ) = e := by
  dsimp [quasiHoleCharge]
  exact div_mul_cancel₀ e (ne_of_gt (Nat.cast_pos.mpr hm))

/-- Laughlin anyonic exchange braid phase θ = π / m -/
def anyonBraidPhase (m : ℕ) : ℝ :=
  Real.pi / (m : ℝ)

/-- **Theorem**: Anyon exchange phase is positive for m ≥ 1: 0 < θ. -/
theorem anyon_braid_phase_pos (m : ℕ) (hm : 0 < m) : 0 < anyonBraidPhase m := by
  dsimp [anyonBraidPhase]
  exact div_pos Real.pi_pos (Nat.cast_pos.mpr hm)

end LaughlinState

end QuantumHall
