import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

namespace QuantumTransport

/-- Quantum Hall Conductance Unit conductance_unit = e² / h -/
def conductanceUnit (e h : ℝ) (he : e ≠ 0) (hh : 0 < h) : ℝ :=
  (e ^ 2) / h

/-- **Theorem**: Conductance unit is strictly positive: e² / h > 0. -/
theorem conductance_unit_pos (e h : ℝ) (he : e ≠ 0) (hh : 0 < h) :
    0 < conductanceUnit e h he hh := by
  dsimp [conductanceUnit]
  have he2 : 0 < e ^ 2 := sq_pos_of_ne_zero he
  exact div_pos he2 hh

/-- Quantized Hall Conductance σ_xy = (e² / h) * C for integer Chern number C. -/
def hallConductance (e h : ℝ) (he : e ≠ 0) (hh : 0 < h) (C : ℤ) : ℝ :=
  conductanceUnit e h he hh * (C : ℝ)

/-- **Theorem**: Hall Conductance Additivity: σ_xy(C₁ + C₂) = σ_xy(C₁) + σ_xy(C₂). -/
theorem hall_conductance_add (e h : ℝ) (he : e ≠ 0) (hh : 0 < h) (C1 C2 : ℤ) :
    hallConductance e h he hh (C1 + C2) =
    hallConductance e h he hh C1 + hallConductance e h he hh C2 := by
  dsimp [hallConductance]
  push_cast
  ring

/-- **Theorem**: Hall Conductance Zero: σ_xy(0) = 0. -/
theorem hall_conductance_zero (e h : ℝ) (he : e ≠ 0) (hh : 0 < h) :
    hallConductance e h he hh 0 = 0 := by
  dsimp [hallConductance]
  ring

end QuantumTransport
