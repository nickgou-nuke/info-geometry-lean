import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Complex Real

namespace ChernSimonsGauge

/-- 3D Chern-Simons Action S_CS(k) = k * S_unit for integer level k ∈ ℤ. -/
def chernSimonsAction (S_unit : ℝ) (k : ℤ) : ℝ :=
  (k : ℝ) * S_unit

/-- **Theorem**: Chern-Simons Action Level Linearity: S_CS(k₁ + k₂) = S_CS(k₁) + S_CS(k₂). -/
theorem chern_simons_action_add (S_unit : ℝ) (k1 k2 : ℤ) :
    chernSimonsAction S_unit (k1 + k2) = chernSimonsAction S_unit k1 + chernSimonsAction S_unit k2 := by
  dsimp [chernSimonsAction]
  push_cast
  ring

/-- **Theorem**: Zero Level Chern-Simons Action is Zero. -/
theorem chern_simons_action_zero (S_unit : ℝ) :
    chernSimonsAction S_unit 0 = 0 := by
  dsimp [chernSimonsAction]
  ring

/-- Large Gauge Transformation Phase Shift exp(i * 2π * k * N) = 1 for k, N ∈ ℤ. -/
def largeGaugePhaseShift (k N : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((k * N) : ℝ))

/-- **Theorem**: Topological Path Integral Large Gauge Phase Invariance: exp(2π i k N) = 1. -/
theorem large_gauge_phase_invariance (k N : ℤ) :
    largeGaugePhaseShift k N = 1 := by
  dsimp [largeGaugePhaseShift]
  have h_angle : 2 * Real.pi * Complex.I * ((k * N) : ℝ) = (k * N : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h_angle, Complex.exp_int_mul]
  have h2pi : Complex.exp (2 * Real.pi * Complex.I) = 1 := by simp
  rw [h2pi, one_zpow]

end ChernSimonsGauge
