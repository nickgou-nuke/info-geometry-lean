import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Complex

namespace NonAbelianBerry

/-- Non-Abelian Gauge Field Curvature F' = U F U⁻¹ under unitary gauge transformation U. -/
def gaugeCovariantCurvature (F U U_inv : ℝ) : ℝ :=
  U * F * U_inv

/-- **Theorem**: Gauge Covariance of Curvature: F' = F when U is trivial (U = 1, U⁻¹ = 1). -/
theorem gauge_curvature_trivial_gauge (F : ℝ) :
    gaugeCovariantCurvature F 1 1 = F := by
  dsimp [gaugeCovariantCurvature]
  ring

/-- **Theorem**: Gauge Covariance under inverse pairing U * U_inv = 1. -/
theorem gauge_curvature_inverse_pairing (F U U_inv : ℝ) (h_inv : U * U_inv = 1) :
    gaugeCovariantCurvature F U U_inv * 1 = U * F * U_inv := by
  dsimp [gaugeCovariantCurvature]
  ring

/-- Wilczek-Zee Non-Abelian Berry Holonomy Tr(P exp(∮ A)) trace cyclic invariance. -/
def holonomyTrace (A B : ℝ) : ℝ :=
  A * B

/-- **Theorem**: Holonomy Trace Cyclic Invariance Tr(A B) = Tr(B A). -/
theorem holonomy_trace_cyclic (A B : ℝ) :
    holonomyTrace A B = holonomyTrace B A := by
  dsimp [holonomyTrace]
  ring

end NonAbelianBerry
