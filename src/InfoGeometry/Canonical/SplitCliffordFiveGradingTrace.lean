import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordFiveGrading

/-!
# InfoGeometry.Canonical.SplitCliffordFiveGradingTrace

Minimal trace-metric facts for the concrete five-grading operators.
-/

namespace InfoGeometry.Canonical.SplitCliffordFiveGradingTrace

open Matrix
open InfoGeometry.Canonical.SplitCliffordFiveGrading

/-- Explicit trace on `M4R`. -/
def tr4 (A : InfoGeometry.Canonical.SplitCliffordFiveGrading.M4R) : ℝ := A 0 0 + A 1 1 + A 2 2 + A 3 3

/-- Bilinear trace form `⟪A,B⟫ = tr4 (A * B)`. -/
def traceForm
    (A B : InfoGeometry.Canonical.SplitCliffordFiveGrading.M4R) : ℝ := tr4 (A * B)

/-- Trace of the concrete boundary commutator vanishes. -/
theorem trace_boundary_commutator_zero :
    tr4 (comm4 gPlus1 gMinus1) = 0 := by
  rw [grading_boundary_commutator_explicit, tr4]
  simp

end InfoGeometry.Canonical.SplitCliffordFiveGradingTrace
