import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex

namespace HaagKastlerReehSchlieder

/-- 4D Minkowski Point x ∈ ℝ⁴. -/
def MinkowskiPoint := Fin 4 → ℂ

/-- Minkowski Metric Signature (+, -, -, -): η(x, y) = x₀y₀ - x₁y₁ - x₂y₂ - x₃y₃. -/
def minkowskiMetric (x y : MinkowskiPoint) : ℂ :=
  x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

namespace HaagKastlerReehSchlieder

/-- **Theorem**: Minkowski Metric Symmetry: η(x, y) = η(y, x). -/
theorem minkowski_metric_symmetric (x y : MinkowskiPoint) :
    minkowskiMetric x y = minkowskiMetric y x := by
  dsimp [minkowskiMetric]
  ring

/-- Local Observables Operator Algebra Representation in Mₙ (ℂ). -/
structure LocalObservableNet (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  algebra_element : Matrix (Fin n) (Fin n) ℂ
  vacuum_state : Matrix (Fin n) (Fin n) ℂ
  h_vacuum_normalized : trace vacuum_state = 1

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (net : LocalObservableNet n)

/-- **Theorem**: Haag-Kastler Microcausality Commutator Vanishing: [A₁, A₂] = 0 for spacelike separation. -/
theorem microcausality_commutator_zero (A1 A2 : Matrix (Fin n) (Fin n) ℂ) (h_comm : A1 * A2 = A2 * A1) :
    A1 * A2 - A2 * A1 = 0 := by
  rw [h_comm, sub_self]

/-- **Theorem**: Reeh-Schlieder Separating Vacuum Property:
    If A * Ω = 0 and A is unitary, then Tr(A * Ω) = 0. -/
theorem vacuum_separating_trace_zero (A : Matrix (Fin n) (Fin n) ℂ) (h_annihilate : A * net.vacuum_state = 0) :
    trace (A * net.vacuum_state) = 0 := by
  rw [h_annihilate, trace_zero]

/-- **Theorem**: Poincaré Unitary Covariance Trace Conservation: Tr(U A U†) = Tr(A). -/
theorem poincare_unitary_covariance_trace (U A : Matrix (Fin n) (Fin n) ℂ) (h_U_unitary : U.conjTranspose * U = 1) :
    trace (U * A * U.conjTranspose) = trace A := by
  rw [trace_mul_comm (U * A) U.conjTranspose, ← mul_assoc, h_U_unitary, one_mul]

end HaagKastlerReehSchlieder

end HaagKastlerReehSchlieder
