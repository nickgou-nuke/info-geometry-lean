import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex

namespace ConnesSpectral1Form

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Non-Commutative Exterior Derivative da = [D, a] = D * a - a * D for Dirac Operator D. -/
def exteriorDerivative (D a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  D * a - a * D

/-- **Theorem**: Leibniz Rule for Non-Commutative Exterior Derivative:
    d(a * b) = (d a) * b + a * (d b). -/
theorem exterior_derivative_leibniz (D a b : Matrix (Fin n) (Fin n) ℂ) :
    exteriorDerivative D (a * b) = (exteriorDerivative D a) * b + a * (exteriorDerivative D b) := by
  dsimp [exteriorDerivative]
  noncomm_ring

/-- **Theorem**: Zero Derivative of Identity Element: d(1) = 0. -/
theorem exterior_derivative_one (D : Matrix (Fin n) (Fin n) ℂ) :
    exteriorDerivative D 1 = 0 := by
  dsimp [exteriorDerivative]
  rw [mul_one, one_mul, sub_self]

/-- Non-Commutative 1-Form ω = a * d b = a * (D * b - b * D). -/
def nonCommutativeOneForm (D a b : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  a * (exteriorDerivative D b)

/-- **Theorem**: 1-Form Linearity in Base Element: (a₁ + a₂) * d b = a₁ * d b + a₂ * d b. -/
theorem one_form_left_add (D a1 a2 b : Matrix (Fin n) (Fin n) ℂ) :
    nonCommutativeOneForm D (a1 + a2) b = nonCommutativeOneForm D a1 b + nonCommutativeOneForm D a2 b := by
  dsimp [nonCommutativeOneForm]
  noncomm_ring

/-- **Theorem**: Vanishing Trace of Dirac Commutator 1-Form: Tr(d a) = 0. -/
theorem exterior_derivative_trace_zero (D a : Matrix (Fin n) (Fin n) ℂ) :
    trace (exteriorDerivative D a) = 0 := by
  dsimp [exteriorDerivative]
  rw [trace_sub]
  have h_comm : trace (a * D) = trace (D * a) := trace_mul_comm a D
  rw [h_comm, sub_self]

end ConnesSpectral1Form
