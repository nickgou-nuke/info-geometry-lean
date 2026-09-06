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

namespace NonAbelianGauge

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Non-Abelian Field Strength Curvature Tensor F(A₁, A₂) = [A₁, A₂] = A₁ A₂ - A₂ A₁. -/
def fieldStrength (A1 A2 : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  A1 * A2 - A2 * A1

/-- **Theorem**: Field Strength Anti-Symmetry F(A₁, A₂) = - F(A₂, A₁). -/
theorem field_strength_antisymmetric (A1 A2 : Matrix (Fin n) (Fin n) ℂ) :
    fieldStrength A1 A2 = - fieldStrength A2 A1 := by
  dsimp [fieldStrength]
  noncomm_ring

/-- **Theorem**: Vanishing Trace of Field Strength Curvature: Tr(F(A₁, A₂)) = 0. -/
theorem field_strength_trace_zero (A1 A2 : Matrix (Fin n) (Fin n) ℂ) :
    trace (fieldStrength A1 A2) = 0 := by
  dsimp [fieldStrength]
  rw [trace_sub]
  have h_comm : trace (A1 * A2) = trace (A2 * A1) := trace_mul_comm A1 A2
  rw [h_comm, sub_self]

/-- Gauge Transformation Covariance of Curvature Tensor F' = U * F * U⁻¹. -/
def transformedFieldStrength (U F : Matrix (Fin n) (Fin n) ℂ) (U_inv : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  U * F * U_inv

/-- **Theorem**: Gauge Invariance of Field Strength Action Trace: Tr(U F U⁻¹) = Tr(F) when U⁻¹ U = 1. -/
theorem field_strength_gauge_trace_invariant (U F U_inv : Matrix (Fin n) (Fin n) ℂ) (h_inv : U_inv * U = 1) :
    trace (transformedFieldStrength U F U_inv) = trace F := by
  dsimp [transformedFieldStrength]
  have h_comm : trace (U * F * U_inv) = trace (U_inv * (U * F)) := trace_mul_comm (U * F) U_inv
  rw [h_comm]
  have h_assoc : U_inv * (U * F) = (U_inv * U) * F := by rw [← Matrix.mul_assoc]
  rw [h_assoc, h_inv, one_mul]

/-- **Theorem**: Non-Abelian Gauge Bianchi Covariant Derivative Trace Identity: Tr([A, F]) = 0. -/
theorem bianchi_covariant_derivative_trace_zero (A A1 A2 : Matrix (Fin n) (Fin n) ℂ) :
    trace (A * fieldStrength A1 A2 - fieldStrength A1 A2 * A) = 0 := by
  rw [trace_sub]
  have h_comm : trace (A * fieldStrength A1 A2) = trace (fieldStrength A1 A2 * A) := trace_mul_comm A (fieldStrength A1 A2)
  rw [h_comm, sub_self]

end NonAbelianGauge
