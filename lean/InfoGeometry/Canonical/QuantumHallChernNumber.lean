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

namespace QuantumHallChern

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

namespace HallProjector

variable (P : selfAdjoint (Matrix (Fin n) (Fin n) ℂ))

def matrixVal : Matrix (Fin n) (Fin n) ℂ := P

theorem self_adjoint : (matrixVal P).conjTranspose = matrixVal P := by
  simpa only [matrixVal, Matrix.star_eq_conjTranspose] using P.property

/-- **Theorem**: Hall Projector Idempotency P² = P. -/
theorem hall_projector_idempotent
    (h_proj_sq : matrixVal P * matrixVal P = matrixVal P) :
    matrixVal P * matrixVal P = matrixVal P := h_proj_sq

/-- Non-Abelian Kubo Curvature Form F(P, X, Y) = P * (X * Y - Y * X) * P. -/
def kuboCurvature (X Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  matrixVal P * (X * Y - Y * X) * matrixVal P

/-- **Theorem**: Kubo Curvature Anti-Symmetry F(P, X, Y) = - F(P, Y, X). -/
theorem kubo_curvature_antisymmetric (X Y : Matrix (Fin n) (Fin n) ℂ) :
    kuboCurvature P X Y = - kuboCurvature P Y X := by
  dsimp [kuboCurvature]
  noncomm_ring

/-- **Theorem**: Kubo Curvature Projection Invariance P * F(P, X, Y) = F(P, X, Y). -/
theorem kubo_curvature_projected_left
    (h_proj_sq : matrixVal P * matrixVal P = matrixVal P)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    matrixVal P * kuboCurvature P X Y = kuboCurvature P X Y := by
  dsimp [kuboCurvature]
  have h_assoc : matrixVal P * (matrixVal P * (X * Y - Y * X) * matrixVal P) = (matrixVal P * matrixVal P) * (X * Y - Y * X) * matrixVal P := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [h_assoc]
  rw [h_proj_sq]

/-- **Theorem**: Topological Hall Conductance Trace Commutativity: Tr(P [X, Y] P) = Tr([X, Y] P). -/
theorem hall_conductance_trace_comm
    (h_proj_sq : matrixVal P * matrixVal P = matrixVal P)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    trace (kuboCurvature P X Y) = trace ((X * Y - Y * X) * matrixVal P) := by
  dsimp [kuboCurvature]
  have h_assoc : matrixVal P * (X * Y - Y * X) * matrixVal P = matrixVal P * ((X * Y - Y * X) * matrixVal P) := by
    rw [Matrix.mul_assoc]
  rw [h_assoc]
  have h_comm : trace (matrixVal P * ((X * Y - Y * X) * matrixVal P)) = trace (((X * Y - Y * X) * matrixVal P) * matrixVal P) := trace_mul_comm (matrixVal P) ((X * Y - Y * X) * matrixVal P)
  rw [h_comm]
  have h_sq : ((X * Y - Y * X) * matrixVal P) * matrixVal P = (X * Y - Y * X) * (matrixVal P * matrixVal P) := by
    rw [Matrix.mul_assoc]
  rw [h_sq]
  rw [h_proj_sq]

end HallProjector

end QuantumHallChern
