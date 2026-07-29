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

/-- Quantum Hall Projection Operator P satisfying P² = P and P† = P. -/
structure HallProjector (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  P_val : selfAdjoint (Matrix (Fin n) (Fin n) ℂ)
  h_proj_sq :
    (P_val : Matrix (Fin n) (Fin n) ℂ) * P_val = P_val

namespace HallProjector

variable (proj : HallProjector n)

def matrixVal : Matrix (Fin n) (Fin n) ℂ := proj.P_val

theorem self_adjoint : (matrixVal proj).conjTranspose = matrixVal proj := by
  simpa only [matrixVal, Matrix.star_eq_conjTranspose] using proj.P_val.property

/-- **Theorem**: Hall Projector Idempotency P² = P. -/
theorem hall_projector_idempotent : matrixVal proj * matrixVal proj = matrixVal proj :=
  by simpa [matrixVal] using proj.h_proj_sq

/-- Non-Abelian Kubo Curvature Form F(P, X, Y) = P * (X * Y - Y * X) * P. -/
def kuboCurvature (X Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  matrixVal proj * (X * Y - Y * X) * matrixVal proj

/-- **Theorem**: Kubo Curvature Anti-Symmetry F(P, X, Y) = - F(P, Y, X). -/
theorem kubo_curvature_antisymmetric (X Y : Matrix (Fin n) (Fin n) ℂ) :
    proj.kuboCurvature X Y = - proj.kuboCurvature Y X := by
  dsimp [kuboCurvature]
  noncomm_ring

/-- **Theorem**: Kubo Curvature Projection Invariance P * F(P, X, Y) = F(P, X, Y). -/
theorem kubo_curvature_projected_left (X Y : Matrix (Fin n) (Fin n) ℂ) :
    matrixVal proj * proj.kuboCurvature X Y = proj.kuboCurvature X Y := by
  dsimp [kuboCurvature]
  have h_assoc : matrixVal proj * (matrixVal proj * (X * Y - Y * X) * matrixVal proj) = (matrixVal proj * matrixVal proj) * (X * Y - Y * X) * matrixVal proj := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [h_assoc]
  rw [show matrixVal proj * matrixVal proj = matrixVal proj by simpa [matrixVal] using proj.h_proj_sq]

/-- **Theorem**: Topological Hall Conductance Trace Commutativity: Tr(P [X, Y] P) = Tr([X, Y] P). -/
theorem hall_conductance_trace_comm (X Y : Matrix (Fin n) (Fin n) ℂ) :
    trace (proj.kuboCurvature X Y) = trace ((X * Y - Y * X) * matrixVal proj) := by
  dsimp [kuboCurvature]
  have h_assoc : matrixVal proj * (X * Y - Y * X) * matrixVal proj = matrixVal proj * ((X * Y - Y * X) * matrixVal proj) := by
    rw [Matrix.mul_assoc]
  rw [h_assoc]
  have h_comm : trace (matrixVal proj * ((X * Y - Y * X) * matrixVal proj)) = trace (((X * Y - Y * X) * matrixVal proj) * matrixVal proj) := trace_mul_comm (matrixVal proj) ((X * Y - Y * X) * matrixVal proj)
  rw [h_comm]
  have h_sq : ((X * Y - Y * X) * matrixVal proj) * matrixVal proj = (X * Y - Y * X) * (matrixVal proj * matrixVal proj) := by
    rw [Matrix.mul_assoc]
  rw [h_sq]
  rw [show matrixVal proj * matrixVal proj = matrixVal proj by simpa [matrixVal] using proj.h_proj_sq]

end HallProjector

end QuantumHallChern
