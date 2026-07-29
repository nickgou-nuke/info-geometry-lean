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

namespace LevinWenStringNet

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Levin-Wen String-Net Liquid Lattice Projector Operators Q_v (vertex) and B_p (plaquette). -/
structure StringNetOperators (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  Q_v : Matrix (Fin n) (Fin n) ℂ
  B_p : Matrix (Fin n) (Fin n) ℂ
  h_Q_proj : Q_v * Q_v = Q_v
  h_B_proj : B_p * B_p = B_p
  h_comm : Q_v * B_p = B_p * Q_v

namespace StringNetOperators

variable (ops : StringNetOperators n)

/-- Total String-Net Ground State Code Projector P_s = Q_v * B_p. -/
def groundStateProjector : Matrix (Fin n) (Fin n) ℂ :=
  ops.Q_v * ops.B_p

/-- **Theorem**: Plaquette-Vertex Commutator Zero: Q_v B_p - B_p Q_v = 0. -/
theorem vertex_plaquette_commute_zero :
    ops.Q_v * ops.B_p - ops.B_p * ops.Q_v = 0 := by
  rw [ops.h_comm, sub_self]

/-- **Theorem**: String-Net Ground State Projector Idempotency: P_s² = P_s. -/
theorem ground_state_projector_idempotent :
    ops.groundStateProjector * ops.groundStateProjector = ops.groundStateProjector := by
  dsimp [groundStateProjector]
  calc (ops.Q_v * ops.B_p) * (ops.Q_v * ops.B_p)
    _ = ops.Q_v * (ops.B_p * ops.Q_v) * ops.B_p := by noncomm_ring
    _ = ops.Q_v * (ops.Q_v * ops.B_p) * ops.B_p := by rw [← ops.h_comm]
    _ = (ops.Q_v * ops.Q_v) * (ops.B_p * ops.B_p) := by noncomm_ring
    _ = ops.Q_v * ops.B_p := by rw [ops.h_Q_proj, ops.h_B_proj]

/-- **Theorem**: String-Net Ground State Projector Trace Commutativity: Tr(P_s) = Tr(B_p Q_v). -/
theorem ground_state_projector_trace_comm :
    trace ops.groundStateProjector = trace (ops.B_p * ops.Q_v) := by
  dsimp [groundStateProjector]
  exact trace_mul_comm ops.Q_v ops.B_p

/-- Topological Entanglement Entropy Function S(L, α, γ) = α L - γ. -/
def topologicalEntanglementEntropy (L alpha gamma : ℝ) : ℝ :=
  alpha * L - gamma

/-- **Theorem**: Area Law Linear Correction Subtraction: S(L, α, γ) - α L = - γ. -/
theorem topological_entropy_universal_correction (L alpha gamma : ℝ) :
    topologicalEntanglementEntropy L alpha gamma - alpha * L = - gamma := by
  dsimp [topologicalEntanglementEntropy]
  ring

end StringNetOperators

end LevinWenStringNet
