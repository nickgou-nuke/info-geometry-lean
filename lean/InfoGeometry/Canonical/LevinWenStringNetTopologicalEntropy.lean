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
  Q_v : {Q : Matrix (Fin n) (Fin n) ℂ // IsIdempotentElem Q}
  B_p : {B : Matrix (Fin n) (Fin n) ℂ // IsIdempotentElem B}
  h_comm :
    (Q_v : Matrix (Fin n) (Fin n) ℂ) * B_p =
      (B_p : Matrix (Fin n) (Fin n) ℂ) * Q_v

namespace StringNetOperators

variable (ops : StringNetOperators n)

def QVal : Matrix (Fin n) (Fin n) ℂ := ops.Q_v

def BVal : Matrix (Fin n) (Fin n) ℂ := ops.B_p

theorem h_Q_proj : QVal ops * QVal ops = QVal ops := by
  simpa only [QVal, IsIdempotentElem] using ops.Q_v.2

theorem h_B_proj : BVal ops * BVal ops = BVal ops := by
  simpa only [BVal, IsIdempotentElem] using ops.B_p.2

/-- Total String-Net Ground State Code Projector P_s = Q_v * B_p. -/
def groundStateProjector : Matrix (Fin n) (Fin n) ℂ :=
  QVal ops * BVal ops

/-- **Theorem**: Plaquette-Vertex Commutator Zero: Q_v B_p - B_p Q_v = 0. -/
theorem vertex_plaquette_commute_zero :
    QVal ops * BVal ops - BVal ops * QVal ops = 0 := by
  change (ops.Q_v : Matrix (Fin n) (Fin n) ℂ) * ops.B_p -
      (ops.B_p : Matrix (Fin n) (Fin n) ℂ) * ops.Q_v = 0
  rw [ops.h_comm, sub_self]

/-- **Theorem**: String-Net Ground State Projector Idempotency: P_s² = P_s. -/
theorem ground_state_projector_idempotent :
    ops.groundStateProjector * ops.groundStateProjector = ops.groundStateProjector := by
  dsimp [groundStateProjector]
  calc (QVal ops * BVal ops) * (QVal ops * BVal ops)
    _ = QVal ops * (BVal ops * QVal ops) * BVal ops := by noncomm_ring
    _ = QVal ops * (QVal ops * BVal ops) * BVal ops := by
      have hcomm : BVal ops * QVal ops = QVal ops * BVal ops := by
        simpa only [BVal, QVal] using ops.h_comm.symm
      rw [hcomm]
    _ = (QVal ops * QVal ops) * (BVal ops * BVal ops) := by noncomm_ring
    _ = QVal ops * BVal ops := by rw [h_Q_proj ops, h_B_proj ops]

/-- **Theorem**: String-Net Ground State Projector Trace Commutativity: Tr(P_s) = Tr(B_p Q_v). -/
theorem ground_state_projector_trace_comm :
    trace ops.groundStateProjector = trace (BVal ops * QVal ops) := by
  dsimp [groundStateProjector]
  exact trace_mul_comm (QVal ops) (BVal ops)

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
