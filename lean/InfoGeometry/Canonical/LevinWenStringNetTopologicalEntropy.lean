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

namespace StringNetOperators

variable (ops : StringNetOperators n)

theorem h_Q_proj :
    (ops.Q_v : Matrix (Fin n) (Fin n) ℂ) * ops.Q_v = ops.Q_v := by
  simpa only [IsIdempotentElem] using ops.Q_v.2

theorem h_B_proj :
    (ops.B_p : Matrix (Fin n) (Fin n) ℂ) * ops.B_p = ops.B_p := by
  simpa only [IsIdempotentElem] using ops.B_p.2

/-- Total String-Net Ground State Code Projector P_s = Q_v * B_p. -/
def groundStateProjector : Matrix (Fin n) (Fin n) ℂ :=
  (ops.Q_v : Matrix (Fin n) (Fin n) ℂ) * ops.B_p

/-- **Theorem**: Plaquette-Vertex Commutator Zero: Q_v B_p - B_p Q_v = 0. -/
theorem vertex_plaquette_commute_zero
    (h_comm :
      (ops.Q_v : Matrix (Fin n) (Fin n) ℂ) * ops.B_p =
        (ops.B_p : Matrix (Fin n) (Fin n) ℂ) * ops.Q_v) :
    (ops.Q_v : Matrix (Fin n) (Fin n) ℂ) * ops.B_p -
        ops.B_p * ops.Q_v = 0 := by
  rw [h_comm, sub_self]

/-- **Theorem**: String-Net Ground State Projector Idempotency: P_s² = P_s. -/
theorem ground_state_projector_idempotent
    (h_comm :
      (ops.Q_v : Matrix (Fin n) (Fin n) ℂ) * ops.B_p =
        (ops.B_p : Matrix (Fin n) (Fin n) ℂ) * ops.Q_v) :
    ops.groundStateProjector * ops.groundStateProjector = ops.groundStateProjector := by
  dsimp [groundStateProjector]
  calc
    ((ops.Q_v : Matrix (Fin n) (Fin n) ℂ) * ops.B_p) *
        ((ops.Q_v : Matrix (Fin n) (Fin n) ℂ) * ops.B_p) =
        (ops.Q_v : Matrix (Fin n) (Fin n) ℂ) *
          (ops.B_p * ops.Q_v) * ops.B_p := by noncomm_ring
    _ = (ops.Q_v : Matrix (Fin n) (Fin n) ℂ) *
          (ops.Q_v * ops.B_p) * ops.B_p := by
      rw [show ops.B_p * (ops.Q_v : Matrix (Fin n) (Fin n) ℂ) =
          (ops.Q_v : Matrix (Fin n) (Fin n) ℂ) * ops.B_p from h_comm.symm]
    _ = ((ops.Q_v : Matrix (Fin n) (Fin n) ℂ) * ops.Q_v) *
          (ops.B_p * ops.B_p) := by noncomm_ring
    _ = (ops.Q_v : Matrix (Fin n) (Fin n) ℂ) * ops.B_p := by
      rw [h_Q_proj ops, h_B_proj ops]

/-- **Theorem**: String-Net Ground State Projector Trace Commutativity: Tr(P_s) = Tr(B_p Q_v). -/
theorem ground_state_projector_trace_comm :
    trace ops.groundStateProjector =
      trace ((ops.B_p : Matrix (Fin n) (Fin n) ℂ) *
        (ops.Q_v : Matrix (Fin n) (Fin n) ℂ)) := by
  dsimp [groundStateProjector]
  exact trace_mul_comm (ops.Q_v : Matrix (Fin n) (Fin n) ℂ) ops.B_p

/-- Topological Entanglement Entropy Function S(L, α, γ) = α L - γ. -/
def topologicalEntanglementEntropy (L alpha gamma : ℝ) : ℝ :=
  alpha * L - gamma

/-- **Theorem**: Area Law Linear Correction Subtraction: S(L, α, γ) - α L = - γ. -/
theorem topological_entropy_universal_correction (L alpha gamma : ℝ) :
    topologicalEntanglementEntropy L alpha gamma - alpha * L = - gamma := by
  dsimp [topologicalEntanglementEntropy]
  ring

end StringNetOperators

/-! ### Constructive 2×2 Matrix Model of Commuting String-Net Projectors -/

/-- Commuting vertex projector $Q_v = I_2$. -/
def standardQv : Matrix (Fin 2) (Fin 2) ℂ :=
  1

/-- Commuting plaquette projector $B_p = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$. -/
def standardBp : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0;
     0, 0]

/-- $Q_v$ is idempotent: $Q_v^2 = Q_v$. -/
theorem standardQv_idem : IsIdempotentElem standardQv := by
  dsimp [standardQv, IsIdempotentElem]
  rw [Matrix.mul_one]

/-- $B_p$ is idempotent: $B_p^2 = B_p$. -/
theorem standardBp_idem : IsIdempotentElem standardBp := by
  dsimp [standardBp, IsIdempotentElem]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Concrete 2×2 StringNetOperators package. -/
def standardStringNetOps : StringNetOperators 2 where
  Q_v := ⟨standardQv, standardQv_idem⟩
  B_p := ⟨standardBp, standardBp_idem⟩

/-- 🏆 THEOREM 1 (Constructive Commutator Zero):
    $[Q_v, B_p] = 0$. -/
theorem standard_vertex_plaquette_commute :
    (standardStringNetOps.Q_v : Matrix (Fin 2) (Fin 2) ℂ) * standardStringNetOps.B_p =
      (standardStringNetOps.B_p : Matrix (Fin 2) (Fin 2) ℂ) * standardStringNetOps.Q_v := by
  dsimp [standardStringNetOps, standardQv, standardBp]
  rw [Matrix.one_mul, Matrix.mul_one]

/-- 🏆 THEOREM 2 (Constructive Ground State Projector Idempotency):
    $P_s^2 = P_s$ with 0 hypotheses. -/
theorem standard_ground_state_projector_idempotent :
    standardStringNetOps.groundStateProjector * standardStringNetOps.groundStateProjector =
      standardStringNetOps.groundStateProjector :=
  StringNetOperators.ground_state_projector_idempotent standardStringNetOps standard_vertex_plaquette_commute

/-- 🏆 THEOREM 3 (Constructive Code Degeneracy):
    $\operatorname{Tr}(P_s) = 1$. -/
theorem standard_ground_state_trace :
    trace standardStringNetOps.groundStateProjector = 1 := by
  dsimp [standardStringNetOps, StringNetOperators.groundStateProjector, standardQv, standardBp, Matrix.trace]
  simp [Fin.sum_univ_two]

end LevinWenStringNet
