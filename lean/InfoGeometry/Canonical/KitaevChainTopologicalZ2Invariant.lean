import Mathlib.Analysis.Complex.Basic
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

namespace KitaevChainTopologicalZ2Invariant

/-- Majorana Zero Mode Operator in Mₙ(ℂ). -/
structure MajoranaOperator (n : ℕ) [DecidableEq (Fin n)] where
  gamma : Matrix (Fin n) (Fin n) ℂ
  h_self_adjoint : gamma.conjTranspose = gamma
  h_involution : gamma * gamma = 1

/-- Fermion Parity Operator P = (-1)ᵀ. -/
structure FermionParityOperator (n : ℕ) [DecidableEq (Fin n)] where
  parity : Matrix (Fin n) (Fin n) ℂ
  h_self_adjoint : parity.conjTranspose = parity
  h_involution : parity * parity = 1

namespace KitaevChain

variable {n : ℕ} [DecidableEq (Fin n)] (m : MajoranaOperator n) (p : FermionParityOperator n)

/-- **Theorem**: Majorana Operator Self-Adjointness: γ† = γ. -/
theorem majorana_self_adjoint :
    m.gamma.conjTranspose = m.gamma :=
  m.h_self_adjoint

/-- **Theorem**: Majorana Operator Nilpotent Square: γ² = 1. -/
theorem majorana_involution :
    m.gamma * m.gamma = 1 :=
  m.h_involution

/-- **Theorem**: Fermion Parity Involutivity: P² = 1. -/
theorem parity_involution :
    p.parity * p.parity = 1 :=
  p.h_involution

/-- **Theorem**: Fermion Parity Unitary Trace Conservation: Tr(P P†) = n. -/
theorem parity_trace_conservation :
    trace (p.parity * p.parity.conjTranspose) = n := by
  rw [p.h_self_adjoint, p.h_involution, trace_one, Fintype.card_fin]

/-- **Theorem**: Majorana Edge State Parity Intertwining & Trace Conservation:
    If P γ = -γ P for odd Majorana edge mode, then Tr(P γ P†) = -Tr(γ). -/
theorem majorana_edge_parity_trace (h_anti_comm : p.parity * m.gamma = - (m.gamma * p.parity)) :
    trace (p.parity * m.gamma * p.parity.conjTranspose) = - trace m.gamma := by
  have h_step : p.parity * m.gamma * p.parity = - (m.gamma * (p.parity * p.parity)) := by
    calc p.parity * m.gamma * p.parity
      _ = (p.parity * m.gamma) * p.parity := rfl
      _ = (- (m.gamma * p.parity)) * p.parity := by rw [h_anti_comm]
      _ = - (m.gamma * (p.parity * p.parity)) := by noncomm_ring
  rw [p.h_self_adjoint, h_step, p.h_involution, mul_one, trace_neg]

end KitaevChain

end KitaevChainTopologicalZ2Invariant
