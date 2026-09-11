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

namespace FierzModularConjugationBridge

/-- Fierz-Tomita Holographic Scattering System in Mₙ(ℂ). -/
structure FierzModularSystem (n : ℕ) [DecidableEq (Fin n)] where
  J     : Matrix (Fin n) (Fin n) ℂ  -- Tomita Modular Conjugation
  Gamma : Matrix (Fin n) (Fin n) ℂ  -- Fierz Clifford Channel (S,V,T,A,P)
  X     : Matrix (Fin n) (Fin n) ℂ  -- Macroscopic Observer State
  h_J_sq : J * J = 1
  h_fierz_odd : J * Gamma * J = - Gamma
  h_state_even : J * X * J = X

namespace FierzTomitaScattering

variable {n : ℕ} [DecidableEq (Fin n)] (sys : FierzModularSystem n)

/-- **Theorem**: Fierz-Tomita Product Transformation Identity:
    Γ X = - (J (Γ X) J). -/
theorem fierz_tomita_product_identity :
    sys.Gamma * sys.X = - (sys.J * (sys.Gamma * sys.X) * sys.J) := by
  have h1 : (sys.J * sys.Gamma * sys.J) * (sys.J * sys.X * sys.J) = sys.J * (sys.Gamma * sys.X) * sys.J := by
    calc (sys.J * sys.Gamma * sys.J) * (sys.J * sys.X * sys.J)
      _ = sys.J * sys.Gamma * (sys.J * sys.J) * sys.X * sys.J := by noncomm_ring
      _ = sys.J * sys.Gamma * 1 * sys.X * sys.J := by rw [sys.h_J_sq]
      _ = sys.J * (sys.Gamma * sys.X) * sys.J := by noncomm_ring
  rw [← h1, sys.h_fierz_odd, sys.h_state_even, neg_mul, neg_neg]

/-- **Theorem**: Fierz-Tomita Cosmic Censorship Selection Rule:
    Tr(Γ X) = 0 for any J-odd Fierz channel acting on a J-even state. -/
theorem fierz_tomita_selection_rule :
    trace (sys.Gamma * sys.X) = 0 := by
  have h_prod := fierz_tomita_product_identity sys
  have h_tr : trace (sys.Gamma * sys.X) = - trace (sys.J * (sys.Gamma * sys.X) * sys.J) := by
    nth_rw 1 [h_prod]
    rw [trace_neg]
  have h_cycle : trace (sys.J * (sys.Gamma * sys.X) * sys.J) = trace (sys.Gamma * sys.X) := by
    rw [trace_mul_comm (sys.J * (sys.Gamma * sys.X)) sys.J]
    rw [← mul_assoc, sys.h_J_sq, one_mul]
  rw [h_cycle] at h_tr
  have h_add : trace (sys.Gamma * sys.X) + trace (sys.Gamma * sys.X) = 0 := by
    nth_rw 1 [h_tr]
    rw [neg_add_cancel]
  calc trace (sys.Gamma * sys.X)
    _ = (1 / 2 : ℂ) * (trace (sys.Gamma * sys.X) + trace (sys.Gamma * sys.X)) := by ring
    _ = (1 / 2 : ℂ) * 0 := by rw [h_add]
    _ = 0 := by ring

end FierzTomitaScattering

end FierzModularConjugationBridge
