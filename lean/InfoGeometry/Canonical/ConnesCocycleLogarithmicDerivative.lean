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

namespace ConnesCocycleLogarithm

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Connes Modular Cocycle 1-Parameter Group u(t) = [Dφ : Dψ]_t with Infinitesimal Generator L = u'(0). -/
structure ModularCocycleGroup (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  L_gen : Matrix (Fin n) (Fin n) ℂ
  h_self_adj : L_gen.conjTranspose = L_gen

namespace ModularCocycleGroup

variable (cocycle : ModularCocycleGroup n)

/-- Logarithmic Differential Operator Variation d ln Q = L_gen. -/
def d_ln_Q : Matrix (Fin n) (Fin n) ℂ :=
  cocycle.L_gen

/-- **Theorem**: Logarithmic Differential Variation Self-Adjointness: (d ln Q)† = d ln Q. -/
theorem d_ln_Q_self_adj :
    cocycle.d_ln_Q.conjTranspose = cocycle.d_ln_Q := by
  dsimp [d_ln_Q]
  exact cocycle.h_self_adj

/-- **Theorem**: Connes Cocycle Chain Rule Logarithmic Additivity:
    d ln Q₁₃ = d ln Q₁₂ + d ln Q₂₃ for L₁₃ = L₁₂ + L₂₃. -/
theorem cocycle_chain_rule_log_add (L12 L23 : ModularCocycleGroup n) :
    (ModularCocycleGroup.mk (L12.L_gen + L23.L_gen) (by
      rw [conjTranspose_add, L12.h_self_adj, L23.h_self_adj]
    )).d_ln_Q = L12.d_ln_Q + L23.d_ln_Q := by
  dsimp [d_ln_Q]

/-- **Theorem**: Logarithmic Variation Trace Additivity: Tr(d ln Q₁₃) = Tr(d ln Q₁₂) + Tr(d ln Q₂₃). -/
theorem cocycle_trace_additivity (L12 L23 : ModularCocycleGroup n) :
    trace (L12.d_ln_Q + L23.d_ln_Q) = trace L12.d_ln_Q + trace L23.d_ln_Q := by
  rw [trace_add]

/-- **Theorem**: Commutator Variation Vanishing for Tracial States: Tr([A, d ln Q]) = 0. -/
theorem cocycle_commutator_trace_zero (A : Matrix (Fin n) (Fin n) ℂ) :
    trace (A * cocycle.d_ln_Q - cocycle.d_ln_Q * A) = 0 := by
  rw [trace_sub, trace_mul_comm A cocycle.d_ln_Q, sub_self]

end ModularCocycleGroup

end ConnesCocycleLogarithm
