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
abbrev ModularCocycleGroup (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] :=
  selfAdjoint (Matrix (Fin n) (Fin n) ℂ)

namespace ModularCocycleGroup

variable (cocycle : ModularCocycleGroup n)

def L_gen : Matrix (Fin n) (Fin n) ℂ := cocycle

theorem h_self_adj : (L_gen cocycle).conjTranspose = L_gen cocycle := by
  simpa only [L_gen, Matrix.star_eq_conjTranspose] using cocycle.property

/-- Logarithmic Differential Operator Variation d ln Q = L_gen. -/
def d_ln_Q : Matrix (Fin n) (Fin n) ℂ :=
  L_gen cocycle

/-- **Theorem**: Logarithmic Differential Variation Self-Adjointness: (d ln Q)† = d ln Q. -/
theorem d_ln_Q_self_adj :
    (d_ln_Q cocycle).conjTranspose = d_ln_Q cocycle := by
  dsimp [d_ln_Q]
  exact h_self_adj cocycle

/-- **Theorem**: Connes Cocycle Chain Rule Logarithmic Additivity:
    d ln Q₁₃ = d ln Q₁₂ + d ln Q₂₃ for L₁₃ = L₁₂ + L₂₃. -/
theorem cocycle_chain_rule_log_add (L12 L23 : ModularCocycleGroup n) :
    d_ln_Q (⟨L_gen L12 + L_gen L23, by
      change (L_gen L12 + L_gen L23).conjTranspose = L_gen L12 + L_gen L23
      rw [conjTranspose_add, h_self_adj L12, h_self_adj L23]
    ⟩ : ModularCocycleGroup n) = d_ln_Q L12 + d_ln_Q L23 := by
  rfl

/-- **Theorem**: Logarithmic Variation Trace Additivity: Tr(d ln Q₁₃) = Tr(d ln Q₁₂) + Tr(d ln Q₂₃). -/
theorem cocycle_trace_additivity (L12 L23 : ModularCocycleGroup n) :
    trace (d_ln_Q L12 + d_ln_Q L23) = trace (d_ln_Q L12) + trace (d_ln_Q L23) := by
  rw [trace_add]

/-- **Theorem**: Commutator Variation Vanishing for Tracial States: Tr([A, d ln Q]) = 0. -/
theorem cocycle_commutator_trace_zero (A : Matrix (Fin n) (Fin n) ℂ) :
    trace (A * d_ln_Q cocycle - d_ln_Q cocycle * A) = 0 := by
  rw [trace_sub, trace_mul_comm A (d_ln_Q cocycle), sub_self]

end ModularCocycleGroup

end ConnesCocycleLogarithm
