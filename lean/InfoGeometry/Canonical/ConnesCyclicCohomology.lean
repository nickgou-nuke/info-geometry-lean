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

namespace ConnesCyclic

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Cyclic Cochain Boundary Operator b: C^k → C^(k+1) satisfying b² = 0. -/
abbrev CyclicBoundaryOperator (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] : Type _ :=
  Σ' b : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    (∀ X Y, b (X + Y) = b X + b Y) ∧
      ∀ X, b (b X) = 0

namespace CyclicBoundaryOperator

variable (boundary : CyclicBoundaryOperator n)

abbrev b : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := boundary.1
abbrev b_add : ∀ X Y, boundary.b (X + Y) = boundary.b X + boundary.b Y := boundary.2.1
abbrev b_nilpotent : ∀ X, boundary.b (boundary.b X) = 0 := boundary.2.2

/-- **Theorem**: Connes Cyclic Boundary Nilpotency b(b(X)) = 0. -/
theorem boundary_nilpotent_sq (X : Matrix (Fin n) (Fin n) ℂ) :
    boundary.b (boundary.b X) = 0 :=
  boundary.b_nilpotent X

/-- **Theorem**: Boundary Operator Value at Zero b(0) = 0. -/
theorem boundary_zero : boundary.b 0 = 0 := by
  have h : boundary.b 0 = boundary.b 0 + boundary.b 0 := by
    have h_add := boundary.b_add 0 0
    rw [add_zero] at h_add
    exact h_add
  have h_sub : boundary.b 0 - boundary.b 0 = (boundary.b 0 + boundary.b 0) - boundary.b 0 := by rw [← h]
  have h_lh : boundary.b 0 - boundary.b 0 = 0 := sub_self (boundary.b 0)
  have h_rh : (boundary.b 0 + boundary.b 0) - boundary.b 0 = boundary.b 0 := by noncomm_ring
  rw [h_lh, h_rh] at h_sub
  exact h_sub.symm

/-- Connes Cyclic 1-Cochain Pairing φ(a, b) = Tr(a * b). -/
def cyclicOneCochainPairing (a b : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  trace (a * b)

/-- **Theorem**: Cyclic 1-Cochain Invariance under Shift: φ(a, b) = φ(b, a). -/
theorem cyclic_one_cochain_shift (a b : Matrix (Fin n) (Fin n) ℂ) :
    cyclicOneCochainPairing a b = cyclicOneCochainPairing b a := by
  dsimp [cyclicOneCochainPairing]
  exact trace_mul_comm a b

end CyclicBoundaryOperator

end ConnesCyclic
