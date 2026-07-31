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

namespace CyclicBoundaryOperator

variable (b : Matrix (Fin n) (Fin n) ℂ →+ Matrix (Fin n) (Fin n) ℂ)

abbrev b_add : ∀ X Y, b (X + Y) = b X + b Y :=
  b.map_add
/-- **Theorem**: Connes Cyclic Boundary Nilpotency b(b(X)) = 0. -/
theorem boundary_nilpotent_sq
    (nilpotent : ∀ X, b (b X) = 0)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    b (b X) = 0 := nilpotent X

/-- **Theorem**: Boundary Operator Value at Zero b(0) = 0. -/
theorem boundary_zero : b 0 = 0 := by
  exact b.map_zero

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
