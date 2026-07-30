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
structure CyclicBoundaryOperator (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  b : Matrix (Fin n) (Fin n) ℂ →+ Matrix (Fin n) (Fin n) ℂ
  nilpotent : ∀ X, b (b X) = 0

namespace CyclicBoundaryOperator

variable (boundary : CyclicBoundaryOperator n)

abbrev b_add : ∀ X Y, boundary.b (X + Y) = boundary.b X + boundary.b Y :=
  boundary.b.map_add
/-- **Theorem**: Connes Cyclic Boundary Nilpotency b(b(X)) = 0. -/
theorem boundary_nilpotent_sq (X : Matrix (Fin n) (Fin n) ℂ) :
    boundary.b (boundary.b X) = 0 :=
  boundary.nilpotent X

/-- **Theorem**: Boundary Operator Value at Zero b(0) = 0. -/
theorem boundary_zero : boundary.b 0 = 0 := by
  exact boundary.b.map_zero

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
