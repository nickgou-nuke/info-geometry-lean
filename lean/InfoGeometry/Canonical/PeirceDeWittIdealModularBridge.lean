import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
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

namespace PeirceDeWittIdeal

/-- Upper Peirce Projector p_+ = diag(1, 0) in M₂ (ℂ). -/
def pPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0;
     0, 0]

/-- Lower Peirce Projector p_- = diag(0, 1) in M₂ (ℂ). -/
def pMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0;
     0, 1]

namespace PeirceDeWittIdeal

/-- **Theorem**: Upper Peirce Projector Idempotency: p_+² = p_+. -/
theorem pPlus_idempotent : pPlus * pPlus = pPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [pPlus, Matrix.mul_apply, Fin.sum_univ_two]
  }

/-- **Theorem**: Lower Peirce Projector Idempotency: p_-² = p_-. -/
theorem pMinus_idempotent : pMinus * pMinus = pMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [pMinus, Matrix.mul_apply, Fin.sum_univ_two]
  }

/-- **Theorem**: Peirce Projector Orthogonality: p_+ * p_- = 0. -/
theorem pPlus_pMinus_orthogonal : pPlus * pMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [pPlus, pMinus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply]
  }

/-- **Theorem**: Peirce Identity Resolution: p_+ + p_- = 1. -/
theorem pPlus_add_pMinus_eq_one : pPlus + pMinus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [pPlus, pMinus, Matrix.add_apply, Matrix.one_apply]
  }

/-- **Theorem**: DeWitt Body-Soul Trace Resolution: Tr(p_+) = 1 and Tr(p_-) = 1. -/
theorem peirce_trace_resolution : trace pPlus = 1 ∧ trace pMinus = 1 := by
  constructor <;> simp [pPlus, pMinus, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

end PeirceDeWittIdeal

end PeirceDeWittIdeal
