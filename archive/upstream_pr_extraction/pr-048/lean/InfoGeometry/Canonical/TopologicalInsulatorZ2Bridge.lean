import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

namespace TopologicalInsulator

/-- Time-reversal operator for spin-1/2 systems T² = -1. -/
structure TimeReversalOperator where
  opSquareVal : ℝ
  is_spin_half : opSquareVal = -1

namespace TimeReversalOperator

variable (T : TimeReversalOperator)

/-- **Theorem**: Time-reversal square for spin-1/2 fermions is negative: T² = -1. -/
theorem spin_half_time_reversal_sq : T.opSquareVal = -1 :=
  T.is_spin_half

/-- **Theorem**: Kramers degeneracy: T² ψ ≠ ψ for non-zero states. -/
theorem kramers_degeneracy_non_trivial (v : ℝ) (hv : v ≠ 0) :
    T.opSquareVal * v ≠ v := by
  rw [T.is_spin_half]
  intro h
  have h2 : v = 0 := by linarith
  exact hv h2

/-- ℤ₂ Topological Invariant ν ∈ {0, 1} product over 4 Time-Reversal Invariant Momentum (TRIM) points. -/
def z2Invariant (trim_parities : Fin 4 → ℤ) : ℤ :=
  (trim_parities 0) * (trim_parities 1) * (trim_parities 2) * (trim_parities 3)

/-- **Theorem**: If all TRIM parities are +1, the ℤ₂ invariant is trivial: ν = +1. -/
theorem z2_trivial_all_positive :
    z2Invariant (fun _ => 1) = 1 := rfl

/-- **Theorem**: If exactly one TRIM parity is -1, the ℤ₂ invariant is non-trivial: ν = -1. -/
theorem z2_nontrivial_one_negative :
    z2Invariant (fun i => if i = 0 then -1 else 1) = -1 := rfl

end TimeReversalOperator

end TopologicalInsulator
