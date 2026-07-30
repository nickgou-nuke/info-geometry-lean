import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.POM

/-- A concrete order-one recurrence sample: the geometric sequence `2^n`. -/
def xiMinimalRecurrenceSequence (n : ℕ) : ℚ := 2 ^ n

/-- The `d = 1` Hankel block attached to the first sample `a₀ = 1`. -/
def xiMinimalRecurrenceHankelBlock : Matrix (Fin 1) (Fin 1) ℚ := 1

/-- The right-hand side `b = (a₁)`. -/
def xiMinimalRecurrenceRhs : Fin 1 → ℚ := ![xiMinimalRecurrenceSequence 1]

/-- The coefficient vector `c = (2)` for the recurrence `a_{m+1} = 2 a_m`. -/
def xiMinimalRecurrenceCoeffs : Fin 1 → ℚ := ![(2 : ℚ)]

/-- For the identity `1 × 1` Hankel block, the inverse matrix is again the identity. -/
def xiMinimalRecurrenceHankelInverse : Matrix (Fin 1) (Fin 1) ℚ := 1

/-- Paper-facing concrete `d = 1` instance of the minimal-recurrence inversion formula:
the first Hankel block is invertible and the coefficient vector is exactly `H⁻¹ b`.
    cor:xi-hankel-minimal-recurrence-inversion-formula -/
theorem paper_xi_hankel_minimal_recurrence_inversion_formula :
    (∀ n : ℕ,
      xiMinimalRecurrenceSequence (n + 1) =
        2 * xiMinimalRecurrenceSequence n) ∧
      Matrix.det xiMinimalRecurrenceHankelBlock ≠ 0 ∧
      xiMinimalRecurrenceHankelInverse.mulVec xiMinimalRecurrenceRhs =
        xiMinimalRecurrenceCoeffs := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simp [xiMinimalRecurrenceSequence, pow_succ, mul_comm]
  · native_decide
  · native_decide

end Omega.POM
