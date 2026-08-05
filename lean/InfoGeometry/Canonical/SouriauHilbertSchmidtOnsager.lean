import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

open Matrix BigOperators

namespace SouriauHilbertSchmidtOnsager

variable {n : ℕ}

/-!
This owner contains only the real Hilbert--Schmidt pairing on the full matrix
algebra.  It makes no Kubo--Mori or BKM claim: no faithful density operator,
matrix functional calculus, operator logarithm, or Kubo--Mori integral occurs
in these definitions.
-/

/-- The full, generally noncommutative real matrix algebra. -/
abbrev MatrixSpace (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The real Hilbert--Schmidt pairing `Tr(AᵀB)`. -/
def hilbertSchmidtPairing (A B : MatrixSpace n) : ℝ :=
  trace (A.transpose * B)

theorem hilbertSchmidtPairing_eq_sum (A B : MatrixSpace n) :
    hilbertSchmidtPairing A B = ∑ i, ∑ j, A j i * B j i := by
  simp [hilbertSchmidtPairing, Matrix.trace, Matrix.mul_apply,
    Matrix.transpose_apply]

/-- Symmetry of the real Hilbert--Schmidt pairing. -/
theorem hilbertSchmidtPairing_symm (A B : MatrixSpace n) :
    hilbertSchmidtPairing A B = hilbertSchmidtPairing B A := by
  rw [hilbertSchmidtPairing_eq_sum, hilbertSchmidtPairing_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Nonnegativity of the Hilbert--Schmidt quadratic form. -/
theorem hilbertSchmidtPairing_nonneg (A : MatrixSpace n) :
    0 ≤ hilbertSchmidtPairing A A := by
  rw [hilbertSchmidtPairing_eq_sum]
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  simpa [pow_two] using sq_nonneg (A j i)

/-- A finite matrix metriplectic packet whose dissipative kernel is measured
by the Hilbert--Schmidt pairing. -/
structure HilbertSchmidtMetriplecticSystem (n : ℕ) where
  H : MatrixSpace n
  rho : MatrixSpace n
  h_H_kernel :
    ∀ A : MatrixSpace n,
      hilbertSchmidtPairing A (H * rho - rho * H) = 0

/-- Energy conservation supplied by the stated Hilbert--Schmidt kernel law. -/
theorem hilbertSchmidt_energy_conservation
    (sys : HilbertSchmidtMetriplecticSystem n) :
    hilbertSchmidtPairing
        (sys.H * sys.rho - sys.rho * sys.H) sys.H = 0 := by
  rw [hilbertSchmidtPairing_symm]
  exact sys.h_H_kernel sys.H

/-- The Hilbert--Schmidt entropy-direction quadratic form is nonnegative. -/
theorem hilbertSchmidt_dissipation_nonneg (dS : MatrixSpace n) :
    0 ≤ hilbertSchmidtPairing dS dS :=
  hilbertSchmidtPairing_nonneg dS

/-- Packaged Hilbert--Schmidt Onsager summary: symmetry, dissipation
nonnegativity, and the kernel-based energy conservation law. -/
theorem hilbertSchmidt_metriplectic_summary
    (sys : HilbertSchmidtMetriplecticSystem n) :
    ((∀ A B : MatrixSpace n,
        hilbertSchmidtPairing A B = hilbertSchmidtPairing B A) ∧
      (∀ A : MatrixSpace n, 0 ≤ hilbertSchmidtPairing A A)) ∧
    (hilbertSchmidtPairing
        (sys.H * sys.rho - sys.rho * sys.H) sys.H = 0) := by
  constructor
  · constructor
    · intro A B
      exact hilbertSchmidtPairing_symm A B
    · intro A
      exact hilbertSchmidtPairing_nonneg A
  · exact hilbertSchmidt_energy_conservation sys

end SouriauHilbertSchmidtOnsager
