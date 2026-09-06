import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix BigOperators

namespace HilbertSchmidtMatrix

variable {n : ℕ}

/-- Real Hilbert-Schmidt Inner Product on n × n real matrices: <A, B>_HS = Tr(Aᵀ B). -/
def hilbertSchmidtPairing (A B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  trace (A.transpose * B)

/-- **Theorem**: Hilbert-Schmidt Pairing Sum Formula: <A, B>_HS = ∑_{i,j} A_ji * B_ji. -/
theorem hilbertSchmidtPairing_eq_sum (A B : Matrix (Fin n) (Fin n) ℝ) :
    hilbertSchmidtPairing A B = ∑ i, ∑ j, A j i * B j i := by
  simp [hilbertSchmidtPairing, Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]

/-- **Theorem**: Hilbert-Schmidt Metric Symmetry: <A, B>_HS = <B, A>_HS. -/
theorem hilbertSchmidt_symmetry (A B : Matrix (Fin n) (Fin n) ℝ) :
    hilbertSchmidtPairing A B = hilbertSchmidtPairing B A := by
  rw [hilbertSchmidtPairing_eq_sum, hilbertSchmidtPairing_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Theorem**: Hilbert-Schmidt Metric Positive Semi-Definiteness: <A, A>_HS ≥ 0. -/
theorem hilbertSchmidt_pos_semidef (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ hilbertSchmidtPairing A A := by
  rw [hilbertSchmidtPairing_eq_sum]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  simpa [pow_two] using sq_nonneg (A j i)

/-- Hilbert-Schmidt Metriplectic System with Hamiltonian matrix H and state matrix rho. -/
structure HilbertSchmidtMetriplecticSystem (n : ℕ) where
  H : Matrix (Fin n) (Fin n) ℝ
  rho : Matrix (Fin n) (Fin n) ℝ
  h_kernel : ∀ A : Matrix (Fin n) (Fin n) ℝ, hilbertSchmidtPairing A (H * rho - rho * H) = 0

/-- **Theorem**: Hilbert-Schmidt Energy Conservation under Lie bracket kernel. -/
theorem hilbertSchmidt_energy_conservation (sys : HilbertSchmidtMetriplecticSystem n) :
    hilbertSchmidtPairing (sys.H * sys.rho - sys.rho * sys.H) sys.H = 0 := by
  rw [hilbertSchmidt_symmetry]
  exact sys.h_kernel sys.H

/-- **Theorem**: Hilbert-Schmidt Entropy Dissipation Non-Negativity. -/
theorem hilbertSchmidt_dissipation_nonneg (dS : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ hilbertSchmidtPairing dS dS :=
  hilbertSchmidt_pos_semidef dS

end HilbertSchmidtMatrix
