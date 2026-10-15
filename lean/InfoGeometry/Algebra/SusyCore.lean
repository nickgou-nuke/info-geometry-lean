import InfoGeometry.Algebra.SpinCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Mul

open Matrix

namespace InfoGeometry.Algebra.SusyCore

open InfoGeometry.Algebra.SpinCore

/-- Fermionic Supercharge operator A -/
def Supercharge_A : Matrix (Fin 2) (Fin 2) ℚ := J_plus

/-- Conjugate Supercharge operator A† -/
def Supercharge_Adjoint : Matrix (Fin 2) (Fin 2) ℚ := J_minus

/-- Bosonic Partner Hamiltonian H₋ = A†A -/
def H_minus : Matrix (Fin 2) (Fin 2) ℚ := Supercharge_Adjoint * Supercharge_A

/-- Fermionic Partner Hamiltonian H₊ = AA† -/
def H_plus : Matrix (Fin 2) (Fin 2) ℚ := Supercharge_A * Supercharge_Adjoint

/-- Theorem: Supersymmetric Nilpotency Condition -/
theorem supercharge_nilpotent : Supercharge_A * Supercharge_A = 0 := j_plus_nilpotent

/-- The finite Witten Index Trace counting bosonic minus fermionic states. -/
def witten_index_trace : ℚ := (H_minus - H_plus) 0 0 + (H_minus - H_plus) 1 1

/-- Theorem: Perfect Supersymmetric State Balance -/
theorem witten_index_cancellation : witten_index_trace = 0 := by
  change (∑ k : Fin 2, J_minus 0 k * J_plus k 0) - (∑ k : Fin 2, J_plus 0 k * J_minus k 0) +
    ((∑ k : Fin 2, J_minus 1 k * J_plus k 1) - (∑ k : Fin 2, J_plus 1 k * J_minus k 1)) = 0
  simp [Fin.sum_univ_two, J_plus, J_minus]

end InfoGeometry.Algebra.SusyCore
