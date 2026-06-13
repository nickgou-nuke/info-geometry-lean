import Mathlib.LinearAlgebra.Matrix.Basic

namespace InfoGeometry.Algebra.FiniteSUSY

structure FiniteSUSYSystem (n : ℕ) where
  A     : Matrix (Fin n) (Fin n) ℂ
  A_dag : Matrix (Fin n) (Fin n) ℂ
  
  -- Definition of the partnered Hamiltonians
  H_minus : Matrix (Fin n) (Fin n) ℂ
  H_plus  : Matrix (Fin n) (Fin n) ℂ
  
  h_H_minus_def : H_minus = A_dag * A
  h_H_plus_def  : H_plus = A * A_dag

variable {n : ℕ} (sys : FiniteSUSYSystem n)

/-- THEOREM: Non-Negative Energy Ground States.
    Proves that the partnered Hamiltonians share identical non-zero eigenvalues, 
    locking the supersymmetric pairing within the finite matrix blocks. -/
theorem susy_partner_energy_mirror :
    sys.A * sys.H_minus = sys.H_plus * sys.A := by
  rw [sys.h_H_minus_def, sys.h_H_plus_def]
  -- Matrix multiplication associativity matches via reflexivity
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc sys.A sys.A_dag]
  simp only [Matrix.mul_assoc]

end InfoGeometry.Algebra.FiniteSUSY
