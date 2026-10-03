import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

open Matrix
open scoped Kronecker

namespace DoubledSylvester

variable {R : Type*} [CommRing R]
variable {N : ℕ}

/-! ### 1. Commutator & Sylvester Matrix Generators -/

/-- The Lie bracket (commutator) [X, Y] = X * Y - Y * X of two square matrices. -/
def bracket {α : Type*} [Fintype α] [DecidableEq α] (X Y : Matrix α α R) : Matrix α α R :=
  X * Y - Y * X

/-- Sylvester Clock operator C: diagonal matrix of phases C_{j,k} = δ_{j,k} ω^j. -/
def sylvesterClock (ω : R) : Matrix (Fin N) (Fin N) R :=
  Matrix.diagonal (fun j => ω ^ (j : ℕ))

/-- Sylvester Shift operator S: cyclic forward permutation S * e_k = e_{k+1 mod N}. -/
def sylvesterShift [NeZero N] : Matrix (Fin N) (Fin N) R :=
  fun j k => if (j : ℕ) = ((k : ℕ) + 1) % N then 1 else 0

/-- Sylvester Adjoint Shift S*: cyclic backward permutation S* * e_k = e_{k-1 mod N}. -/
def sylvesterShiftAdj [NeZero N] : Matrix (Fin N) (Fin N) R :=
  fun j k => if ((j : ℕ) + 1) % N = (k : ℕ) then 1 else 0

/-! ### 2. The Doubled Algebra Embeddings -/

/-- Embedding of the physical algebra sheet M: A ↦ A ⊗ I. -/
def sheet1 (A : Matrix (Fin N) (Fin N) R) : Matrix (Fin N × Fin N) (Fin N × Fin N) R :=
  A ⊗ₖ (1 : Matrix (Fin N) (Fin N) R)

/-- Embedding of the twin commutant sheet M': B ↦ I ⊗ B. -/
def sheet2 (B : Matrix (Fin N) (Fin N) R) : Matrix (Fin N × Fin N) (Fin N × Fin N) R :=
  (1 : Matrix (Fin N) (Fin N) R) ⊗ₖ B

/-! ### 3. Universal Commutant Factorization & Commutation -/

/-- Factorization: (A ⊗ I) * (I ⊗ B) = A ⊗ B. -/
theorem sheet1_mul_sheet2 (A B : Matrix (Fin N) (Fin N) R) :
    sheet1 A * sheet2 B = A ⊗ₖ B := by
  dsimp [sheet1, sheet2]
  rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]

/-- Factorization: (I ⊗ B) * (A ⊗ I) = A ⊗ B. -/
theorem sheet2_mul_sheet1 (A B : Matrix (Fin N) (Fin N) R) :
    sheet2 B * sheet1 A = A ⊗ₖ B := by
  dsimp [sheet1, sheet2]
  rw [← Matrix.mul_kronecker_mul, one_mul, mul_one]

/-- General Commutant Theorem:
Any operator on Sheet 1 strictly commutes with any operator on Sheet 2. -/
theorem commutant_commutes (A B : Matrix (Fin N) (Fin N) R) :
    bracket (sheet1 A) (sheet2 B) = 0 := by
  dsimp [bracket]
  rw [sheet1_mul_sheet2, sheet2_mul_sheet1, sub_self]

/-! ### 4. Exact Proof: [C ⊗ I, I ⊗ S*] = 0 -/

/-- Formal verification that the Clock on Sheet 1 and the Adjoint Shift on Sheet 2 commute. -/
theorem bracket_clock_shiftAdj_eq_zero [NeZero N] (ω : R) :
    bracket (sheet1 (sylvesterClock (N := N) ω))
            (sheet2 (sylvesterShiftAdj (N := N))) = 0 :=
  commutant_commutes (sylvesterClock ω) sylvesterShiftAdj

end DoubledSylvester
