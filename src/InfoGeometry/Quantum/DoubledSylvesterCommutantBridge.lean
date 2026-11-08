import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

open Matrix
open scoped Kronecker

namespace DoubledSylvester

variable {R : Type*} [CommRing R]
variable {N : ℕ}

/-! ### Commutators and finite matrix generators

The parameter `ω` is arbitrary in the coefficient ring; no root-of-unity or
unitarity property is assumed. -/

/-- The Lie bracket (commutator) [X, Y] = X * Y - Y * X of two square matrices. -/
def bracket {α : Type*} [Fintype α] [DecidableEq α] (X Y : Matrix α α R) : Matrix α α R :=
  X * Y - Y * X

/-- Diagonal power matrix `C`, with diagonal entries `ω ^ j`. -/
def sylvesterClock (ω : R) : Matrix (Fin N) (Fin N) R :=
  Matrix.diagonal (fun j => ω ^ (j : ℕ))

/-- Sylvester Shift operator S: cyclic forward permutation S * e_k = e_{k+1 mod N}. -/
def sylvesterShift [NeZero N] : Matrix (Fin N) (Fin N) R :=
  fun j k => if (j : ℕ) = ((k : ℕ) + 1) % N then 1 else 0

/-- Transpose of the cyclic forward permutation matrix. -/
def sylvesterShiftTranspose [NeZero N] : Matrix (Fin N) (Fin N) R :=
  fun j k => if ((j : ℕ) + 1) % N = (k : ℕ) then 1 else 0

/-! ### The two tensor-factor embeddings -/

/-- Embedding of the first tensor factor, `A ↦ A ⊗ I`. -/
def sheet1 (A : Matrix (Fin N) (Fin N) R) : Matrix (Fin N × Fin N) (Fin N × Fin N) R :=
  A ⊗ₖ (1 : Matrix (Fin N) (Fin N) R)

/-- Embedding of the second tensor factor, `B ↦ I ⊗ B`. -/
def sheet2 (B : Matrix (Fin N) (Fin N) R) : Matrix (Fin N × Fin N) (Fin N × Fin N) R :=
  (1 : Matrix (Fin N) (Fin N) R) ⊗ₖ B

/-! ### Tensor-factor products and commutation -/

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

/-! The result is an algebraic tensor-factor commutation identity. It does not
formalize Tomita–Takesaki theory or a Hilbert-space adjoint. -/

/-- The diagonal power matrix on the first factor commutes with the
transpose permutation matrix on the second factor. -/
theorem bracket_clock_shiftTranspose_eq_zero [NeZero N] (ω : R) :
    bracket (sheet1 (sylvesterClock (N := N) ω))
            (sheet2 (sylvesterShiftTranspose (N := N))) = 0 :=
  commutant_commutes (sylvesterClock ω) sylvesterShiftTranspose

end DoubledSylvester
