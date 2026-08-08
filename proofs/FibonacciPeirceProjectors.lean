import Mathlib
import proofs.CuntzMatrixCorner

open Matrix Real Complex

namespace FibonacciPeirceProjectors

/-- The real local Fibonacci matrix -/
def fibonacciMatrixReal : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 1],
    ![1, 1]]

/-- Eigenvalues: Golden ratio and its conjugate -/
def phi : ℝ := (1 + Real.sqrt 5) / 2
def tau : ℝ := (Real.sqrt 5 - 1) / 2

/-- Spectral Peirce Projectors -/
def fibonacciPeircePlus : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt 5)⁻¹ • (fibonacciMatrixReal + tau • (1 : Matrix (Fin 2) (Fin 2) ℝ))

def fibonacciPeirceMinus : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt 5)⁻¹ • (phi • (1 : Matrix (Fin 2) (Fin 2) ℝ) - fibonacciMatrixReal)

lemma sqrt5_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)

-- Helper to expand matrix operations on 2x2 matrices
macro "fib_simp" : tactic =>
  `(tactic| (
    ext i j
    fin_cases i <;> fin_cases j <;> (
      dsimp [fibonacciPeircePlus, fibonacciPeirceMinus, fibonacciMatrixReal, phi, tau]
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
            Matrix.one_apply, Matrix.transpose_apply, Fin.sum_univ_two,
            mul_add, add_mul]
    )
  ))

-- Now we can prove everything by letting ring_nf expand and then substituting sqrt 5 ^ 2 = 5
macro "fib_proof" : tactic =>
  `(tactic| (
    fib_simp
    have h : (Real.sqrt 5) ^ 2 = 5 := sqrt5_sq
    try nlinarith [h]
  ))

theorem fibonacciPeircePlus_idempotent :
    fibonacciPeircePlus * fibonacciPeircePlus = fibonacciPeircePlus := by
  fib_proof

theorem fibonacciPeirceMinus_idempotent :
    fibonacciPeirceMinus * fibonacciPeirceMinus = fibonacciPeirceMinus := by
  fib_proof

theorem fibonacciPeircePlus_selfAdjoint :
    fibonacciPeircePlusᵀ = fibonacciPeircePlus := by
  fib_proof

theorem fibonacciPeirceMinus_selfAdjoint :
    fibonacciPeirceMinusᵀ = fibonacciPeirceMinus := by
  fib_proof

theorem fibonacciPeirce_orthogonal :
    fibonacciPeircePlus * fibonacciPeirceMinus = 0 := by
  fib_proof

theorem fibonacciPeirce_sum :
    fibonacciPeircePlus + fibonacciPeirceMinus = 1 := by
  fib_proof

theorem fibonacciMatrix_mul_peircePlus :
    fibonacciMatrixReal * fibonacciPeircePlus = phi • fibonacciPeircePlus := by
  fib_proof

theorem fibonacciMatrix_mul_peirceMinus :
    fibonacciMatrixReal * fibonacciPeirceMinus = (-tau) • fibonacciPeirceMinus := by
  fib_proof

/-- Cuntz images of the Peirce projectors -/
variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (S : Fin 2 → A) [CuntzMatrixCorner.CuntzO2 (S 0) (S 1)]

def ofRealMatrix (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (M i j : ℂ)

def CuntzPeircePlus : A :=
  CuntzMatrixCorner.cuntzCornerMap S (ofRealMatrix fibonacciPeircePlus)

def CuntzPeirceMinus : A :=
  CuntzMatrixCorner.cuntzCornerMap S (ofRealMatrix fibonacciPeirceMinus)

theorem ofRealMatrix_mul (M N : Matrix (Fin 2) (Fin 2) ℝ) :
    ofRealMatrix (M * N) = ofRealMatrix M * ofRealMatrix N := by
  ext i j
  dsimp [ofRealMatrix, Matrix.mul_apply]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  push_cast
  rfl

theorem ofRealMatrix_add (M N : Matrix (Fin 2) (Fin 2) ℝ) :
    ofRealMatrix (M + N) = ofRealMatrix M + ofRealMatrix N := by
  ext i j
  dsimp [ofRealMatrix, Matrix.add_apply]
  push_cast
  rfl

theorem ofRealMatrix_zero :
    ofRealMatrix 0 = 0 := by
  ext i j; rfl

theorem ofRealMatrix_one :
    ofRealMatrix 1 = 1 := by
  ext i j
  dsimp [ofRealMatrix, Matrix.one_apply]
  split_ifs <;> simp

theorem CuntzPeirce_orthogonal :
    CuntzPeircePlus S * CuntzPeirceMinus S = 0 := by
  dsimp [CuntzPeircePlus, CuntzPeirceMinus]
  rw [← CuntzMatrixCorner.cuntzCornerMap_mul S]
  rw [← ofRealMatrix_mul]
  rw [fibonacciPeirce_orthogonal]
  rw [ofRealMatrix_zero]
  -- We don't have cuntzCornerMap_zero? We can just use map_zero, but cuntzCornerMap is not a StarAlgHom yet
  -- Wait, I didn't prove cuntzCornerMap_zero in CuntzMatrixCorner.lean!
  -- Let's just dsimp and prove it.
  dsimp [CuntzMatrixCorner.cuntzCornerMap]
  simp

theorem CuntzPeirce_sum :
    CuntzPeircePlus S + CuntzPeirceMinus S = 1 := by
  dsimp [CuntzPeircePlus, CuntzPeirceMinus]
  rw [← CuntzMatrixCorner.cuntzCornerMap_add]
  rw [← ofRealMatrix_add]
  rw [fibonacciPeirce_sum]
  rw [ofRealMatrix_one]
  exact CuntzMatrixCorner.cuntzCornerMap_one S

end FibonacciPeirceProjectors
