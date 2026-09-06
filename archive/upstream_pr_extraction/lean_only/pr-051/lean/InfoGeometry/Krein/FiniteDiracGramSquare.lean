import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# Finite Dirac/Gram square

The universal finite algebraic wire from a rectangular operator to its two
Gram operators.  This owner proves only the block-matrix identities; polar,
KAN, current, and colimit compatibility require separate hypotheses.
-/

namespace InfoGeometry.Krein.FiniteDiracGramSquare

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def dirac (T : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  Matrix.fromBlocks 0 T Tᴴ 0

def qPlus (T : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  Matrix.fromBlocks 0 T 0 0

def qMinus (T : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  Matrix.fromBlocks 0 0 Tᴴ 0

theorem qPlus_sq (T : Matrix m n ℂ) : qPlus T * qPlus T = 0 := by
  rw [qPlus, Matrix.fromBlocks_multiply]
  simp

theorem qMinus_sq (T : Matrix m n ℂ) : qMinus T * qMinus T = 0 := by
  rw [qMinus, Matrix.fromBlocks_multiply]
  simp

theorem qMinus_eq_qPlus_conjTranspose (T : Matrix m n ℂ) :
    (qPlus T)ᴴ = qMinus T := by
  ext i j <;> cases i <;> cases j <;>
    simp [qPlus, qMinus, Matrix.fromBlocks]

theorem qPlus_add_qMinus_eq_dirac (T : Matrix m n ℂ) :
    qPlus T + qMinus T = dirac T := by
  ext i j <;> cases i <;> cases j <;>
    simp [qPlus, qMinus, dirac, Matrix.fromBlocks]

theorem qPlus_qMinus_add_qMinus_qPlus_eq_dirac_sq (T : Matrix m n ℂ) :
    qPlus T * qMinus T + qMinus T * qPlus T = dirac T * dirac T := by
  calc
    qPlus T * qMinus T + qMinus T * qPlus T =
        (qPlus T + qMinus T) * (qPlus T + qMinus T) -
          qPlus T * qPlus T - qMinus T * qMinus T := by
            noncomm_ring
    _ = (qPlus T + qMinus T) * (qPlus T + qMinus T) := by
          rw [qPlus_sq, qMinus_sq]
          simp
    _ = dirac T * dirac T := by rw [qPlus_add_qMinus_eq_dirac T]

def leftGram (T : Matrix m n ℂ) : Matrix m m ℂ := T * Tᴴ

def rightGram (T : Matrix m n ℂ) : Matrix n n ℂ := Tᴴ * T

theorem qPlus_mul_qMinus (T : Matrix m n ℂ) :
    qPlus T * qMinus T =
      Matrix.fromBlocks (leftGram T) 0 0 0 := by
  rw [qPlus, qMinus, leftGram, Matrix.fromBlocks_multiply]
  simp

theorem qMinus_mul_qPlus (T : Matrix m n ℂ) :
    qMinus T * qPlus T =
      Matrix.fromBlocks 0 0 0 (rightGram T) := by
  rw [qMinus, qPlus, rightGram, Matrix.fromBlocks_multiply]
  simp

theorem leftGram_isHermitian (T : Matrix m n ℂ) :
    (leftGram T)ᴴ = leftGram T := by
  simp [leftGram]

theorem rightGram_isHermitian (T : Matrix m n ℂ) :
    (rightGram T)ᴴ = rightGram T := by
  simp [rightGram]

theorem rightGram_posSemidef (T : Matrix m n ℂ) :
    (rightGram T).PosSemidef := by
  exact posSemidef_conjTranspose_mul_self T

theorem leftGram_posSemidef (T : Matrix m n ℂ) :
    (leftGram T).PosSemidef := by
  exact posSemidef_self_mul_conjTranspose T

theorem rightGram_trace_nonneg (T : Matrix m n ℂ) :
    0 ≤ Matrix.trace (rightGram T) := by
  exact (rightGram_posSemidef T).trace_nonneg

theorem leftGram_trace_nonneg (T : Matrix m n ℂ) :
    0 ≤ Matrix.trace (leftGram T) := by
  exact (leftGram_posSemidef T).trace_nonneg

theorem rightGram_conjTranspose (T : Matrix m n ℂ) :
    rightGram Tᴴ = leftGram T := by
  simp [rightGram, leftGram]

theorem leftGram_conjTranspose (T : Matrix m n ℂ) :
    leftGram Tᴴ = rightGram T := by
  simp [rightGram, leftGram]

theorem trace_leftGram_eq_trace_rightGram (T : Matrix m n ℂ) :
    Matrix.trace (leftGram T) = Matrix.trace (rightGram T) := by
  exact Matrix.trace_mul_comm T Tᴴ

theorem dirac_isHermitian (T : Matrix m n ℂ) :
    (dirac T)ᴴ = dirac T := by
  ext i j <;> cases i <;> cases j <;>
    simp [dirac, Matrix.fromBlocks]

theorem dirac_sq (T : Matrix m n ℂ) :
    dirac T * dirac T =
      Matrix.fromBlocks (leftGram T) 0 0 (rightGram T) := by
  rw [dirac, leftGram, rightGram, Matrix.fromBlocks_multiply]
  simp

theorem dirac_sq_isHermitian (T : Matrix m n ℂ) :
    (dirac T * dirac T)ᴴ = dirac T * dirac T := by
  simp only [Matrix.conjTranspose_mul, dirac_isHermitian]

theorem trace_dirac_sq (T : Matrix m n ℂ) :
    Matrix.trace (dirac T * dirac T) =
      Matrix.trace (leftGram T) + Matrix.trace (rightGram T) := by
  rw [dirac_sq]
  unfold Matrix.trace
  rw [Fintype.sum_sum_type]
  simp [Matrix.fromBlocks]

theorem trace_dirac_sq_eq_two_rightGram (T : Matrix m n ℂ) :
    Matrix.trace (dirac T * dirac T) = 2 * Matrix.trace (rightGram T) := by
  rw [trace_dirac_sq, trace_leftGram_eq_trace_rightGram]
  ring

theorem trace_dirac_sq_nonneg (T : Matrix m n ℂ) :
    0 ≤ Matrix.trace (dirac T * dirac T) := by
  rw [trace_dirac_sq]
  exact add_nonneg (leftGram_posSemidef T).trace_nonneg
    (rightGram_posSemidef T).trace_nonneg

theorem dirac_sq_left_block (T : Matrix m n ℂ) (i j : m) :
    (dirac T * dirac T) (Sum.inl i) (Sum.inl j) =
      (leftGram T) i j := by
  rw [dirac_sq]
  rfl

theorem dirac_sq_right_block (T : Matrix m n ℂ) (i j : n) :
    (dirac T * dirac T) (Sum.inr i) (Sum.inr j) =
      (rightGram T) i j := by
  rw [dirac_sq]
  rfl

end

end InfoGeometry.Krein.FiniteDiracGramSquare
