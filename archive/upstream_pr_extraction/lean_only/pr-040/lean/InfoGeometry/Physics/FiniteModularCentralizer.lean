import InfoGeometry.Physics.FiniteRelativeModularLogBridge
import Mathlib.Data.Matrix.Basic

noncomputable section

/-!
# Finite diagonal modular centralizer

This owner isolates the zero-frequency sector of a finite diagonal state.
It is a matrix-unit statement only: no Tomita standard form or generic
functional calculus is introduced.
-/

namespace InfoGeometry.Physics.FiniteModularCentralizer

open InfoGeometry.Physics.FiniteRelativeModularLogBridge
open InfoGeometry.Physics.FiniteRelativeModularOperator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixUnit (i j : ι) : Matrix ι ι ℝ :=
  fun k l => if k = i then if l = j then 1 else 0 else 0

def diagonalCentralizer (p : ι → ℝ) : Set (Matrix ι ι ℝ) :=
  {A | Matrix.diagonal p * A = A * Matrix.diagonal p}

def realMatrixUnit (i j : ι) : Matrix ι ι ℝ :=
  fun k l => if k = i then if l = j then 1 else 0 else 0

theorem matrixUnit_mem_diagonalCentralizer_iff
    (p : ι → ℝ) (i j : ι) :
    realMatrixUnit i j ∈ diagonalCentralizer p ↔ p i = p j := by
  constructor
  · intro h
    have hij := congr_fun (congr_fun h i) j
    simpa [diagonalCentralizer, realMatrixUnit, Matrix.diagonal_mul,
      Matrix.mul_diagonal] using hij
  · intro hp
    ext k l
    by_cases hki : k = i <;> by_cases hlj : l = j <;>
      simp [diagonalCentralizer, realMatrixUnit, Matrix.diagonal_mul,
        Matrix.mul_diagonal, hki, hlj, hp]

theorem relativeLogEigenvalue_eq_zero_iff
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    relativeLogEigenvalue p q = 0 ↔ p = q := by
  rw [relativeLogEigenvalue_eq_neg_log_ratio hp hq]
  constructor
  · intro h
    have hratio : Real.log (p / q) = 0 := by linarith
    have hlog : Real.log (p / q) = Real.log 1 := by simpa using hratio
    have : p / q = 1 := Real.log_injOn_pos
      (Set.mem_Ioi.mpr (div_pos hp hq))
      (Set.mem_Ioi.mpr (show (0 : ℝ) < 1 by exact zero_lt_one)) hlog
    exact (div_eq_one_iff_eq hq.ne').mp this
  · rintro rfl
    simp

end InfoGeometry.Physics.FiniteModularCentralizer
